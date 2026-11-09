// Lean compiler output
// Module: Lean.Elab.Tactic.AutoTry
// Imports: import Init.Try import Lean.Linter.Basic import Lean.Elab.InfoTree.Util import Lean.Elab.Tactic.Try import Lean.Elab.Tactic.Meta import Lean.Elab.BuiltinTerm
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
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
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
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
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lean_inheritedTraceOptions;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__28;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__29;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticSorry"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticAdmit"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_value;
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 55, 102, 232, 177, 170, 100, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 145, .m_capacity = 145, .m_length = 144, .m_data = "Tactic.unsolvedGoals message yielded no (msgCtx, namingCtx, goal) tuples; producer not following the `withContext`/`withNamingContext` contract\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "no tacticSeq body found for unsolved-goals message at "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "; unrecognised seq variant\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "try\?"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tryTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 128, 230, 128, 87, 180, 97, 21)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(lean_object* v_opts_238_, lean_object* v_opt_239_){
_start:
{
lean_object* v_name_240_; lean_object* v_defValue_241_; lean_object* v_map_242_; lean_object* v___x_243_; 
v_name_240_ = lean_ctor_get(v_opt_239_, 0);
v_defValue_241_ = lean_ctor_get(v_opt_239_, 1);
v_map_242_ = lean_ctor_get(v_opts_238_, 0);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_242_, v_name_240_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_inc(v_defValue_241_);
return v_defValue_241_;
}
else
{
lean_object* v_val_244_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v___x_243_, 1);
if (lean_obj_tag(v_val_244_) == 3)
{
lean_object* v_v_245_; 
v_v_245_ = lean_ctor_get(v_val_244_, 0);
lean_inc(v_v_245_);
lean_dec_ref_known(v_val_244_, 1);
return v_v_245_;
}
else
{
lean_dec(v_val_244_);
lean_inc(v_defValue_241_);
return v_defValue_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1___boxed(lean_object* v_opts_246_, lean_object* v_opt_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v_opts_246_, v_opt_247_);
lean_dec_ref(v_opt_247_);
lean_dec_ref(v_opts_246_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_249_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__1);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg();
return v_res_255_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1(void){
_start:
{
lean_object* v___x_262_; uint64_t v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0));
v___x_263_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2(void){
_start:
{
uint64_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1);
v___x_265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0));
v___x_266_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set_uint64(v___x_266_, sizeof(void*)*1, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4(void){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg();
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
lean_ctor_set(v___x_276_, 2, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_277_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7);
v___x_278_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6);
v___x_279_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_280_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_281_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_278_);
lean_ctor_set(v___x_281_, 3, v___x_279_);
lean_ctor_set(v___x_281_, 4, v___x_279_);
lean_ctor_set(v___x_281_, 5, v___x_279_);
lean_ctor_set(v___x_281_, 6, v___x_279_);
lean_ctor_set(v___x_281_, 7, v___x_277_);
return v___x_281_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_unsigned_to_nat(32u);
v___x_283_ = lean_mk_empty_array_with_capacity(v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10(void){
_start:
{
size_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_285_ = ((size_t)5ULL);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_unsigned_to_nat(32u);
v___x_288_ = lean_mk_empty_array_with_capacity(v___x_287_);
v___x_289_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9);
v___x_290_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
lean_ctor_set(v___x_290_, 2, v___x_286_);
lean_ctor_set(v___x_290_, 3, v___x_286_);
lean_ctor_set_usize(v___x_290_, 4, v___x_285_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_ctor_set(v___x_292_, 2, v___x_291_);
lean_ctor_set(v___x_292_, 3, v___x_291_);
lean_ctor_set(v___x_292_, 4, v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = l_Lean_Options_empty;
v___x_294_ = l_Lean_Core_getMaxHeartbeats(v___x_293_);
return v___x_294_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13(void){
_start:
{
lean_object* v___x_295_; uint16_t v___x_296_; 
v___x_295_ = l_Lean_Options_empty;
v___x_296_ = l_Lean_OptionFlags_ofOptions(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = l_Lean_firstFrontendMacroScope;
v___x_299_ = lean_nat_add(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19(void){
_start:
{
lean_object* v___x_310_; uint64_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_311_ = 0ULL;
v___x_312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set_uint64(v___x_312_, sizeof(void*)*1, v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = l_Lean_Options_empty;
v___x_317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_318_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
lean_ctor_set(v___x_318_, 3, v___x_315_);
lean_ctor_set(v___x_318_, 4, v___x_315_);
lean_ctor_set(v___x_318_, 5, v___x_315_);
lean_ctor_set(v___x_318_, 6, v___x_317_);
lean_ctor_set(v___x_318_, 7, v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = l_Lean_NameSet_empty;
v___x_320_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_ctor_set(v___x_321_, 2, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; 
v___x_322_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_323_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_324_ = 1;
v___x_325_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
lean_ctor_set(v___x_325_, 2, v___x_322_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*3, v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = l_Lean_maxRecDepth;
v___x_330_ = l_Lean_Options_empty;
v___x_331_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__28(void){
_start:
{
uint16_t v___x_332_; uint16_t v___x_333_; uint16_t v___x_334_; 
v___x_332_ = 512;
v___x_333_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13);
v___x_334_ = lean_uint16_land(v___x_333_, v___x_332_);
return v___x_334_;
}
}
static uint8_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__29(void){
_start:
{
uint16_t v___x_335_; uint16_t v___x_336_; uint8_t v___x_337_; 
v___x_335_ = 0;
v___x_336_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__28, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__28_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__28);
v___x_337_ = lean_uint16_dec_eq(v___x_336_, v___x_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object* v_env_338_, lean_object* v_mctx_339_, lean_object* v_lctx_340_, lean_object* v_opts_341_, lean_object* v_namingCtx_342_, lean_object* v_x_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_fileName_359_; lean_object* v_fileMap_360_; lean_object* v_ref_361_; lean_object* v_cancelTk_x3f_362_; lean_object* v_a_364_; lean_object* v_a_371_; lean_object* v_currNamespace_373_; lean_object* v_openDecls_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint16_t v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___y_395_; uint16_t v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_498_; lean_object* v___y_499_; uint16_t v___y_500_; lean_object* v___y_501_; uint8_t v___y_502_; lean_object* v___y_503_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v_fileName_538_; lean_object* v_fileMap_539_; lean_object* v_currNamespace_540_; lean_object* v_openDecls_541_; lean_object* v_initHeartbeats_542_; lean_object* v_maxHeartbeats_543_; lean_object* v_quotContext_544_; lean_object* v_currMacroScope_545_; lean_object* v_cancelTk_x3f_546_; lean_object* v_inheritedTraceOptions_547_; lean_object* v_currRecDepth_548_; lean_object* v_ref_549_; uint8_t v_suppressElabErrors_550_; uint8_t v_checkDeprecated_551_; uint8_t v_isRecordingDeps_552_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___y_561_; lean_object* v_env_582_; uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_347_ = lean_box(1);
v___x_348_ = 0;
v___x_349_ = l_Lean_Environment_setExporting(v_env_338_, v___x_348_);
v___x_350_ = 1;
v___x_351_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_354_ = lean_box(0);
v___x_355_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_355_, 0, v___x_351_);
lean_ctor_set(v___x_355_, 1, v___x_347_);
lean_ctor_set(v___x_355_, 2, v_lctx_340_);
lean_ctor_set(v___x_355_, 3, v___x_353_);
lean_ctor_set(v___x_355_, 4, v___x_354_);
lean_ctor_set(v___x_355_, 5, v___x_352_);
lean_ctor_set(v___x_355_, 6, v___x_354_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*7, v___x_348_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*7 + 1, v___x_348_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*7 + 2, v___x_348_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*7 + 3, v___x_350_);
v___x_356_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_357_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_358_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v_fileName_359_ = lean_ctor_get(v_a_344_, 0);
v_fileMap_360_ = lean_ctor_get(v_a_344_, 1);
v_ref_361_ = lean_ctor_get(v_a_344_, 7);
v_cancelTk_x3f_362_ = lean_ctor_get(v_a_344_, 9);
v_currNamespace_373_ = lean_ctor_get(v_namingCtx_342_, 0);
lean_inc(v_currNamespace_373_);
v_openDecls_374_ = lean_ctor_get(v_namingCtx_342_, 1);
lean_inc(v_openDecls_374_);
lean_dec_ref(v_namingCtx_342_);
v___x_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_375_, 0, v_mctx_339_);
lean_ctor_set(v___x_375_, 1, v___x_356_);
lean_ctor_set(v___x_375_, 2, v___x_347_);
lean_ctor_set(v___x_375_, 3, v___x_357_);
lean_ctor_set(v___x_375_, 4, v___x_358_);
v___x_376_ = l_Lean_Options_empty;
v___x_377_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12);
v___x_378_ = lean_box(0);
v___x_379_ = l_Lean_firstFrontendMacroScope;
v___x_380_ = lean_box(0);
v___x_381_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__13);
v___x_382_ = 0;
v___x_383_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__14);
v___x_384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17));
v___x_385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18));
v___x_386_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
v___x_387_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20);
v___x_388_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21);
v___x_389_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22);
v___x_390_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23);
v___x_391_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_391_, 0, v___x_349_);
lean_ctor_set(v___x_391_, 1, v___x_383_);
lean_ctor_set(v___x_391_, 2, v___x_384_);
lean_ctor_set(v___x_391_, 3, v___x_385_);
lean_ctor_set(v___x_391_, 4, v___x_386_);
lean_ctor_set(v___x_391_, 5, v___x_387_);
lean_ctor_set(v___x_391_, 6, v___x_388_);
lean_ctor_set(v___x_391_, 7, v___x_389_);
lean_ctor_set(v___x_391_, 8, v___x_390_);
lean_ctor_set(v___x_391_, 9, v___x_353_);
v___x_392_ = lean_io_get_num_heartbeats();
v___x_393_ = lean_st_mk_ref(v___x_391_);
v___x_557_ = l_Lean_inheritedTraceOptions;
v___x_558_ = lean_st_ref_get(v___x_557_);
v___x_559_ = lean_st_ref_get(v___x_393_);
v_env_582_ = lean_ctor_get(v___x_559_, 0);
lean_inc_ref(v_env_582_);
lean_dec(v___x_559_);
v___x_583_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_582_);
lean_dec_ref(v_env_582_);
v___x_584_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__29, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__29_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__29);
if (v___x_584_ == 0)
{
if (v___x_583_ == 0)
{
v___y_561_ = v___x_350_;
goto v___jp_560_;
}
else
{
v_fileName_538_ = v_fileName_359_;
v_fileMap_539_ = v_fileMap_360_;
v_currNamespace_540_ = v_currNamespace_373_;
v_openDecls_541_ = v_openDecls_374_;
v_initHeartbeats_542_ = v___x_392_;
v_maxHeartbeats_543_ = v___x_377_;
v_quotContext_544_ = v___x_378_;
v_currMacroScope_545_ = v___x_379_;
v_cancelTk_x3f_546_ = v_cancelTk_x3f_362_;
v_inheritedTraceOptions_547_ = v___x_558_;
v_currRecDepth_548_ = v___x_352_;
v_ref_549_ = v___x_380_;
v_suppressElabErrors_550_ = v___x_348_;
v_checkDeprecated_551_ = v___x_382_;
v_isRecordingDeps_552_ = v___x_348_;
goto v___jp_537_;
}
}
else
{
if (v___x_583_ == 0)
{
v_fileName_538_ = v_fileName_359_;
v_fileMap_539_ = v_fileMap_360_;
v_currNamespace_540_ = v_currNamespace_373_;
v_openDecls_541_ = v_openDecls_374_;
v_initHeartbeats_542_ = v___x_392_;
v_maxHeartbeats_543_ = v___x_377_;
v_quotContext_544_ = v___x_378_;
v_currMacroScope_545_ = v___x_379_;
v_cancelTk_x3f_546_ = v_cancelTk_x3f_362_;
v_inheritedTraceOptions_547_ = v___x_558_;
v_currRecDepth_548_ = v___x_352_;
v_ref_549_ = v___x_380_;
v_suppressElabErrors_550_ = v___x_348_;
v_checkDeprecated_551_ = v___x_382_;
v_isRecordingDeps_552_ = v___x_348_;
goto v___jp_537_;
}
else
{
v___y_561_ = v___x_348_;
goto v___jp_560_;
}
}
v___jp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_365_ = lean_io_error_to_string(v_a_364_);
v___x_366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
v___x_367_ = l_Lean_MessageData_ofFormat(v___x_366_);
lean_inc(v_ref_361_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v_ref_361_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
v___jp_370_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_mk_io_user_error(v_a_371_);
v_a_364_ = v___x_372_;
goto v___jp_363_;
}
v___jp_394_:
{
lean_object* v_toCold_400_; lean_object* v_currRecDepth_401_; lean_object* v_ref_402_; uint8_t v_suppressElabErrors_403_; uint8_t v_checkDeprecated_404_; uint8_t v_isRecordingDeps_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_496_; 
v_toCold_400_ = lean_ctor_get(v___y_398_, 0);
v_currRecDepth_401_ = lean_ctor_get(v___y_398_, 1);
v_ref_402_ = lean_ctor_get(v___y_398_, 2);
v_suppressElabErrors_403_ = lean_ctor_get_uint8(v___y_398_, sizeof(void*)*3 + 2);
v_checkDeprecated_404_ = lean_ctor_get_uint8(v___y_398_, sizeof(void*)*3 + 3);
v_isRecordingDeps_405_ = lean_ctor_get_uint8(v___y_398_, sizeof(void*)*3 + 4);
v_isSharedCheck_496_ = !lean_is_exclusive(v___y_398_);
if (v_isSharedCheck_496_ == 0)
{
v___x_407_ = v___y_398_;
v_isShared_408_ = v_isSharedCheck_496_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_ref_402_);
lean_inc(v_currRecDepth_401_);
lean_inc(v_toCold_400_);
lean_dec(v___y_398_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_496_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_fileName_409_; lean_object* v_fileMap_410_; lean_object* v_currNamespace_411_; lean_object* v_openDecls_412_; lean_object* v_initHeartbeats_413_; lean_object* v_maxHeartbeats_414_; lean_object* v_quotContext_415_; lean_object* v_currMacroScope_416_; lean_object* v_cancelTk_x3f_417_; lean_object* v_inheritedTraceOptions_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_493_; 
v_fileName_409_ = lean_ctor_get(v_toCold_400_, 0);
v_fileMap_410_ = lean_ctor_get(v_toCold_400_, 1);
v_currNamespace_411_ = lean_ctor_get(v_toCold_400_, 4);
v_openDecls_412_ = lean_ctor_get(v_toCold_400_, 5);
v_initHeartbeats_413_ = lean_ctor_get(v_toCold_400_, 6);
v_maxHeartbeats_414_ = lean_ctor_get(v_toCold_400_, 7);
v_quotContext_415_ = lean_ctor_get(v_toCold_400_, 8);
v_currMacroScope_416_ = lean_ctor_get(v_toCold_400_, 9);
v_cancelTk_x3f_417_ = lean_ctor_get(v_toCold_400_, 10);
v_inheritedTraceOptions_418_ = lean_ctor_get(v_toCold_400_, 11);
v_isSharedCheck_493_ = !lean_is_exclusive(v_toCold_400_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_494_ = lean_ctor_get(v_toCold_400_, 3);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_toCold_400_, 2);
lean_dec(v_unused_495_);
v___x_420_ = v_toCold_400_;
v_isShared_421_ = v_isSharedCheck_493_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_inheritedTraceOptions_418_);
lean_inc(v_cancelTk_x3f_417_);
lean_inc(v_currMacroScope_416_);
lean_inc(v_quotContext_415_);
lean_inc(v_maxHeartbeats_414_);
lean_inc(v_initHeartbeats_413_);
lean_inc(v_openDecls_412_);
lean_inc(v_currNamespace_411_);
lean_inc(v_fileMap_410_);
lean_inc(v_fileName_409_);
lean_dec(v_toCold_400_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_493_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v___y_395_, v___y_397_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 3, v___x_422_);
lean_ctor_set(v___x_420_, 2, v___y_395_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_fileName_409_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_fileMap_410_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v___y_395_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_currNamespace_411_);
lean_ctor_set(v_reuseFailAlloc_492_, 5, v_openDecls_412_);
lean_ctor_set(v_reuseFailAlloc_492_, 6, v_initHeartbeats_413_);
lean_ctor_set(v_reuseFailAlloc_492_, 7, v_maxHeartbeats_414_);
lean_ctor_set(v_reuseFailAlloc_492_, 8, v_quotContext_415_);
lean_ctor_set(v_reuseFailAlloc_492_, 9, v_currMacroScope_416_);
lean_ctor_set(v_reuseFailAlloc_492_, 10, v_cancelTk_x3f_417_);
lean_ctor_set(v_reuseFailAlloc_492_, 11, v_inheritedTraceOptions_418_);
v___x_424_ = v_reuseFailAlloc_492_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_426_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_424_);
v___x_426_ = v___x_407_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_currRecDepth_401_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_ref_402_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*3 + 2, v_suppressElabErrors_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*3 + 3, v_checkDeprecated_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*3 + 4, v_isRecordingDeps_405_);
v___x_426_ = v_reuseFailAlloc_491_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_ctor_set_uint16(v___x_426_, sizeof(void*)*3, v___y_396_);
v___x_427_ = lean_st_mk_ref(v___x_375_);
lean_inc(v___x_427_);
v___x_428_ = lean_apply_5(v_x_343_, v___x_355_, v___x_427_, v___x_426_, v___y_399_, lean_box(0));
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_475_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_475_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_475_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_475_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v_traceState_436_; lean_object* v_traceState_437_; lean_object* v_env_438_; lean_object* v_messages_439_; lean_object* v_scopes_440_; lean_object* v_usedQuotCtxts_441_; lean_object* v_nextMacroScope_442_; lean_object* v_maxRecDepth_443_; lean_object* v_ngen_444_; lean_object* v_auxDeclNGen_445_; lean_object* v_infoState_446_; lean_object* v_snapshotTasks_447_; lean_object* v_prevLinterStates_448_; lean_object* v_codeQualityEntryTasks_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_473_; 
v___x_433_ = lean_st_ref_get(v___x_427_);
lean_dec(v___x_427_);
lean_dec(v___x_433_);
v___x_434_ = lean_st_ref_get(v___x_393_);
lean_dec(v___x_393_);
v___x_435_ = lean_st_ref_take(v_a_345_);
v_traceState_436_ = lean_ctor_get(v___x_435_, 9);
lean_inc_ref(v_traceState_436_);
v_traceState_437_ = lean_ctor_get(v___x_434_, 4);
lean_inc_ref(v_traceState_437_);
v_env_438_ = lean_ctor_get(v___x_435_, 0);
v_messages_439_ = lean_ctor_get(v___x_435_, 1);
v_scopes_440_ = lean_ctor_get(v___x_435_, 2);
v_usedQuotCtxts_441_ = lean_ctor_get(v___x_435_, 3);
v_nextMacroScope_442_ = lean_ctor_get(v___x_435_, 4);
v_maxRecDepth_443_ = lean_ctor_get(v___x_435_, 5);
v_ngen_444_ = lean_ctor_get(v___x_435_, 6);
v_auxDeclNGen_445_ = lean_ctor_get(v___x_435_, 7);
v_infoState_446_ = lean_ctor_get(v___x_435_, 8);
v_snapshotTasks_447_ = lean_ctor_get(v___x_435_, 10);
v_prevLinterStates_448_ = lean_ctor_get(v___x_435_, 11);
v_codeQualityEntryTasks_449_ = lean_ctor_get(v___x_435_, 12);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v___x_435_, 9);
lean_dec(v_unused_474_);
v___x_451_ = v___x_435_;
v_isShared_452_ = v_isSharedCheck_473_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_codeQualityEntryTasks_449_);
lean_inc(v_prevLinterStates_448_);
lean_inc(v_snapshotTasks_447_);
lean_inc(v_infoState_446_);
lean_inc(v_auxDeclNGen_445_);
lean_inc(v_ngen_444_);
lean_inc(v_maxRecDepth_443_);
lean_inc(v_nextMacroScope_442_);
lean_inc(v_usedQuotCtxts_441_);
lean_inc(v_scopes_440_);
lean_inc(v_messages_439_);
lean_inc(v_env_438_);
lean_dec(v___x_435_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_473_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v_messages_453_; uint64_t v_tid_454_; lean_object* v_traces_455_; lean_object* v_traces_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_472_; 
v_messages_453_ = lean_ctor_get(v___x_434_, 7);
lean_inc_ref(v_messages_453_);
lean_dec(v___x_434_);
v_tid_454_ = lean_ctor_get_uint64(v_traceState_436_, sizeof(void*)*1);
v_traces_455_ = lean_ctor_get(v_traceState_436_, 0);
lean_inc_ref(v_traces_455_);
lean_dec_ref(v_traceState_436_);
v_traces_456_ = lean_ctor_get(v_traceState_437_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_traceState_437_);
if (v_isSharedCheck_472_ == 0)
{
v___x_458_ = v_traceState_437_;
v_isShared_459_ = v_isSharedCheck_472_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_traces_456_);
lean_dec(v_traceState_437_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_472_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_460_ = l_Lean_MessageLog_append(v_messages_439_, v_messages_453_);
v___x_461_ = l_Lean_PersistentArray_append___redArg(v_traces_455_, v_traces_456_);
lean_dec_ref(v_traces_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_461_);
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_471_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
lean_ctor_set_uint64(v___x_463_, sizeof(void*)*1, v_tid_454_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 9, v___x_463_);
lean_ctor_set(v___x_451_, 1, v___x_460_);
v___x_465_ = v___x_451_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_env_438_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_scopes_440_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_usedQuotCtxts_441_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_nextMacroScope_442_);
lean_ctor_set(v_reuseFailAlloc_470_, 5, v_maxRecDepth_443_);
lean_ctor_set(v_reuseFailAlloc_470_, 6, v_ngen_444_);
lean_ctor_set(v_reuseFailAlloc_470_, 7, v_auxDeclNGen_445_);
lean_ctor_set(v_reuseFailAlloc_470_, 8, v_infoState_446_);
lean_ctor_set(v_reuseFailAlloc_470_, 9, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_470_, 10, v_snapshotTasks_447_);
lean_ctor_set(v_reuseFailAlloc_470_, 11, v_prevLinterStates_448_);
lean_ctor_set(v_reuseFailAlloc_470_, 12, v_codeQualityEntryTasks_449_);
v___x_465_ = v_reuseFailAlloc_470_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = lean_st_ref_put(v_a_345_, v___x_465_);
if (v_isShared_432_ == 0)
{
v___x_468_ = v___x_431_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_429_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_476_; 
lean_dec(v___x_427_);
lean_dec(v___x_393_);
v_a_476_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_428_, 1);
if (lean_obj_tag(v_a_476_) == 0)
{
lean_object* v_msg_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_msg_477_ = lean_ctor_get(v_a_476_, 1);
lean_inc_ref(v_msg_477_);
lean_dec_ref_known(v_a_476_, 2);
v___x_478_ = l_Lean_MessageData_toString(v_msg_477_);
v___x_479_ = lean_mk_io_user_error(v___x_478_);
v_a_364_ = v___x_479_;
goto v___jp_363_;
}
else
{
lean_object* v_id_480_; lean_object* v___x_481_; 
v_id_480_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_id_480_);
lean_dec_ref_known(v_a_476_, 2);
v___x_481_ = l_Lean_InternalExceptionId_getName(v_id_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec(v_id_480_);
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 1);
v___x_483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24));
v___x_484_ = l_Lean_Name_toString(v_a_482_, v___x_350_);
v___x_485_ = lean_string_append(v___x_483_, v___x_484_);
lean_dec_ref(v___x_484_);
v_a_371_ = v___x_485_;
goto v___jp_370_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec_ref_known(v___x_481_, 1);
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25));
v___x_487_ = l_Nat_reprFast(v_id_480_);
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
lean_dec_ref(v___x_487_);
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26));
v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
v_a_371_ = v___x_490_;
goto v___jp_370_;
}
}
}
}
}
}
}
}
v___jp_497_:
{
lean_object* v___x_504_; lean_object* v_env_505_; lean_object* v_nextMacroScope_506_; lean_object* v_ngen_507_; lean_object* v_auxDeclNGen_508_; lean_object* v_traceState_509_; lean_object* v_recordedDeps_510_; lean_object* v_messages_511_; lean_object* v_infoState_512_; lean_object* v_snapshotTasks_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_522_; 
v___x_504_ = lean_st_ref_take(v___y_503_);
v_env_505_ = lean_ctor_get(v___x_504_, 0);
v_nextMacroScope_506_ = lean_ctor_get(v___x_504_, 1);
v_ngen_507_ = lean_ctor_get(v___x_504_, 2);
v_auxDeclNGen_508_ = lean_ctor_get(v___x_504_, 3);
v_traceState_509_ = lean_ctor_get(v___x_504_, 4);
v_recordedDeps_510_ = lean_ctor_get(v___x_504_, 6);
v_messages_511_ = lean_ctor_get(v___x_504_, 7);
v_infoState_512_ = lean_ctor_get(v___x_504_, 8);
v_snapshotTasks_513_ = lean_ctor_get(v___x_504_, 9);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v___x_504_, 5);
lean_dec(v_unused_523_);
v___x_515_ = v___x_504_;
v_isShared_516_ = v_isSharedCheck_522_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_snapshotTasks_513_);
lean_inc(v_infoState_512_);
lean_inc(v_messages_511_);
lean_inc(v_recordedDeps_510_);
lean_inc(v_traceState_509_);
lean_inc(v_auxDeclNGen_508_);
lean_inc(v_ngen_507_);
lean_inc(v_nextMacroScope_506_);
lean_inc(v_env_505_);
lean_dec(v___x_504_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_522_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = l_Lean_Kernel_enableDiag(v_env_505_, v___y_502_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 5, v___x_387_);
lean_ctor_set(v___x_515_, 0, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_nextMacroScope_506_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_ngen_507_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_auxDeclNGen_508_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v_traceState_509_);
lean_ctor_set(v_reuseFailAlloc_521_, 5, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_521_, 6, v_recordedDeps_510_);
lean_ctor_set(v_reuseFailAlloc_521_, 7, v_messages_511_);
lean_ctor_set(v_reuseFailAlloc_521_, 8, v_infoState_512_);
lean_ctor_set(v_reuseFailAlloc_521_, 9, v_snapshotTasks_513_);
v___x_519_ = v_reuseFailAlloc_521_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; 
v___x_520_ = lean_st_ref_put(v___y_503_, v___x_519_);
v___y_395_ = v___y_498_;
v___y_396_ = v___y_500_;
v___y_397_ = v___y_499_;
v___y_398_ = v___y_501_;
v___y_399_ = v___y_503_;
goto v___jp_394_;
}
}
}
v___jp_524_:
{
uint16_t v___x_529_; lean_object* v___x_530_; lean_object* v_env_531_; uint8_t v___x_532_; uint16_t v___x_533_; uint16_t v___x_534_; uint16_t v___x_535_; uint8_t v___x_536_; 
v___x_529_ = l_Lean_OptionFlags_ofOptions(v___y_528_);
v___x_530_ = lean_st_ref_get(v___y_527_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_env_531_);
lean_dec(v___x_530_);
v___x_532_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_531_);
lean_dec_ref(v_env_531_);
v___x_533_ = 512;
v___x_534_ = lean_uint16_land(v___x_529_, v___x_533_);
v___x_535_ = 0;
v___x_536_ = lean_uint16_dec_eq(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
if (v___x_532_ == 0)
{
v___y_498_ = v___y_528_;
v___y_499_ = v___y_525_;
v___y_500_ = v___x_529_;
v___y_501_ = v___y_526_;
v___y_502_ = v___x_350_;
v___y_503_ = v___y_527_;
goto v___jp_497_;
}
else
{
v___y_395_ = v___y_528_;
v___y_396_ = v___x_529_;
v___y_397_ = v___y_525_;
v___y_398_ = v___y_526_;
v___y_399_ = v___y_527_;
goto v___jp_394_;
}
}
else
{
if (v___x_532_ == 0)
{
v___y_395_ = v___y_528_;
v___y_396_ = v___x_529_;
v___y_397_ = v___y_525_;
v___y_398_ = v___y_526_;
v___y_399_ = v___y_527_;
goto v___jp_394_;
}
else
{
v___y_498_ = v___y_528_;
v___y_499_ = v___y_525_;
v___y_500_ = v___x_529_;
v___y_501_ = v___y_526_;
v___y_502_ = v___x_348_;
v___y_503_ = v___y_527_;
goto v___jp_497_;
}
}
}
v___jp_537_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_553_ = l_Lean_maxRecDepth;
v___x_554_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27);
lean_inc(v_cancelTk_x3f_546_);
lean_inc(v_currMacroScope_545_);
lean_inc(v_quotContext_544_);
lean_inc(v_maxHeartbeats_543_);
lean_inc_ref(v_fileMap_539_);
lean_inc_ref(v_fileName_538_);
v___x_555_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_555_, 0, v_fileName_538_);
lean_ctor_set(v___x_555_, 1, v_fileMap_539_);
lean_ctor_set(v___x_555_, 2, v___x_376_);
lean_ctor_set(v___x_555_, 3, v___x_554_);
lean_ctor_set(v___x_555_, 4, v_currNamespace_540_);
lean_ctor_set(v___x_555_, 5, v_openDecls_541_);
lean_ctor_set(v___x_555_, 6, v_initHeartbeats_542_);
lean_ctor_set(v___x_555_, 7, v_maxHeartbeats_543_);
lean_ctor_set(v___x_555_, 8, v_quotContext_544_);
lean_ctor_set(v___x_555_, 9, v_currMacroScope_545_);
lean_ctor_set(v___x_555_, 10, v_cancelTk_x3f_546_);
lean_ctor_set(v___x_555_, 11, v_inheritedTraceOptions_547_);
lean_inc(v_ref_549_);
v___x_556_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v_currRecDepth_548_);
lean_ctor_set(v___x_556_, 2, v_ref_549_);
lean_ctor_set_uint16(v___x_556_, sizeof(void*)*3, v___x_381_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*3 + 2, v_suppressElabErrors_550_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*3 + 3, v_checkDeprecated_551_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*3 + 4, v_isRecordingDeps_552_);
lean_inc(v___x_393_);
v___y_525_ = v___x_553_;
v___y_526_ = v___x_556_;
v___y_527_ = v___x_393_;
v___y_528_ = v_opts_341_;
goto v___jp_524_;
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v_env_563_; lean_object* v_nextMacroScope_564_; lean_object* v_ngen_565_; lean_object* v_auxDeclNGen_566_; lean_object* v_traceState_567_; lean_object* v_recordedDeps_568_; lean_object* v_messages_569_; lean_object* v_infoState_570_; lean_object* v_snapshotTasks_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_580_; 
v___x_562_ = lean_st_ref_take(v___x_393_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
v_nextMacroScope_564_ = lean_ctor_get(v___x_562_, 1);
v_ngen_565_ = lean_ctor_get(v___x_562_, 2);
v_auxDeclNGen_566_ = lean_ctor_get(v___x_562_, 3);
v_traceState_567_ = lean_ctor_get(v___x_562_, 4);
v_recordedDeps_568_ = lean_ctor_get(v___x_562_, 6);
v_messages_569_ = lean_ctor_get(v___x_562_, 7);
v_infoState_570_ = lean_ctor_get(v___x_562_, 8);
v_snapshotTasks_571_ = lean_ctor_get(v___x_562_, 9);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v___x_562_, 5);
lean_dec(v_unused_581_);
v___x_573_ = v___x_562_;
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snapshotTasks_571_);
lean_inc(v_infoState_570_);
lean_inc(v_messages_569_);
lean_inc(v_recordedDeps_568_);
lean_inc(v_traceState_567_);
lean_inc(v_auxDeclNGen_566_);
lean_inc(v_ngen_565_);
lean_inc(v_nextMacroScope_564_);
lean_inc(v_env_563_);
lean_dec(v___x_562_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_Kernel_enableDiag(v_env_563_, v___y_561_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 5, v___x_387_);
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_nextMacroScope_564_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_ngen_565_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v_auxDeclNGen_566_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v_traceState_567_);
lean_ctor_set(v_reuseFailAlloc_579_, 5, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_579_, 6, v_recordedDeps_568_);
lean_ctor_set(v_reuseFailAlloc_579_, 7, v_messages_569_);
lean_ctor_set(v_reuseFailAlloc_579_, 8, v_infoState_570_);
lean_ctor_set(v_reuseFailAlloc_579_, 9, v_snapshotTasks_571_);
v___x_577_ = v_reuseFailAlloc_579_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; 
v___x_578_ = lean_st_ref_put(v___x_393_, v___x_577_);
v_fileName_538_ = v_fileName_359_;
v_fileMap_539_ = v_fileMap_360_;
v_currNamespace_540_ = v_currNamespace_373_;
v_openDecls_541_ = v_openDecls_374_;
v_initHeartbeats_542_ = v___x_392_;
v_maxHeartbeats_543_ = v___x_377_;
v_quotContext_544_ = v___x_378_;
v_currMacroScope_545_ = v___x_379_;
v_cancelTk_x3f_546_ = v_cancelTk_x3f_362_;
v_inheritedTraceOptions_547_ = v___x_558_;
v_currRecDepth_548_ = v___x_352_;
v_ref_549_ = v___x_380_;
v_suppressElabErrors_550_ = v___x_348_;
v_checkDeprecated_551_ = v___x_382_;
v_isRecordingDeps_552_ = v___x_348_;
goto v___jp_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_585_, lean_object* v_mctx_586_, lean_object* v_lctx_587_, lean_object* v_opts_588_, lean_object* v_namingCtx_589_, lean_object* v_x_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_585_, v_mctx_586_, v_lctx_587_, v_opts_588_, v_namingCtx_589_, v_x_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_595_, lean_object* v_env_596_, lean_object* v_mctx_597_, lean_object* v_lctx_598_, lean_object* v_opts_599_, lean_object* v_namingCtx_600_, lean_object* v_x_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_596_, v_mctx_597_, v_lctx_598_, v_opts_599_, v_namingCtx_600_, v_x_601_, v_a_602_, v_a_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_606_, lean_object* v_env_607_, lean_object* v_mctx_608_, lean_object* v_lctx_609_, lean_object* v_opts_610_, lean_object* v_namingCtx_611_, lean_object* v_x_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_606_, v_env_607_, v_mctx_608_, v_lctx_609_, v_opts_610_, v_namingCtx_611_, v_x_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0(lean_object* v_00_u03b2_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___redArg(){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___redArg___boxed(lean_object* v___dummy_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___redArg();
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object* v_00_u03b2_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
return v___x_624_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Syntax_getKind(v_stx_628_);
if (lean_obj_tag(v___x_629_) == 1)
{
lean_object* v_pre_630_; 
v_pre_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_pre_630_);
if (lean_obj_tag(v_pre_630_) == 1)
{
lean_object* v_pre_631_; 
v_pre_631_ = lean_ctor_get(v_pre_630_, 0);
lean_inc(v_pre_631_);
if (lean_obj_tag(v_pre_631_) == 1)
{
lean_object* v_pre_632_; 
v_pre_632_ = lean_ctor_get(v_pre_631_, 0);
lean_inc(v_pre_632_);
if (lean_obj_tag(v_pre_632_) == 1)
{
lean_object* v_pre_633_; 
v_pre_633_ = lean_ctor_get(v_pre_632_, 0);
if (lean_obj_tag(v_pre_633_) == 0)
{
lean_object* v_str_634_; lean_object* v_str_635_; lean_object* v_str_636_; lean_object* v_str_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_str_634_ = lean_ctor_get(v___x_629_, 1);
lean_inc_ref(v_str_634_);
lean_dec_ref_known(v___x_629_, 2);
v_str_635_ = lean_ctor_get(v_pre_630_, 1);
lean_inc_ref(v_str_635_);
lean_dec_ref_known(v_pre_630_, 2);
v_str_636_ = lean_ctor_get(v_pre_631_, 1);
lean_inc_ref(v_str_636_);
lean_dec_ref_known(v_pre_631_, 2);
v_str_637_ = lean_ctor_get(v_pre_632_, 1);
lean_inc_ref(v_str_637_);
lean_dec_ref_known(v_pre_632_, 2);
v___x_638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_639_ = lean_string_dec_eq(v_str_637_, v___x_638_);
lean_dec_ref(v_str_637_);
if (v___x_639_ == 0)
{
lean_dec_ref(v_str_636_);
lean_dec_ref(v_str_635_);
lean_dec_ref(v_str_634_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_641_ = lean_string_dec_eq(v_str_636_, v___x_640_);
lean_dec_ref(v_str_636_);
if (v___x_641_ == 0)
{
lean_dec_ref(v_str_635_);
lean_dec_ref(v_str_634_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_643_ = lean_string_dec_eq(v_str_635_, v___x_642_);
lean_dec_ref(v_str_635_);
if (v___x_643_ == 0)
{
lean_dec_ref(v_str_634_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_645_ = lean_string_dec_eq(v_str_634_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_647_ = lean_string_dec_eq(v_str_634_, v___x_646_);
lean_dec_ref(v_str_634_);
return v___x_647_;
}
else
{
lean_dec_ref(v_str_634_);
return v___x_645_;
}
}
}
}
}
else
{
uint8_t v___x_648_; 
lean_dec_ref_known(v_pre_632_, 2);
lean_dec_ref_known(v_pre_631_, 2);
lean_dec_ref_known(v_pre_630_, 2);
lean_dec_ref_known(v___x_629_, 2);
v___x_648_ = 0;
return v___x_648_;
}
}
else
{
uint8_t v___x_649_; 
lean_dec(v_pre_632_);
lean_dec_ref_known(v_pre_631_, 2);
lean_dec_ref_known(v_pre_630_, 2);
lean_dec_ref_known(v___x_629_, 2);
v___x_649_ = 0;
return v___x_649_;
}
}
else
{
uint8_t v___x_650_; 
lean_dec_ref_known(v_pre_630_, 2);
lean_dec(v_pre_631_);
lean_dec_ref_known(v___x_629_, 2);
v___x_650_ = 0;
return v___x_650_;
}
}
else
{
uint8_t v___x_651_; 
lean_dec_ref_known(v___x_629_, 2);
lean_dec(v_pre_630_);
v___x_651_ = 0;
return v___x_651_;
}
}
else
{
uint8_t v___x_652_; 
lean_dec(v___x_629_);
v___x_652_ = 0;
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_653_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = lean_obj_tag_nat(v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl___boxed(lean_object* v_x_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(v_x_658_);
lean_dec(v_x_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_660_, lean_object* v_k_661_){
_start:
{
if (lean_obj_tag(v_t_660_) == 0)
{
lean_object* v_tacticSeq_662_; lean_object* v_insertPos_663_; lean_object* v___x_664_; 
v_tacticSeq_662_ = lean_ctor_get(v_t_660_, 0);
lean_inc(v_tacticSeq_662_);
v_insertPos_663_ = lean_ctor_get(v_t_660_, 1);
lean_inc(v_insertPos_663_);
lean_dec_ref_known(v_t_660_, 2);
v___x_664_ = lean_apply_2(v_k_661_, v_tacticSeq_662_, v_insertPos_663_);
return v___x_664_;
}
else
{
return v_k_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_665_, lean_object* v_ctorIdx_666_, lean_object* v_t_667_, lean_object* v_h_668_, lean_object* v_k_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_667_, v_k_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_671_, lean_object* v_ctorIdx_672_, lean_object* v_t_673_, lean_object* v_h_674_, lean_object* v_k_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_671_, v_ctorIdx_672_, v_t_673_, v_h_674_, v_k_675_);
lean_dec(v_ctorIdx_672_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_677_, lean_object* v_unsolvedGoal_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_677_, v_unsolvedGoal_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_680_, lean_object* v_t_681_, lean_object* v_h_682_, lean_object* v_unsolvedGoal_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_681_, v_unsolvedGoal_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_685_, lean_object* v_sorryTactic_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_685_, v_sorryTactic_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_688_, lean_object* v_t_689_, lean_object* v_h_690_, lean_object* v_sorryTactic_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_689_, v_sorryTactic_691_);
return v___x_692_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_696_; lean_object* v___x_697_; 
v___x_696_ = 32;
v___x_697_ = lean_box_uint32(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_698_, lean_object* v_fileMap_699_){
_start:
{
uint8_t v___x_700_; lean_object* v___x_701_; 
v___x_700_ = 0;
v___x_701_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_698_, v___x_700_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v_val_702_; lean_object* v___x_703_; 
v_val_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_698_, v___x_700_);
if (lean_obj_tag(v___x_703_) == 1)
{
lean_object* v_val_704_; lean_object* v_startPos_705_; lean_object* v_line_706_; lean_object* v_column_707_; lean_object* v_endPos_708_; lean_object* v_line_709_; uint8_t v___x_710_; 
v_val_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v___x_703_, 1);
lean_inc_ref(v_fileMap_699_);
v_startPos_705_ = l_Lean_FileMap_toPosition(v_fileMap_699_, v_val_702_);
lean_dec(v_val_702_);
v_line_706_ = lean_ctor_get(v_startPos_705_, 0);
lean_inc(v_line_706_);
v_column_707_ = lean_ctor_get(v_startPos_705_, 1);
lean_inc(v_column_707_);
lean_dec_ref(v_startPos_705_);
v_endPos_708_ = l_Lean_FileMap_toPosition(v_fileMap_699_, v_val_704_);
lean_dec(v_val_704_);
v_line_709_ = lean_ctor_get(v_endPos_708_, 0);
lean_inc(v_line_709_);
lean_dec_ref(v_endPos_708_);
v___x_710_ = lean_nat_dec_eq(v_line_706_, v_line_709_);
lean_dec(v_line_709_);
lean_dec(v_line_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_712_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_713_ = l_List_replicateTR___redArg(v_column_707_, v___x_712_);
v___x_714_ = lean_string_mk(v___x_713_);
v___x_715_ = lean_string_append(v___x_711_, v___x_714_);
lean_dec_ref(v___x_714_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; 
lean_dec(v_column_707_);
v___x_716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_716_;
}
}
else
{
lean_object* v___x_717_; 
lean_dec(v___x_703_);
lean_dec(v_val_702_);
lean_dec_ref(v_fileMap_699_);
v___x_717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_717_;
}
}
else
{
lean_object* v___x_718_; 
lean_dec(v___x_701_);
lean_dec_ref(v_fileMap_699_);
v___x_718_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_719_, lean_object* v_fileMap_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_719_, v_fileMap_720_);
lean_dec(v_tacticSeq_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_728_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
lean_inc(v_p_726_);
v___x_729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_p_726_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
lean_ctor_set(v___x_729_, 3, v_p_726_);
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_727_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_start_734_; lean_object* v_stop_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
v_start_734_ = lean_ctor_get(v_range_731_, 0);
v_stop_735_ = lean_ctor_get(v_range_731_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_range_731_);
if (v_isSharedCheck_743_ == 0)
{
v___x_737_ = v_range_731_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_stop_735_);
lean_inc(v_start_734_);
lean_dec(v_range_731_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_739_, 0, v___x_733_);
lean_ctor_set(v___x_739_, 1, v_start_734_);
lean_ctor_set(v___x_739_, 2, v___x_733_);
lean_ctor_set(v___x_739_, 3, v_stop_735_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 2);
lean_ctor_set(v___x_737_, 1, v___x_732_);
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_732_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_744_, lean_object* v_nc_x3f_745_, lean_object* v_msg_746_, lean_object* v_acc_747_){
_start:
{
switch(lean_obj_tag(v_msg_746_))
{
case 3:
{
lean_object* v_a_748_; lean_object* v_a_749_; lean_object* v___x_750_; 
lean_dec(v_mc_x3f_744_);
v_a_748_ = lean_ctor_get(v_msg_746_, 0);
v_a_749_ = lean_ctor_get(v_msg_746_, 1);
lean_inc_ref(v_a_748_);
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v_a_748_);
v_mc_x3f_744_ = v___x_750_;
v_msg_746_ = v_a_749_;
goto _start;
}
case 4:
{
lean_object* v_a_752_; lean_object* v_a_753_; lean_object* v___x_754_; 
lean_dec(v_nc_x3f_745_);
v_a_752_ = lean_ctor_get(v_msg_746_, 0);
v_a_753_ = lean_ctor_get(v_msg_746_, 1);
lean_inc_ref(v_a_752_);
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v_a_752_);
v_nc_x3f_745_ = v___x_754_;
v_msg_746_ = v_a_753_;
goto _start;
}
case 5:
{
lean_object* v_a_756_; 
v_a_756_ = lean_ctor_get(v_msg_746_, 1);
v_msg_746_ = v_a_756_;
goto _start;
}
case 6:
{
lean_object* v_a_758_; 
v_a_758_ = lean_ctor_get(v_msg_746_, 0);
v_msg_746_ = v_a_758_;
goto _start;
}
case 8:
{
lean_object* v_a_760_; 
v_a_760_ = lean_ctor_get(v_msg_746_, 1);
v_msg_746_ = v_a_760_;
goto _start;
}
case 7:
{
lean_object* v_a_762_; lean_object* v_a_763_; lean_object* v___x_764_; 
v_a_762_ = lean_ctor_get(v_msg_746_, 0);
v_a_763_ = lean_ctor_get(v_msg_746_, 1);
lean_inc(v_nc_x3f_745_);
lean_inc(v_mc_x3f_744_);
v___x_764_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_744_, v_nc_x3f_745_, v_a_762_, v_acc_747_);
v_msg_746_ = v_a_763_;
v_acc_747_ = v___x_764_;
goto _start;
}
case 2:
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v_msg_746_, 1);
v_msg_746_ = v_a_766_;
goto _start;
}
case 9:
{
lean_object* v_msg_768_; lean_object* v_children_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_msg_768_ = lean_ctor_get(v_msg_746_, 1);
v_children_769_ = lean_ctor_get(v_msg_746_, 2);
lean_inc(v_nc_x3f_745_);
lean_inc(v_mc_x3f_744_);
v___x_770_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_744_, v_nc_x3f_745_, v_msg_768_, v_acc_747_);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_array_get_size(v_children_769_);
v___x_773_ = lean_nat_dec_lt(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec(v_nc_x3f_745_);
lean_dec(v_mc_x3f_744_);
return v___x_770_;
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)0ULL);
v___x_775_ = lean_usize_of_nat(v___x_772_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_744_, v_nc_x3f_745_, v_children_769_, v___x_774_, v___x_775_, v___x_770_);
return v___x_776_;
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_744_) == 1)
{
if (lean_obj_tag(v_nc_x3f_745_) == 1)
{
lean_object* v_a_777_; lean_object* v_val_778_; lean_object* v_val_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_777_ = lean_ctor_get(v_msg_746_, 0);
v_val_778_ = lean_ctor_get(v_mc_x3f_744_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_mc_x3f_744_, 1);
v_val_779_ = lean_ctor_get(v_nc_x3f_745_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v_nc_x3f_745_, 1);
lean_inc(v_a_777_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_val_779_);
lean_ctor_set(v___x_780_, 1, v_a_777_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_val_778_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_array_push(v_acc_747_, v___x_781_);
return v___x_782_;
}
else
{
lean_dec_ref_known(v_mc_x3f_744_, 1);
lean_dec(v_nc_x3f_745_);
return v_acc_747_;
}
}
else
{
lean_dec(v_nc_x3f_745_);
lean_dec(v_mc_x3f_744_);
return v_acc_747_;
}
}
default: 
{
lean_dec(v_nc_x3f_745_);
lean_dec(v_mc_x3f_744_);
return v_acc_747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_783_, lean_object* v_nc_x3f_784_, lean_object* v_as_785_, size_t v_i_786_, size_t v_stop_787_, lean_object* v_b_788_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = lean_usize_dec_eq(v_i_786_, v_stop_787_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; size_t v___x_792_; size_t v___x_793_; 
v___x_790_ = lean_array_uget_borrowed(v_as_785_, v_i_786_);
lean_inc(v_nc_x3f_784_);
lean_inc(v_mc_x3f_783_);
v___x_791_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_783_, v_nc_x3f_784_, v___x_790_, v_b_788_);
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_786_, v___x_792_);
v_i_786_ = v___x_793_;
v_b_788_ = v___x_791_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_784_);
lean_dec(v_mc_x3f_783_);
return v_b_788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_795_, lean_object* v_nc_x3f_796_, lean_object* v_as_797_, lean_object* v_i_798_, lean_object* v_stop_799_, lean_object* v_b_800_){
_start:
{
size_t v_i_boxed_801_; size_t v_stop_boxed_802_; lean_object* v_res_803_; 
v_i_boxed_801_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_stop_boxed_802_ = lean_unbox_usize(v_stop_799_);
lean_dec(v_stop_799_);
v_res_803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_795_, v_nc_x3f_796_, v_as_797_, v_i_boxed_801_, v_stop_boxed_802_, v_b_800_);
lean_dec_ref(v_as_797_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_804_, lean_object* v_nc_x3f_805_, lean_object* v_msg_806_, lean_object* v_acc_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_804_, v_nc_x3f_805_, v_msg_806_, v_acc_807_);
lean_dec_ref(v_msg_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = lean_box(0);
v___x_813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_814_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_812_, v___x_812_, v_msg_811_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_815_);
lean_dec_ref(v_msg_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_819_, lean_object* v_stx_820_){
_start:
{
lean_object* v___x_821_; 
lean_inc(v_stx_820_);
v___x_821_ = l_Lean_Syntax_getKind(v_stx_820_);
if (lean_obj_tag(v___x_821_) == 1)
{
lean_object* v_pre_822_; 
v_pre_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_pre_822_);
if (lean_obj_tag(v_pre_822_) == 1)
{
lean_object* v_pre_823_; 
v_pre_823_ = lean_ctor_get(v_pre_822_, 0);
lean_inc(v_pre_823_);
if (lean_obj_tag(v_pre_823_) == 1)
{
lean_object* v_pre_824_; 
v_pre_824_ = lean_ctor_get(v_pre_823_, 0);
lean_inc(v_pre_824_);
if (lean_obj_tag(v_pre_824_) == 1)
{
lean_object* v_pre_825_; 
v_pre_825_ = lean_ctor_get(v_pre_824_, 0);
if (lean_obj_tag(v_pre_825_) == 0)
{
lean_object* v_str_826_; lean_object* v_str_827_; lean_object* v_str_828_; lean_object* v_str_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_str_826_ = lean_ctor_get(v___x_821_, 1);
lean_inc_ref(v_str_826_);
lean_dec_ref_known(v___x_821_, 2);
v_str_827_ = lean_ctor_get(v_pre_822_, 1);
lean_inc_ref(v_str_827_);
lean_dec_ref_known(v_pre_822_, 2);
v_str_828_ = lean_ctor_get(v_pre_823_, 1);
lean_inc_ref(v_str_828_);
lean_dec_ref_known(v_pre_823_, 2);
v_str_829_ = lean_ctor_get(v_pre_824_, 1);
lean_inc_ref(v_str_829_);
lean_dec_ref_known(v_pre_824_, 2);
v___x_830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_831_ = lean_string_dec_eq(v_str_829_, v___x_830_);
lean_dec_ref(v_str_829_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec_ref(v_str_828_);
lean_dec_ref(v_str_827_);
lean_dec_ref(v_str_826_);
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_834_ = lean_string_dec_eq(v_str_828_, v___x_833_);
lean_dec_ref(v_str_828_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v_str_827_);
lean_dec_ref(v_str_826_);
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_835_ = lean_box(0);
return v___x_835_;
}
else
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_837_ = lean_string_dec_eq(v_str_827_, v___x_836_);
lean_dec_ref(v_str_827_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v_str_826_);
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_838_ = lean_box(0);
return v___x_838_;
}
else
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_840_ = lean_string_dec_eq(v_str_826_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_842_ = lean_string_dec_eq(v_str_826_, v___x_841_);
lean_dec_ref(v_str_826_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_843_ = lean_box(0);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v_body_845_; lean_object* v___y_847_; lean_object* v___x_850_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v_body_845_ = l_Lean_Syntax_getArg(v_stx_820_, v___x_844_);
v___x_850_ = l_Lean_Syntax_getTailPos_x3f(v_body_845_, v___x_840_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_unsigned_to_nat(2u);
v___x_852_ = l_Lean_Syntax_getArg(v_stx_820_, v___x_851_);
lean_dec(v_stx_820_);
v___x_853_ = l_Lean_Syntax_getPos_x3f(v___x_852_, v___x_840_);
lean_dec(v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_stop_854_; 
v_stop_854_ = lean_ctor_get(v_range_819_, 1);
lean_inc(v_stop_854_);
lean_dec_ref(v_range_819_);
v___y_847_ = v_stop_854_;
goto v___jp_846_;
}
else
{
lean_object* v_val_855_; 
lean_dec_ref(v_range_819_);
v_val_855_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v___x_853_, 1);
v___y_847_ = v_val_855_;
goto v___jp_846_;
}
}
else
{
lean_object* v_val_856_; 
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v_val_856_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v___x_850_, 1);
v___y_847_ = v_val_856_;
goto v___jp_846_;
}
v___jp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_body_845_);
lean_ctor_set(v___x_848_, 1, v___y_847_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
else
{
lean_object* v___x_857_; lean_object* v_body_858_; lean_object* v___y_860_; uint8_t v___x_863_; lean_object* v___x_864_; 
lean_dec_ref(v_str_826_);
v___x_857_ = lean_unsigned_to_nat(0u);
v_body_858_ = l_Lean_Syntax_getArg(v_stx_820_, v___x_857_);
lean_dec(v_stx_820_);
v___x_863_ = 0;
v___x_864_ = l_Lean_Syntax_getTailPos_x3f(v_body_858_, v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_stop_865_; 
v_stop_865_ = lean_ctor_get(v_range_819_, 1);
lean_inc(v_stop_865_);
lean_dec_ref(v_range_819_);
v___y_860_ = v_stop_865_;
goto v___jp_859_;
}
else
{
lean_object* v_val_866_; 
lean_dec_ref(v_range_819_);
v_val_866_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v___x_864_, 1);
v___y_860_ = v_val_866_;
goto v___jp_859_;
}
v___jp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_body_858_);
lean_ctor_set(v___x_861_, 1, v___y_860_);
v___x_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
}
}
}
}
else
{
lean_object* v___x_867_; 
lean_dec_ref_known(v_pre_824_, 2);
lean_dec_ref_known(v_pre_823_, 2);
lean_dec_ref_known(v_pre_822_, 2);
lean_dec_ref_known(v___x_821_, 2);
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_867_ = lean_box(0);
return v___x_867_;
}
}
else
{
lean_object* v___x_868_; 
lean_dec_ref_known(v_pre_823_, 2);
lean_dec(v_pre_824_);
lean_dec_ref_known(v_pre_822_, 2);
lean_dec_ref_known(v___x_821_, 2);
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_868_ = lean_box(0);
return v___x_868_;
}
}
else
{
lean_object* v___x_869_; 
lean_dec_ref_known(v_pre_822_, 2);
lean_dec(v_pre_823_);
lean_dec_ref_known(v___x_821_, 2);
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_869_ = lean_box(0);
return v___x_869_;
}
}
else
{
lean_object* v___x_870_; 
lean_dec(v_pre_822_);
lean_dec_ref_known(v___x_821_, 2);
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_870_ = lean_box(0);
return v___x_870_;
}
}
else
{
lean_object* v___x_871_; 
lean_dec(v___x_821_);
lean_dec(v_stx_820_);
lean_dec_ref(v_range_819_);
v___x_871_ = lean_box(0);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_875_, lean_object* v_stx_876_){
_start:
{
lean_object* v___x_877_; 
lean_inc(v_stx_876_);
lean_inc_ref(v_range_875_);
v___x_877_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_875_, v_stx_876_);
if (lean_obj_tag(v___x_877_) == 1)
{
lean_dec(v_stx_876_);
lean_dec_ref(v_range_875_);
return v___x_877_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v_fst_884_; 
lean_dec(v___x_877_);
v___x_878_ = l_Lean_Syntax_getArgs(v_stx_876_);
lean_dec(v_stx_876_);
v___x_879_ = lean_box(0);
v___x_880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_881_ = lean_array_size(v___x_878_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_875_, v___x_878_, v_sz_881_, v___x_882_, v___x_880_);
lean_dec_ref(v___x_878_);
v_fst_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_fst_884_);
lean_dec_ref(v___x_883_);
if (lean_obj_tag(v_fst_884_) == 0)
{
return v___x_879_;
}
else
{
lean_object* v_val_885_; 
v_val_885_ = lean_ctor_get(v_fst_884_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v_fst_884_, 1);
return v_val_885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_886_, lean_object* v_as_887_, size_t v_sz_888_, size_t v_i_889_, lean_object* v_b_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = lean_usize_dec_lt(v_i_889_, v_sz_888_);
if (v___x_891_ == 0)
{
lean_dec_ref(v_range_886_);
lean_inc_ref(v_b_890_);
return v_b_890_;
}
else
{
lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v_a_893_ = lean_array_uget_borrowed(v_as_887_, v_i_889_);
lean_inc(v_a_893_);
lean_inc_ref(v_range_886_);
v___x_894_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_886_, v_a_893_);
if (lean_obj_tag(v___x_894_) == 1)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v_range_886_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_892_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; size_t v___x_898_; size_t v___x_899_; 
lean_dec(v___x_894_);
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_898_ = ((size_t)1ULL);
v___x_899_ = lean_usize_add(v_i_889_, v___x_898_);
v_i_889_ = v___x_899_;
v_b_890_ = v___x_897_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_901_, lean_object* v_as_902_, lean_object* v_sz_903_, lean_object* v_i_904_, lean_object* v_b_905_){
_start:
{
size_t v_sz_boxed_906_; size_t v_i_boxed_907_; lean_object* v_res_908_; 
v_sz_boxed_906_ = lean_unbox_usize(v_sz_903_);
lean_dec(v_sz_903_);
v_i_boxed_907_ = lean_unbox_usize(v_i_904_);
lean_dec(v_i_904_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_901_, v_as_902_, v_sz_boxed_906_, v_i_boxed_907_, v_b_905_);
lean_dec_ref(v_b_905_);
lean_dec_ref(v_as_902_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_909_, lean_object* v_stx_910_){
_start:
{
uint8_t v___x_911_; lean_object* v___x_912_; 
v___x_911_ = 0;
v___x_912_ = l_Lean_Syntax_getRange_x3f(v_stx_910_, v___x_911_);
if (lean_obj_tag(v___x_912_) == 1)
{
lean_object* v_val_913_; uint8_t v___x_914_; 
v_val_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_Syntax_Range_includes(v_val_913_, v_range_909_, v___x_911_, v___x_911_);
lean_dec(v_val_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_stx_910_);
lean_dec_ref(v_range_909_);
v___x_915_ = lean_box(0);
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; size_t v_sz_918_; size_t v___x_919_; lean_object* v___x_920_; lean_object* v_fst_921_; 
v___x_916_ = l_Lean_Syntax_getArgs(v_stx_910_);
v___x_917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_918_ = lean_array_size(v___x_916_);
v___x_919_ = ((size_t)0ULL);
lean_inc_ref(v_range_909_);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_909_, v___x_916_, v_sz_918_, v___x_919_, v___x_917_);
lean_dec_ref(v___x_916_);
v_fst_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_fst_921_);
lean_dec_ref(v___x_920_);
if (lean_obj_tag(v_fst_921_) == 0)
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_909_, v_stx_910_);
return v___x_922_;
}
else
{
lean_object* v_val_923_; 
lean_dec(v_stx_910_);
lean_dec_ref(v_range_909_);
v_val_923_ = lean_ctor_get(v_fst_921_, 0);
lean_inc(v_val_923_);
lean_dec_ref_known(v_fst_921_, 1);
return v_val_923_;
}
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v___x_912_);
lean_dec(v_stx_910_);
lean_dec_ref(v_range_909_);
v___x_924_ = lean_box(0);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_925_, lean_object* v_as_926_, size_t v_sz_927_, size_t v_i_928_, lean_object* v_b_929_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = lean_usize_dec_lt(v_i_928_, v_sz_927_);
if (v___x_930_ == 0)
{
lean_dec_ref(v_range_925_);
lean_inc_ref(v_b_929_);
return v_b_929_;
}
else
{
lean_object* v___x_931_; lean_object* v_a_932_; lean_object* v___x_933_; 
v___x_931_ = lean_box(0);
v_a_932_ = lean_array_uget_borrowed(v_as_926_, v_i_928_);
lean_inc(v_a_932_);
lean_inc_ref(v_range_925_);
v___x_933_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_925_, v_a_932_);
if (lean_obj_tag(v___x_933_) == 1)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_range_925_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_931_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; size_t v___x_937_; size_t v___x_938_; 
lean_dec(v___x_933_);
v___x_936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_928_, v___x_937_);
v_i_928_ = v___x_938_;
v_b_929_ = v___x_936_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_940_, lean_object* v_as_941_, lean_object* v_sz_942_, lean_object* v_i_943_, lean_object* v_b_944_){
_start:
{
size_t v_sz_boxed_945_; size_t v_i_boxed_946_; lean_object* v_res_947_; 
v_sz_boxed_945_ = lean_unbox_usize(v_sz_942_);
lean_dec(v_sz_942_);
v_i_boxed_946_ = lean_unbox_usize(v_i_943_);
lean_dec(v_i_943_);
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_940_, v_as_941_, v_sz_boxed_945_, v_i_boxed_946_, v_b_944_);
lean_dec_ref(v_b_944_);
lean_dec_ref(v_as_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_948_, lean_object* v_range_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_949_, v_cmd_948_);
return v___x_950_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_opts_951_, lean_object* v_opt_952_){
_start:
{
lean_object* v_name_953_; lean_object* v_defValue_954_; lean_object* v_map_955_; lean_object* v___x_956_; 
v_name_953_ = lean_ctor_get(v_opt_952_, 0);
v_defValue_954_ = lean_ctor_get(v_opt_952_, 1);
v_map_955_ = lean_ctor_get(v_opts_951_, 0);
v___x_956_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_955_, v_name_953_);
if (lean_obj_tag(v___x_956_) == 0)
{
uint8_t v___x_957_; 
v___x_957_ = lean_unbox(v_defValue_954_);
return v___x_957_;
}
else
{
lean_object* v_val_958_; 
v_val_958_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_val_958_);
lean_dec_ref_known(v___x_956_, 1);
if (lean_obj_tag(v_val_958_) == 1)
{
uint8_t v_v_959_; 
v_v_959_ = lean_ctor_get_uint8(v_val_958_, 0);
lean_dec_ref_known(v_val_958_, 0);
return v_v_959_;
}
else
{
uint8_t v___x_960_; 
lean_dec(v_val_958_);
v___x_960_ = lean_unbox(v_defValue_954_);
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_opts_961_, lean_object* v_opt_962_){
_start:
{
uint8_t v_res_963_; lean_object* v_r_964_; 
v_res_963_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_961_, v_opt_962_);
lean_dec_ref(v_opt_962_);
lean_dec_ref(v_opts_961_);
v_r_964_ = lean_box(v_res_963_);
return v_r_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_965_, lean_object* v_info_966_, lean_object* v_acc_967_){
_start:
{
if (lean_obj_tag(v_info_966_) == 0)
{
lean_object* v_i_968_; lean_object* v_toElabInfo_969_; lean_object* v_mctxBefore_970_; lean_object* v_goalsBefore_971_; lean_object* v_stx_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_990_; 
v_i_968_ = lean_ctor_get(v_info_966_, 0);
lean_inc_ref(v_i_968_);
lean_dec_ref_known(v_info_966_, 1);
v_toElabInfo_969_ = lean_ctor_get(v_i_968_, 0);
lean_inc_ref(v_toElabInfo_969_);
v_mctxBefore_970_ = lean_ctor_get(v_i_968_, 1);
lean_inc_ref(v_mctxBefore_970_);
v_goalsBefore_971_ = lean_ctor_get(v_i_968_, 2);
lean_inc(v_goalsBefore_971_);
lean_dec_ref(v_i_968_);
v_stx_972_ = lean_ctor_get(v_toElabInfo_969_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_toElabInfo_969_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v_toElabInfo_969_, 0);
lean_dec(v_unused_991_);
v___x_974_ = v_toElabInfo_969_;
v_isShared_975_ = v_isSharedCheck_990_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_stx_972_);
lean_dec(v_toElabInfo_969_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_990_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
uint8_t v___x_976_; 
lean_inc(v_stx_972_);
v___x_976_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_972_);
if (v___x_976_ == 0)
{
lean_del_object(v___x_974_);
lean_dec(v_stx_972_);
lean_dec(v_goalsBefore_971_);
lean_dec_ref(v_mctxBefore_970_);
return v_acc_967_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = l_List_head_x3f___redArg(v_goalsBefore_971_);
lean_dec(v_goalsBefore_971_);
if (lean_obj_tag(v___x_977_) == 1)
{
lean_object* v_toCommandContextInfo_978_; lean_object* v_val_979_; lean_object* v_env_980_; lean_object* v_options_981_; lean_object* v_currNamespace_982_; lean_object* v_openDecls_983_; lean_object* v_namingCtx_985_; 
v_toCommandContextInfo_978_ = lean_ctor_get(v_ctx_965_, 0);
v_val_979_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_val_979_);
lean_dec_ref_known(v___x_977_, 1);
v_env_980_ = lean_ctor_get(v_toCommandContextInfo_978_, 0);
v_options_981_ = lean_ctor_get(v_toCommandContextInfo_978_, 4);
v_currNamespace_982_ = lean_ctor_get(v_toCommandContextInfo_978_, 5);
v_openDecls_983_ = lean_ctor_get(v_toCommandContextInfo_978_, 6);
lean_inc(v_openDecls_983_);
lean_inc(v_currNamespace_982_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_openDecls_983_);
lean_ctor_set(v___x_974_, 0, v_currNamespace_982_);
v_namingCtx_985_ = v___x_974_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_currNamespace_982_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_openDecls_983_);
v_namingCtx_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_box(1);
lean_inc_ref(v_options_981_);
lean_inc_ref(v_env_980_);
v___x_987_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_stx_972_);
lean_ctor_set(v___x_987_, 2, v_env_980_);
lean_ctor_set(v___x_987_, 3, v_mctxBefore_970_);
lean_ctor_set(v___x_987_, 4, v_options_981_);
lean_ctor_set(v___x_987_, 5, v_namingCtx_985_);
lean_ctor_set(v___x_987_, 6, v_val_979_);
v___x_988_ = lean_array_push(v_acc_967_, v___x_987_);
return v___x_988_;
}
}
else
{
lean_dec(v___x_977_);
lean_del_object(v___x_974_);
lean_dec(v_stx_972_);
lean_dec_ref(v_mctxBefore_970_);
return v_acc_967_;
}
}
}
}
else
{
lean_dec_ref(v_info_966_);
return v_acc_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_992_, lean_object* v_info_993_, lean_object* v_acc_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_992_, v_info_993_, v_acc_994_);
lean_dec_ref(v_ctx_992_);
return v_res_995_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1));
v___x_1002_ = lean_name_eq(v_x_1000_, v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___boxed(lean_object* v_x_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(v_x_1003_);
lean_dec(v_x_1003_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(lean_object* v_a_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
uint8_t v___x_1008_; 
v___x_1008_ = 0;
return v___x_1008_;
}
else
{
lean_object* v_key_1009_; lean_object* v_tail_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v_fst_1013_; lean_object* v_snd_1014_; uint8_t v___x_1015_; 
v_key_1009_ = lean_ctor_get(v_x_1007_, 0);
v_tail_1010_ = lean_ctor_get(v_x_1007_, 2);
v_fst_1011_ = lean_ctor_get(v_key_1009_, 0);
v_snd_1012_ = lean_ctor_get(v_key_1009_, 1);
v_fst_1013_ = lean_ctor_get(v_a_1006_, 0);
v_snd_1014_ = lean_ctor_get(v_a_1006_, 1);
v___x_1015_ = l_Lean_Syntax_instBEqRange_beq(v_fst_1011_, v_fst_1013_);
if (v___x_1015_ == 0)
{
v_x_1007_ = v_tail_1010_;
goto _start;
}
else
{
uint8_t v___x_1017_; 
v___x_1017_ = l_Lean_instBEqMVarId_beq(v_snd_1012_, v_snd_1014_);
if (v___x_1017_ == 0)
{
v_x_1007_ = v_tail_1010_;
goto _start;
}
else
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg___boxed(lean_object* v_a_1019_, lean_object* v_x_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1019_, v_x_1020_);
lean_dec(v_x_1020_);
lean_dec_ref(v_a_1019_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
return v_x_1023_;
}
else
{
lean_object* v_key_1025_; lean_object* v_value_1026_; lean_object* v_tail_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1054_; 
v_key_1025_ = lean_ctor_get(v_x_1024_, 0);
v_value_1026_ = lean_ctor_get(v_x_1024_, 1);
v_tail_1027_ = lean_ctor_get(v_x_1024_, 2);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1029_ = v_x_1024_;
v_isShared_1030_ = v_isSharedCheck_1054_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_tail_1027_);
lean_inc(v_value_1026_);
lean_inc(v_key_1025_);
lean_dec(v_x_1024_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1054_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v_fold_1039_; uint64_t v___x_1040_; uint64_t v___x_1041_; uint64_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_fst_1031_ = lean_ctor_get(v_key_1025_, 0);
v_snd_1032_ = lean_ctor_get(v_key_1025_, 1);
v___x_1033_ = lean_array_get_size(v_x_1023_);
v___x_1034_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1031_);
v___x_1035_ = l_Lean_instHashableMVarId_hash(v_snd_1032_);
v___x_1036_ = lean_uint64_mix_hash(v___x_1034_, v___x_1035_);
v___x_1037_ = 32ULL;
v___x_1038_ = lean_uint64_shift_right(v___x_1036_, v___x_1037_);
v_fold_1039_ = lean_uint64_xor(v___x_1036_, v___x_1038_);
v___x_1040_ = 16ULL;
v___x_1041_ = lean_uint64_shift_right(v_fold_1039_, v___x_1040_);
v___x_1042_ = lean_uint64_xor(v_fold_1039_, v___x_1041_);
v___x_1043_ = lean_uint64_to_usize(v___x_1042_);
v___x_1044_ = lean_usize_of_nat(v___x_1033_);
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_sub(v___x_1044_, v___x_1045_);
v___x_1047_ = lean_usize_land(v___x_1043_, v___x_1046_);
v___x_1048_ = lean_array_uget_borrowed(v_x_1023_, v___x_1047_);
lean_inc(v___x_1048_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 2, v___x_1048_);
v___x_1050_ = v___x_1029_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_key_1025_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_value_1026_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_array_uset(v_x_1023_, v___x_1047_, v___x_1050_);
v_x_1023_ = v___x_1051_;
v_x_1024_ = v_tail_1027_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1055_, lean_object* v_source_1056_, lean_object* v_target_1057_){
_start:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_array_get_size(v_source_1056_);
v___x_1059_ = lean_nat_dec_lt(v_i_1055_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec_ref(v_source_1056_);
lean_dec(v_i_1055_);
return v_target_1057_;
}
else
{
lean_object* v_es_1060_; lean_object* v___x_1061_; lean_object* v_source_1062_; lean_object* v_target_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_es_1060_ = lean_array_fget(v_source_1056_, v_i_1055_);
v___x_1061_ = lean_box(0);
v_source_1062_ = lean_array_fset(v_source_1056_, v_i_1055_, v___x_1061_);
v_target_1063_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1057_, v_es_1060_);
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_nat_add(v_i_1055_, v___x_1064_);
lean_dec(v_i_1055_);
v_i_1055_ = v___x_1065_;
v_source_1056_ = v_source_1062_;
v_target_1057_ = v_target_1063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(lean_object* v_data_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v_nbuckets_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1068_ = lean_array_get_size(v_data_1067_);
v___x_1069_ = lean_unsigned_to_nat(2u);
v_nbuckets_1070_ = lean_nat_mul(v___x_1068_, v___x_1069_);
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_mk_array(v_nbuckets_1070_, v___x_1072_);
v___x_1074_ = lean_array_propagate_mark(v_data_1067_, v___x_1073_);
v___x_1075_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v___x_1071_, v_data_1067_, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v_m_1076_, lean_object* v_a_1077_, lean_object* v_b_1078_){
_start:
{
lean_object* v_size_1079_; lean_object* v_buckets_1080_; lean_object* v_fst_1081_; lean_object* v_snd_1082_; lean_object* v___x_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; uint64_t v_fold_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v_bkt_1098_; uint8_t v___x_1099_; 
v_size_1079_ = lean_ctor_get(v_m_1076_, 0);
v_buckets_1080_ = lean_ctor_get(v_m_1076_, 1);
v_fst_1081_ = lean_ctor_get(v_a_1077_, 0);
v_snd_1082_ = lean_ctor_get(v_a_1077_, 1);
v___x_1083_ = lean_array_get_size(v_buckets_1080_);
v___x_1084_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1081_);
v___x_1085_ = l_Lean_instHashableMVarId_hash(v_snd_1082_);
v___x_1086_ = lean_uint64_mix_hash(v___x_1084_, v___x_1085_);
v___x_1087_ = 32ULL;
v___x_1088_ = lean_uint64_shift_right(v___x_1086_, v___x_1087_);
v_fold_1089_ = lean_uint64_xor(v___x_1086_, v___x_1088_);
v___x_1090_ = 16ULL;
v___x_1091_ = lean_uint64_shift_right(v_fold_1089_, v___x_1090_);
v___x_1092_ = lean_uint64_xor(v_fold_1089_, v___x_1091_);
v___x_1093_ = lean_uint64_to_usize(v___x_1092_);
v___x_1094_ = lean_usize_of_nat(v___x_1083_);
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = lean_usize_sub(v___x_1094_, v___x_1095_);
v___x_1097_ = lean_usize_land(v___x_1093_, v___x_1096_);
v_bkt_1098_ = lean_array_uget_borrowed(v_buckets_1080_, v___x_1097_);
v___x_1099_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1077_, v_bkt_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1120_; 
lean_inc_ref(v_buckets_1080_);
lean_inc(v_size_1079_);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_m_1076_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; lean_object* v_unused_1122_; 
v_unused_1121_ = lean_ctor_get(v_m_1076_, 1);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_m_1076_, 0);
lean_dec(v_unused_1122_);
v___x_1101_ = v_m_1076_;
v_isShared_1102_ = v_isSharedCheck_1120_;
goto v_resetjp_1100_;
}
else
{
lean_dec(v_m_1076_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1120_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v_size_x27_1104_; lean_object* v___x_1105_; lean_object* v_buckets_x27_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v_size_x27_1104_ = lean_nat_add(v_size_1079_, v___x_1103_);
lean_dec(v_size_1079_);
lean_inc(v_bkt_1098_);
v___x_1105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1105_, 0, v_a_1077_);
lean_ctor_set(v___x_1105_, 1, v_b_1078_);
lean_ctor_set(v___x_1105_, 2, v_bkt_1098_);
v_buckets_x27_1106_ = lean_array_uset(v_buckets_1080_, v___x_1097_, v___x_1105_);
v___x_1107_ = lean_unsigned_to_nat(4u);
v___x_1108_ = lean_nat_mul(v_size_x27_1104_, v___x_1107_);
v___x_1109_ = lean_unsigned_to_nat(3u);
v___x_1110_ = lean_nat_div(v___x_1108_, v___x_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_array_get_size(v_buckets_x27_1106_);
v___x_1112_ = lean_nat_dec_le(v___x_1110_, v___x_1111_);
lean_dec(v___x_1110_);
if (v___x_1112_ == 0)
{
lean_object* v_val_1113_; lean_object* v___x_1115_; 
v_val_1113_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_buckets_x27_1106_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v_val_1113_);
lean_ctor_set(v___x_1101_, 0, v_size_x27_1104_);
v___x_1115_ = v___x_1101_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_size_x27_1104_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_val_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
else
{
lean_object* v___x_1118_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v_buckets_x27_1106_);
lean_ctor_set(v___x_1101_, 0, v_size_x27_1104_);
v___x_1118_ = v___x_1101_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_size_x27_1104_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_buckets_x27_1106_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_dec(v_b_1078_);
lean_dec_ref(v_a_1077_);
return v_m_1076_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_buckets_1125_; lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___x_1128_; uint64_t v___x_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; uint64_t v___x_1133_; uint64_t v_fold_1134_; uint64_t v___x_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_buckets_1125_ = lean_ctor_get(v_m_1123_, 1);
v_fst_1126_ = lean_ctor_get(v_a_1124_, 0);
v_snd_1127_ = lean_ctor_get(v_a_1124_, 1);
v___x_1128_ = lean_array_get_size(v_buckets_1125_);
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
v___x_1143_ = lean_array_uget_borrowed(v_buckets_1125_, v___x_1142_);
v___x_1144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1124_, v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object* v_m_1145_, lean_object* v_a_1146_){
_start:
{
uint8_t v_res_1147_; lean_object* v_r_1148_; 
v_res_1147_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1145_, v_a_1146_);
lean_dec_ref(v_a_1146_);
lean_dec_ref(v_m_1145_);
v_r_1148_ = lean_box(v_res_1147_);
return v_r_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object* v___x_1149_, lean_object* v_fst_1150_, lean_object* v_snd_1151_, lean_object* v___x_1152_, lean_object* v_as_1153_, size_t v_sz_1154_, size_t v_i_1155_, lean_object* v_b_1156_){
_start:
{
lean_object* v_a_1159_; uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1155_, v_sz_1154_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_dec(v___x_1152_);
lean_dec(v_snd_1151_);
lean_dec(v_fst_1150_);
lean_dec_ref(v___x_1149_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_b_1156_);
return v___x_1164_;
}
else
{
lean_object* v_a_1165_; lean_object* v_snd_1166_; lean_object* v_fst_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1203_; 
v_a_1165_ = lean_array_uget(v_as_1153_, v_i_1155_);
v_snd_1166_ = lean_ctor_get(v_a_1165_, 1);
v_fst_1167_ = lean_ctor_get(v_a_1165_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_a_1165_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1169_ = v_a_1165_;
v_isShared_1170_ = v_isSharedCheck_1203_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1166_);
lean_inc(v_fst_1167_);
lean_dec(v_a_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1203_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1202_; 
v_fst_1171_ = lean_ctor_get(v_snd_1166_, 0);
v_snd_1172_ = lean_ctor_get(v_snd_1166_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_snd_1166_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1174_ = v_snd_1166_;
v_isShared_1175_ = v_isSharedCheck_1202_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snd_1172_);
lean_inc(v_fst_1171_);
lean_dec(v_snd_1166_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1202_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1201_; 
v_fst_1176_ = lean_ctor_get(v_b_1156_, 0);
v_snd_1177_ = lean_ctor_get(v_b_1156_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_b_1156_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1179_ = v_b_1156_;
v_isShared_1180_ = v_isSharedCheck_1201_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_snd_1177_);
lean_inc(v_fst_1176_);
lean_dec(v_b_1156_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1201_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
lean_inc(v_snd_1172_);
lean_inc_ref(v___x_1149_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v_snd_1172_);
lean_ctor_set(v___x_1179_, 0, v___x_1149_);
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_snd_1172_);
v___x_1182_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
uint8_t v___x_1183_; 
v___x_1183_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1177_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v_env_1184_; lean_object* v_mctx_1185_; lean_object* v_opts_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v_env_1184_ = lean_ctor_get(v_fst_1167_, 0);
lean_inc_ref(v_env_1184_);
v_mctx_1185_ = lean_ctor_get(v_fst_1167_, 1);
lean_inc_ref(v_mctx_1185_);
v_opts_1186_ = lean_ctor_get(v_fst_1167_, 3);
lean_inc_ref(v_opts_1186_);
lean_dec(v_fst_1167_);
v___x_1187_ = lean_box(0);
v___x_1188_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1177_, v___x_1182_, v___x_1187_);
lean_inc(v_snd_1151_);
lean_inc(v_fst_1150_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_snd_1151_);
lean_ctor_set(v___x_1169_, 0, v_fst_1150_);
v___x_1190_ = v___x_1169_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_fst_1150_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_snd_1151_);
v___x_1190_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_inc(v___x_1152_);
v___x_1191_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v___x_1152_);
lean_ctor_set(v___x_1191_, 2, v_env_1184_);
lean_ctor_set(v___x_1191_, 3, v_mctx_1185_);
lean_ctor_set(v___x_1191_, 4, v_opts_1186_);
lean_ctor_set(v___x_1191_, 5, v_fst_1171_);
lean_ctor_set(v___x_1191_, 6, v_snd_1172_);
v___x_1192_ = lean_array_push(v_fst_1176_, v___x_1191_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1188_);
lean_ctor_set(v___x_1174_, 0, v___x_1192_);
v___x_1194_ = v___x_1174_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1188_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
v_a_1159_ = v___x_1194_;
goto v___jp_1158_;
}
}
}
else
{
lean_object* v___x_1198_; 
lean_dec_ref(v___x_1182_);
lean_dec(v_snd_1172_);
lean_dec(v_fst_1171_);
lean_del_object(v___x_1169_);
lean_dec(v_fst_1167_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_snd_1177_);
lean_ctor_set(v___x_1174_, 0, v_fst_1176_);
v___x_1198_ = v___x_1174_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_fst_1176_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_snd_1177_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
v_a_1159_ = v___x_1198_;
goto v___jp_1158_;
}
}
}
}
}
}
}
v___jp_1158_:
{
size_t v___x_1160_; size_t v___x_1161_; 
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_add(v_i_1155_, v___x_1160_);
v_i_1155_ = v___x_1161_;
v_b_1156_ = v_a_1159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object* v___x_1204_, lean_object* v_fst_1205_, lean_object* v_snd_1206_, lean_object* v___x_1207_, lean_object* v_as_1208_, lean_object* v_sz_1209_, lean_object* v_i_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_){
_start:
{
size_t v_sz_boxed_1213_; size_t v_i_boxed_1214_; lean_object* v_res_1215_; 
v_sz_boxed_1213_ = lean_unbox_usize(v_sz_1209_);
lean_dec(v_sz_1209_);
v_i_boxed_1214_ = lean_unbox_usize(v_i_1210_);
lean_dec(v_i_1210_);
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1204_, v_fst_1205_, v_snd_1206_, v___x_1207_, v_as_1208_, v_sz_boxed_1213_, v_i_boxed_1214_, v_b_1211_);
lean_dec_ref(v_as_1208_);
return v_res_1215_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
lean_ctor_set(v___x_1220_, 3, v___x_1219_);
lean_ctor_set(v___x_1220_, 4, v___x_1218_);
lean_ctor_set(v___x_1220_, 5, v___x_1218_);
lean_ctor_set(v___x_1220_, 6, v___x_1218_);
lean_ctor_set(v___x_1220_, 7, v___x_1218_);
lean_ctor_set(v___x_1220_, 8, v___x_1218_);
lean_ctor_set(v___x_1220_, 9, v___x_1218_);
lean_ctor_set(v___x_1220_, 10, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_unsigned_to_nat(32u);
v___x_1222_ = lean_mk_empty_array_with_capacity(v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = ((size_t)5ULL);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_unsigned_to_nat(32u);
v___x_1227_ = lean_mk_empty_array_with_capacity(v___x_1226_);
v___x_1228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2);
v___x_1229_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v___x_1227_);
lean_ctor_set(v___x_1229_, 2, v___x_1225_);
lean_ctor_set(v___x_1229_, 3, v___x_1225_);
lean_ctor_set_usize(v___x_1229_, 4, v___x_1224_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_box(1);
v___x_1231_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3);
v___x_1232_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___x_1231_);
lean_ctor_set(v___x_1233_, 2, v___x_1230_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(lean_object* v_msgData_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; lean_object* v_env_1238_; uint8_t v___x_1239_; lean_object* v_env_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_scopes_1243_; lean_object* v___x_1244_; lean_object* v_opts_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1237_ = lean_st_ref_get(v___y_1235_);
v_env_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc_ref(v_env_1238_);
lean_dec(v___x_1237_);
v___x_1239_ = 0;
v_env_1240_ = l_Lean_Environment_setRecordingDeps(v_env_1238_, v___x_1239_);
v___x_1241_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1242_ = lean_st_ref_get(v___y_1235_);
v_scopes_1243_ = lean_ctor_get(v___x_1242_, 2);
lean_inc(v_scopes_1243_);
lean_dec(v___x_1242_);
v___x_1244_ = l_List_head_x21___redArg(v___x_1241_, v_scopes_1243_);
lean_dec(v_scopes_1243_);
v_opts_1245_ = lean_ctor_get(v___x_1244_, 1);
lean_inc_ref(v_opts_1245_);
lean_dec(v___x_1244_);
v___x_1246_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1);
v___x_1247_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4);
v___x_1248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1248_, 0, v_env_1240_);
lean_ctor_set(v___x_1248_, 1, v___x_1246_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
lean_ctor_set(v___x_1248_, 3, v_opts_1245_);
v___x_1249_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v_msgData_1234_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_1251_, v___y_1252_);
lean_dec(v___y_1252_);
return v_res_1254_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1255_; double v___x_1256_; 
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_float_of_nat(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v_cls_1259_, lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Elab_Command_getRef___redArg(v___y_1261_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1315_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1266_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msg_1260_, v___y_1262_);
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1315_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1315_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v_traceState_1272_; lean_object* v_env_1273_; lean_object* v_messages_1274_; lean_object* v_scopes_1275_; lean_object* v_usedQuotCtxts_1276_; lean_object* v_nextMacroScope_1277_; lean_object* v_maxRecDepth_1278_; lean_object* v_ngen_1279_; lean_object* v_auxDeclNGen_1280_; lean_object* v_infoState_1281_; lean_object* v_snapshotTasks_1282_; lean_object* v_prevLinterStates_1283_; lean_object* v_codeQualityEntryTasks_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1314_; 
v___x_1271_ = lean_st_ref_take(v___y_1262_);
v_traceState_1272_ = lean_ctor_get(v___x_1271_, 9);
v_env_1273_ = lean_ctor_get(v___x_1271_, 0);
v_messages_1274_ = lean_ctor_get(v___x_1271_, 1);
v_scopes_1275_ = lean_ctor_get(v___x_1271_, 2);
v_usedQuotCtxts_1276_ = lean_ctor_get(v___x_1271_, 3);
v_nextMacroScope_1277_ = lean_ctor_get(v___x_1271_, 4);
v_maxRecDepth_1278_ = lean_ctor_get(v___x_1271_, 5);
v_ngen_1279_ = lean_ctor_get(v___x_1271_, 6);
v_auxDeclNGen_1280_ = lean_ctor_get(v___x_1271_, 7);
v_infoState_1281_ = lean_ctor_get(v___x_1271_, 8);
v_snapshotTasks_1282_ = lean_ctor_get(v___x_1271_, 10);
v_prevLinterStates_1283_ = lean_ctor_get(v___x_1271_, 11);
v_codeQualityEntryTasks_1284_ = lean_ctor_get(v___x_1271_, 12);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1286_ = v___x_1271_;
v_isShared_1287_ = v_isSharedCheck_1314_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1284_);
lean_inc(v_prevLinterStates_1283_);
lean_inc(v_snapshotTasks_1282_);
lean_inc(v_traceState_1272_);
lean_inc(v_infoState_1281_);
lean_inc(v_auxDeclNGen_1280_);
lean_inc(v_ngen_1279_);
lean_inc(v_maxRecDepth_1278_);
lean_inc(v_nextMacroScope_1277_);
lean_inc(v_usedQuotCtxts_1276_);
lean_inc(v_scopes_1275_);
lean_inc(v_messages_1274_);
lean_inc(v_env_1273_);
lean_dec(v___x_1271_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1314_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
uint64_t v_tid_1288_; lean_object* v_traces_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1313_; 
v_tid_1288_ = lean_ctor_get_uint64(v_traceState_1272_, sizeof(void*)*1);
v_traces_1289_ = lean_ctor_get(v_traceState_1272_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_traceState_1272_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1291_ = v_traceState_1272_;
v_isShared_1292_ = v_isSharedCheck_1313_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_traces_1289_);
lean_dec(v_traceState_1272_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1313_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; double v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_box(0);
v___x_1295_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_1296_ = 0;
v___x_1297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1298_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1298_, 0, v_cls_1259_);
lean_ctor_set(v___x_1298_, 1, v___x_1294_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
lean_ctor_set_float(v___x_1298_, sizeof(void*)*3, v___x_1295_);
lean_ctor_set_float(v___x_1298_, sizeof(void*)*3 + 8, v___x_1295_);
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*3 + 16, v___x_1296_);
v___x_1299_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_1300_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v_a_1267_);
lean_ctor_set(v___x_1300_, 2, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_a_1265_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_PersistentArray_push___redArg(v_traces_1289_, v___x_1301_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1302_);
v___x_1304_ = v___x_1291_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1302_);
lean_ctor_set_uint64(v_reuseFailAlloc_1312_, sizeof(void*)*1, v_tid_1288_);
v___x_1304_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 9, v___x_1304_);
v___x_1306_ = v___x_1286_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_env_1273_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_messages_1274_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_scopes_1275_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_usedQuotCtxts_1276_);
lean_ctor_set(v_reuseFailAlloc_1311_, 4, v_nextMacroScope_1277_);
lean_ctor_set(v_reuseFailAlloc_1311_, 5, v_maxRecDepth_1278_);
lean_ctor_set(v_reuseFailAlloc_1311_, 6, v_ngen_1279_);
lean_ctor_set(v_reuseFailAlloc_1311_, 7, v_auxDeclNGen_1280_);
lean_ctor_set(v_reuseFailAlloc_1311_, 8, v_infoState_1281_);
lean_ctor_set(v_reuseFailAlloc_1311_, 9, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1311_, 10, v_snapshotTasks_1282_);
lean_ctor_set(v_reuseFailAlloc_1311_, 11, v_prevLinterStates_1283_);
lean_ctor_set(v_reuseFailAlloc_1311_, 12, v_codeQualityEntryTasks_1284_);
v___x_1306_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_st_ref_put(v___y_1262_, v___x_1306_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1293_);
v___x_1309_ = v___x_1269_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1293_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_msg_1260_);
lean_dec(v_cls_1259_);
v_a_1316_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1264_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1264_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v_cls_1324_, lean_object* v_msg_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_cls_1324_, v_msg_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1329_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2));
v___x_1336_ = l_Lean_Name_append(v___x_1335_, v___x_1334_);
return v___x_1336_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4));
v___x_1339_ = l_Lean_stringToMessageData(v___x_1338_);
return v___x_1339_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6));
v___x_1342_ = l_Lean_stringToMessageData(v___x_1341_);
return v___x_1342_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8));
v___x_1345_ = l_Lean_stringToMessageData(v___x_1344_);
return v___x_1345_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10));
v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(lean_object* v___x_1349_, lean_object* v_val_1350_, lean_object* v_cmd_1351_, uint8_t v_onUnsolved_1352_, uint8_t v___y_1353_, lean_object* v_as_1354_, size_t v_sz_1355_, size_t v_i_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_usize_dec_lt(v_i_1356_, v_sz_1355_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec(v_cmd_1351_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_b_1357_);
return v___x_1362_;
}
else
{
lean_object* v_snd_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1511_; 
v_snd_1363_ = lean_ctor_get(v_b_1357_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_b_1357_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v_b_1357_, 0);
lean_dec(v_unused_1512_);
v___x_1365_ = v_b_1357_;
v_isShared_1366_ = v_isSharedCheck_1511_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snd_1363_);
lean_dec(v_b_1357_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1511_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_fst_1367_; lean_object* v_snd_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1510_; 
v_fst_1367_ = lean_ctor_get(v_snd_1363_, 0);
v_snd_1368_ = lean_ctor_get(v_snd_1363_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_snd_1363_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1370_ = v_snd_1363_;
v_isShared_1371_ = v_isSharedCheck_1510_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snd_1368_);
lean_inc(v_fst_1367_);
lean_dec(v_snd_1363_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1510_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_a_1372_; lean_object* v_pos_1373_; lean_object* v_endPos_1374_; uint8_t v_severity_1375_; lean_object* v_data_1376_; lean_object* v___x_1377_; lean_object* v_a_1379_; 
v_a_1372_ = lean_array_uget_borrowed(v_as_1354_, v_i_1356_);
v_pos_1373_ = lean_ctor_get(v_a_1372_, 1);
v_endPos_1374_ = lean_ctor_get(v_a_1372_, 2);
lean_inc(v_endPos_1374_);
v_severity_1375_ = lean_ctor_get_uint8(v_a_1372_, sizeof(void*)*5 + 1);
v_data_1376_ = lean_ctor_get(v_a_1372_, 4);
v___x_1377_ = lean_box(0);
if (v_severity_1375_ == 2)
{
lean_object* v___f_1392_; uint8_t v___x_1393_; 
v___f_1392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1376_);
v___x_1393_ = l_Lean_MessageData_hasTag(v___f_1392_, v_data_1376_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec(v_endPos_1374_);
lean_del_object(v___x_1365_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_fst_1367_);
lean_ctor_set(v___x_1394_, 1, v_snd_1368_);
v_a_1379_ = v___x_1394_;
goto v___jp_1378_;
}
else
{
if (lean_obj_tag(v_endPos_1374_) == 1)
{
lean_object* v_val_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1507_; 
v_val_1395_ = lean_ctor_get(v_endPos_1374_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_endPos_1374_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1397_ = v_endPos_1374_;
v_isShared_1398_ = v_isSharedCheck_1507_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_val_1395_);
lean_dec(v_endPos_1374_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1507_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; uint8_t v___x_1403_; 
lean_inc_ref(v_pos_1373_);
v___x_1399_ = l_Lean_FileMap_ofPosition(v___x_1349_, v_pos_1373_);
v___x_1400_ = l_Lean_FileMap_ofPosition(v___x_1349_, v_val_1395_);
lean_inc(v___x_1400_);
lean_inc(v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = 0;
v___x_1403_ = l_Lean_Syntax_Range_includes(v_val_1350_, v___x_1401_, v___x_1402_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_dec_ref_known(v___x_1401_, 2);
lean_dec(v___x_1400_);
lean_dec(v___x_1399_);
lean_del_object(v___x_1397_);
lean_del_object(v___x_1365_);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_fst_1367_);
lean_ctor_set(v___x_1404_, 1, v_snd_1368_);
v_a_1379_ = v___x_1404_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1405_; 
lean_inc(v_cmd_1351_);
lean_inc_ref(v___x_1401_);
v___x_1405_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1401_, v_cmd_1351_);
if (lean_obj_tag(v___x_1405_) == 1)
{
lean_object* v_val_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v___x_1400_);
lean_dec(v___x_1399_);
lean_del_object(v___x_1397_);
v_val_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_val_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v_fst_1407_ = lean_ctor_get(v_val_1406_, 0);
v_snd_1408_ = lean_ctor_get(v_val_1406_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_val_1406_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1410_ = v_val_1406_;
v_isShared_1411_ = v_isSharedCheck_1471_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snd_1408_);
lean_inc(v_fst_1407_);
lean_dec(v_val_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1471_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1469_; lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Syntax_getPos_x3f(v_fst_1407_, v___x_1402_);
if (lean_obj_tag(v___x_1470_) == 0)
{
v___y_1469_ = v___x_1403_;
goto v___jp_1468_;
}
else
{
lean_dec_ref_known(v___x_1470_, 1);
v___y_1469_ = v___x_1402_;
goto v___jp_1468_;
}
v___jp_1412_:
{
lean_object* v___x_1418_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_snd_1368_);
lean_ctor_set(v___x_1410_, 0, v_fst_1367_);
v___x_1418_ = v___x_1410_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_fst_1367_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_snd_1368_);
v___x_1418_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
size_t v_sz_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v_sz_1419_ = lean_array_size(v___y_1414_);
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1401_, v_fst_1407_, v_snd_1408_, v___y_1413_, v___y_1414_, v_sz_1419_, v___x_1420_, v___x_1418_);
lean_dec_ref(v___y_1414_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_fst_1423_; lean_object* v_snd_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v_fst_1423_ = lean_ctor_get(v_a_1422_, 0);
v_snd_1424_ = lean_ctor_get(v_a_1422_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_a_1422_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v_a_1422_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_snd_1424_);
lean_inc(v_fst_1423_);
lean_dec(v_a_1422_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_fst_1423_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_snd_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v_a_1379_ = v___x_1429_;
goto v___jp_1378_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_del_object(v___x_1370_);
lean_dec(v_cmd_1351_);
v_a_1432_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1421_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1421_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
v___jp_1441_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
lean_inc_ref(v___x_1401_);
v___x_1442_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1401_);
v___x_1443_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1376_);
v___x_1444_ = lean_array_get_size(v___x_1443_);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_nat_dec_eq(v___x_1444_, v___x_1445_);
if (v___x_1446_ == 0)
{
v___y_1413_ = v___x_1442_;
v___y_1414_ = v___x_1443_;
v___y_1415_ = v___y_1358_;
v___y_1416_ = v___y_1359_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_scopes_1452_; lean_object* v___x_1453_; lean_object* v_opts_1454_; uint8_t v_hasTrace_1455_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1448_ = l_Lean_inheritedTraceOptions;
v___x_1449_ = lean_st_ref_get(v___x_1448_);
v___x_1450_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1451_ = lean_st_ref_get(v___y_1359_);
v_scopes_1452_ = lean_ctor_get(v___x_1451_, 2);
lean_inc(v_scopes_1452_);
lean_dec(v___x_1451_);
v___x_1453_ = l_List_head_x21___redArg(v___x_1450_, v_scopes_1452_);
lean_dec(v_scopes_1452_);
v_opts_1454_ = lean_ctor_get(v___x_1453_, 1);
lean_inc_ref(v_opts_1454_);
lean_dec(v___x_1453_);
v_hasTrace_1455_ = lean_ctor_get_uint8(v_opts_1454_, sizeof(void*)*1);
if (v_hasTrace_1455_ == 0)
{
lean_dec_ref(v_opts_1454_);
lean_dec(v___x_1449_);
v___y_1413_ = v___x_1442_;
v___y_1414_ = v___x_1443_;
v___y_1415_ = v___y_1358_;
v___y_1416_ = v___y_1359_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1457_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1449_, v_opts_1454_, v___x_1456_);
lean_dec_ref(v_opts_1454_);
lean_dec(v___x_1449_);
if (v___x_1457_ == 0)
{
v___y_1413_ = v___x_1442_;
v___y_1414_ = v___x_1443_;
v___y_1415_ = v___y_1358_;
v___y_1416_ = v___y_1359_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1459_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1447_, v___x_1458_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_dec_ref_known(v___x_1459_, 1);
v___y_1413_ = v___x_1442_;
v___y_1414_ = v___x_1443_;
v___y_1415_ = v___y_1358_;
v___y_1416_ = v___y_1359_;
goto v___jp_1412_;
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v___x_1443_);
lean_dec(v___x_1442_);
lean_del_object(v___x_1410_);
lean_dec(v_snd_1408_);
lean_dec(v_fst_1407_);
lean_dec_ref_known(v___x_1401_, 2);
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v_fst_1367_);
lean_dec(v_cmd_1351_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
}
v___jp_1468_:
{
if (v_onUnsolved_1352_ == 0)
{
if (v___y_1353_ == 0)
{
lean_del_object(v___x_1410_);
lean_dec(v_snd_1408_);
lean_dec(v_fst_1407_);
lean_dec_ref_known(v___x_1401_, 2);
goto v___jp_1386_;
}
else
{
if (v___y_1469_ == 0)
{
lean_del_object(v___x_1410_);
lean_dec(v_snd_1408_);
lean_dec(v_fst_1407_);
lean_dec_ref_known(v___x_1401_, 2);
goto v___jp_1386_;
}
else
{
lean_del_object(v___x_1365_);
goto v___jp_1441_;
}
}
}
else
{
lean_del_object(v___x_1365_);
goto v___jp_1441_;
}
}
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_scopes_1477_; lean_object* v___x_1478_; lean_object* v_opts_1479_; uint8_t v_hasTrace_1480_; 
lean_dec(v___x_1405_);
lean_dec_ref_known(v___x_1401_, 2);
lean_del_object(v___x_1365_);
v___x_1472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1473_ = l_Lean_inheritedTraceOptions;
v___x_1474_ = lean_st_ref_get(v___x_1473_);
v___x_1475_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1476_ = lean_st_ref_get(v___y_1359_);
v_scopes_1477_ = lean_ctor_get(v___x_1476_, 2);
lean_inc(v_scopes_1477_);
lean_dec(v___x_1476_);
v___x_1478_ = l_List_head_x21___redArg(v___x_1475_, v_scopes_1477_);
lean_dec(v_scopes_1477_);
v_opts_1479_ = lean_ctor_get(v___x_1478_, 1);
lean_inc_ref(v_opts_1479_);
lean_dec(v___x_1478_);
v_hasTrace_1480_ = lean_ctor_get_uint8(v_opts_1479_, sizeof(void*)*1);
if (v_hasTrace_1480_ == 0)
{
lean_dec_ref(v_opts_1479_);
lean_dec(v___x_1474_);
lean_dec(v___x_1400_);
lean_dec(v___x_1399_);
lean_del_object(v___x_1397_);
goto v___jp_1390_;
}
else
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1482_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1474_, v_opts_1479_, v___x_1481_);
lean_dec_ref(v_opts_1479_);
lean_dec(v___x_1474_);
if (v___x_1482_ == 0)
{
lean_dec(v___x_1400_);
lean_dec(v___x_1399_);
lean_del_object(v___x_1397_);
goto v___jp_1390_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1483_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1484_ = l_Nat_reprFast(v___x_1399_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 3);
lean_ctor_set(v___x_1397_, 0, v___x_1484_);
v___x_1486_ = v___x_1397_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1487_ = l_Lean_MessageData_ofFormat(v___x_1486_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1483_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Nat_reprFast(v___x_1400_);
v___x_1492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
v___x_1493_ = l_Lean_MessageData_ofFormat(v___x_1492_);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1490_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1472_, v___x_1496_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref_known(v___x_1497_, 1);
goto v___jp_1390_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v_fst_1367_);
lean_dec(v_cmd_1351_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
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
lean_object* v___x_1508_; 
lean_dec(v_endPos_1374_);
lean_del_object(v___x_1365_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_fst_1367_);
lean_ctor_set(v___x_1508_, 1, v_snd_1368_);
v_a_1379_ = v___x_1508_;
goto v___jp_1378_;
}
}
}
else
{
lean_object* v___x_1509_; 
lean_dec(v_endPos_1374_);
lean_del_object(v___x_1365_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_fst_1367_);
lean_ctor_set(v___x_1509_, 1, v_snd_1368_);
v_a_1379_ = v___x_1509_;
goto v___jp_1378_;
}
v___jp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v_a_1379_);
lean_ctor_set(v___x_1370_, 0, v___x_1377_);
v___x_1381_ = v___x_1370_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_a_1379_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
size_t v___x_1382_; size_t v___x_1383_; 
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_add(v_i_1356_, v___x_1382_);
v_i_1356_ = v___x_1383_;
v_b_1357_ = v___x_1381_;
goto _start;
}
}
v___jp_1386_:
{
lean_object* v___x_1388_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_snd_1368_);
lean_ctor_set(v___x_1365_, 0, v_fst_1367_);
v___x_1388_ = v___x_1365_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_fst_1367_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_snd_1368_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v_a_1379_ = v___x_1388_;
goto v___jp_1378_;
}
}
v___jp_1390_:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_fst_1367_);
lean_ctor_set(v___x_1391_, 1, v_snd_1368_);
v_a_1379_ = v___x_1391_;
goto v___jp_1378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___boxed(lean_object* v___x_1513_, lean_object* v_val_1514_, lean_object* v_cmd_1515_, lean_object* v_onUnsolved_1516_, lean_object* v___y_1517_, lean_object* v_as_1518_, lean_object* v_sz_1519_, lean_object* v_i_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
uint8_t v_onUnsolved_boxed_1525_; uint8_t v___y_12275__boxed_1526_; size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_onUnsolved_boxed_1525_ = lean_unbox(v_onUnsolved_1516_);
v___y_12275__boxed_1526_ = lean_unbox(v___y_1517_);
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1519_);
lean_dec(v_sz_1519_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1520_);
lean_dec(v_i_1520_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1513_, v_val_1514_, v_cmd_1515_, v_onUnsolved_boxed_1525_, v___y_12275__boxed_1526_, v_as_1518_, v_sz_boxed_1527_, v_i_boxed_1528_, v_b_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec_ref(v_as_1518_);
lean_dec_ref(v_val_1514_);
lean_dec_ref(v___x_1513_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object* v___x_1530_, lean_object* v_val_1531_, lean_object* v_cmd_1532_, uint8_t v_onUnsolved_1533_, uint8_t v___y_1534_, lean_object* v_as_1535_, size_t v_sz_1536_, size_t v_i_1537_, lean_object* v_b_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_usize_dec_lt(v_i_1537_, v_sz_1536_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_dec(v_cmd_1532_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_b_1538_);
return v___x_1543_;
}
else
{
lean_object* v_snd_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1692_; 
v_snd_1544_ = lean_ctor_get(v_b_1538_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_b_1538_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v_b_1538_, 0);
lean_dec(v_unused_1693_);
v___x_1546_ = v_b_1538_;
v_isShared_1547_ = v_isSharedCheck_1692_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_snd_1544_);
lean_dec(v_b_1538_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1692_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_fst_1548_; lean_object* v_snd_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1691_; 
v_fst_1548_ = lean_ctor_get(v_snd_1544_, 0);
v_snd_1549_ = lean_ctor_get(v_snd_1544_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_snd_1544_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1551_ = v_snd_1544_;
v_isShared_1552_ = v_isSharedCheck_1691_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_snd_1549_);
lean_inc(v_fst_1548_);
lean_dec(v_snd_1544_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1691_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_a_1553_; lean_object* v_pos_1554_; lean_object* v_endPos_1555_; uint8_t v_severity_1556_; lean_object* v_data_1557_; lean_object* v___x_1558_; lean_object* v_a_1560_; 
v_a_1553_ = lean_array_uget_borrowed(v_as_1535_, v_i_1537_);
v_pos_1554_ = lean_ctor_get(v_a_1553_, 1);
v_endPos_1555_ = lean_ctor_get(v_a_1553_, 2);
lean_inc(v_endPos_1555_);
v_severity_1556_ = lean_ctor_get_uint8(v_a_1553_, sizeof(void*)*5 + 1);
v_data_1557_ = lean_ctor_get(v_a_1553_, 4);
v___x_1558_ = lean_box(0);
if (v_severity_1556_ == 2)
{
lean_object* v___f_1573_; uint8_t v___x_1574_; 
v___f_1573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1557_);
v___x_1574_ = l_Lean_MessageData_hasTag(v___f_1573_, v_data_1557_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_dec(v_endPos_1555_);
lean_del_object(v___x_1546_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v_fst_1548_);
lean_ctor_set(v___x_1575_, 1, v_snd_1549_);
v_a_1560_ = v___x_1575_;
goto v___jp_1559_;
}
else
{
if (lean_obj_tag(v_endPos_1555_) == 1)
{
lean_object* v_val_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1688_; 
v_val_1576_ = lean_ctor_get(v_endPos_1555_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_endPos_1555_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1578_ = v_endPos_1555_;
v_isShared_1579_ = v_isSharedCheck_1688_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_val_1576_);
lean_dec(v_endPos_1555_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1688_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; uint8_t v___x_1584_; 
lean_inc_ref(v_pos_1554_);
v___x_1580_ = l_Lean_FileMap_ofPosition(v___x_1530_, v_pos_1554_);
v___x_1581_ = l_Lean_FileMap_ofPosition(v___x_1530_, v_val_1576_);
lean_inc(v___x_1581_);
lean_inc(v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = 0;
v___x_1584_ = l_Lean_Syntax_Range_includes(v_val_1531_, v___x_1582_, v___x_1583_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref_known(v___x_1582_, 2);
lean_dec(v___x_1581_);
lean_dec(v___x_1580_);
lean_del_object(v___x_1578_);
lean_del_object(v___x_1546_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_fst_1548_);
lean_ctor_set(v___x_1585_, 1, v_snd_1549_);
v_a_1560_ = v___x_1585_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1586_; 
lean_inc(v_cmd_1532_);
lean_inc_ref(v___x_1582_);
v___x_1586_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1582_, v_cmd_1532_);
if (lean_obj_tag(v___x_1586_) == 1)
{
lean_object* v_val_1587_; lean_object* v_fst_1588_; lean_object* v_snd_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v___x_1581_);
lean_dec(v___x_1580_);
lean_del_object(v___x_1578_);
v_val_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v_fst_1588_ = lean_ctor_get(v_val_1587_, 0);
v_snd_1589_ = lean_ctor_get(v_val_1587_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_val_1587_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1591_ = v_val_1587_;
v_isShared_1592_ = v_isSharedCheck_1652_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_snd_1589_);
lean_inc(v_fst_1588_);
lean_dec(v_val_1587_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1652_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; uint8_t v___y_1650_; lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Syntax_getPos_x3f(v_fst_1588_, v___x_1583_);
if (lean_obj_tag(v___x_1651_) == 0)
{
v___y_1650_ = v___x_1584_;
goto v___jp_1649_;
}
else
{
lean_dec_ref_known(v___x_1651_, 1);
v___y_1650_ = v___x_1583_;
goto v___jp_1649_;
}
v___jp_1593_:
{
lean_object* v___x_1599_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 1, v_snd_1549_);
lean_ctor_set(v___x_1591_, 0, v_fst_1548_);
v___x_1599_ = v___x_1591_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_fst_1548_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_snd_1549_);
v___x_1599_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
size_t v_sz_1600_; size_t v___x_1601_; lean_object* v___x_1602_; 
v_sz_1600_ = lean_array_size(v___y_1594_);
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1582_, v_fst_1588_, v_snd_1589_, v___y_1595_, v___y_1594_, v_sz_1600_, v___x_1601_, v___x_1599_);
lean_dec_ref(v___y_1594_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v_fst_1604_; lean_object* v_snd_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1602_, 1);
v_fst_1604_ = lean_ctor_get(v_a_1603_, 0);
v_snd_1605_ = lean_ctor_get(v_a_1603_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_a_1603_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v_a_1603_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_snd_1605_);
lean_inc(v_fst_1604_);
lean_dec(v_a_1603_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_fst_1604_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_snd_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
v_a_1560_ = v___x_1610_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_del_object(v___x_1551_);
lean_dec(v_cmd_1532_);
v_a_1613_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1602_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1602_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
v___jp_1622_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
lean_inc_ref(v___x_1582_);
v___x_1623_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1582_);
v___x_1624_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1557_);
v___x_1625_ = lean_array_get_size(v___x_1624_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_nat_dec_eq(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
v___y_1594_ = v___x_1624_;
v___y_1595_ = v___x_1623_;
v___y_1596_ = v___y_1539_;
v___y_1597_ = v___y_1540_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_scopes_1633_; lean_object* v___x_1634_; lean_object* v_opts_1635_; uint8_t v_hasTrace_1636_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1629_ = l_Lean_inheritedTraceOptions;
v___x_1630_ = lean_st_ref_get(v___x_1629_);
v___x_1631_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1632_ = lean_st_ref_get(v___y_1540_);
v_scopes_1633_ = lean_ctor_get(v___x_1632_, 2);
lean_inc(v_scopes_1633_);
lean_dec(v___x_1632_);
v___x_1634_ = l_List_head_x21___redArg(v___x_1631_, v_scopes_1633_);
lean_dec(v_scopes_1633_);
v_opts_1635_ = lean_ctor_get(v___x_1634_, 1);
lean_inc_ref(v_opts_1635_);
lean_dec(v___x_1634_);
v_hasTrace_1636_ = lean_ctor_get_uint8(v_opts_1635_, sizeof(void*)*1);
if (v_hasTrace_1636_ == 0)
{
lean_dec_ref(v_opts_1635_);
lean_dec(v___x_1630_);
v___y_1594_ = v___x_1624_;
v___y_1595_ = v___x_1623_;
v___y_1596_ = v___y_1539_;
v___y_1597_ = v___y_1540_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1638_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1630_, v_opts_1635_, v___x_1637_);
lean_dec_ref(v_opts_1635_);
lean_dec(v___x_1630_);
if (v___x_1638_ == 0)
{
v___y_1594_ = v___x_1624_;
v___y_1595_ = v___x_1623_;
v___y_1596_ = v___y_1539_;
v___y_1597_ = v___y_1540_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1640_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1628_, v___x_1639_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_dec_ref_known(v___x_1640_, 1);
v___y_1594_ = v___x_1624_;
v___y_1595_ = v___x_1623_;
v___y_1596_ = v___y_1539_;
v___y_1597_ = v___y_1540_;
goto v___jp_1593_;
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___x_1624_);
lean_dec(v___x_1623_);
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_dec_ref_known(v___x_1582_, 2);
lean_del_object(v___x_1551_);
lean_dec(v_snd_1549_);
lean_dec(v_fst_1548_);
lean_dec(v_cmd_1532_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
}
v___jp_1649_:
{
if (v_onUnsolved_1533_ == 0)
{
if (v___y_1534_ == 0)
{
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_dec_ref_known(v___x_1582_, 2);
goto v___jp_1567_;
}
else
{
if (v___y_1650_ == 0)
{
lean_del_object(v___x_1591_);
lean_dec(v_snd_1589_);
lean_dec(v_fst_1588_);
lean_dec_ref_known(v___x_1582_, 2);
goto v___jp_1567_;
}
else
{
lean_del_object(v___x_1546_);
goto v___jp_1622_;
}
}
}
else
{
lean_del_object(v___x_1546_);
goto v___jp_1622_;
}
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v_scopes_1658_; lean_object* v___x_1659_; lean_object* v_opts_1660_; uint8_t v_hasTrace_1661_; 
lean_dec(v___x_1586_);
lean_dec_ref_known(v___x_1582_, 2);
lean_del_object(v___x_1546_);
v___x_1653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1654_ = l_Lean_inheritedTraceOptions;
v___x_1655_ = lean_st_ref_get(v___x_1654_);
v___x_1656_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1657_ = lean_st_ref_get(v___y_1540_);
v_scopes_1658_ = lean_ctor_get(v___x_1657_, 2);
lean_inc(v_scopes_1658_);
lean_dec(v___x_1657_);
v___x_1659_ = l_List_head_x21___redArg(v___x_1656_, v_scopes_1658_);
lean_dec(v_scopes_1658_);
v_opts_1660_ = lean_ctor_get(v___x_1659_, 1);
lean_inc_ref(v_opts_1660_);
lean_dec(v___x_1659_);
v_hasTrace_1661_ = lean_ctor_get_uint8(v_opts_1660_, sizeof(void*)*1);
if (v_hasTrace_1661_ == 0)
{
lean_dec_ref(v_opts_1660_);
lean_dec(v___x_1655_);
lean_dec(v___x_1581_);
lean_dec(v___x_1580_);
lean_del_object(v___x_1578_);
goto v___jp_1571_;
}
else
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1655_, v_opts_1660_, v___x_1662_);
lean_dec_ref(v_opts_1660_);
lean_dec(v___x_1655_);
if (v___x_1663_ == 0)
{
lean_dec(v___x_1581_);
lean_dec(v___x_1580_);
lean_del_object(v___x_1578_);
goto v___jp_1571_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1665_ = l_Nat_reprFast(v___x_1580_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 3);
lean_ctor_set(v___x_1578_, 0, v___x_1665_);
v___x_1667_ = v___x_1578_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1668_ = l_Lean_MessageData_ofFormat(v___x_1667_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1664_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Nat_reprFast(v___x_1581_);
v___x_1673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
v___x_1674_ = l_Lean_MessageData_ofFormat(v___x_1673_);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1671_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1653_, v___x_1677_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_dec_ref_known(v___x_1678_, 1);
goto v___jp_1571_;
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_del_object(v___x_1551_);
lean_dec(v_snd_1549_);
lean_dec(v_fst_1548_);
lean_dec(v_cmd_1532_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
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
lean_object* v___x_1689_; 
lean_dec(v_endPos_1555_);
lean_del_object(v___x_1546_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_fst_1548_);
lean_ctor_set(v___x_1689_, 1, v_snd_1549_);
v_a_1560_ = v___x_1689_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v___x_1690_; 
lean_dec(v_endPos_1555_);
lean_del_object(v___x_1546_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_fst_1548_);
lean_ctor_set(v___x_1690_, 1, v_snd_1549_);
v_a_1560_ = v___x_1690_;
goto v___jp_1559_;
}
v___jp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v_a_1560_);
lean_ctor_set(v___x_1551_, 0, v___x_1558_);
v___x_1562_ = v___x_1551_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_a_1560_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = ((size_t)1ULL);
v___x_1564_ = lean_usize_add(v_i_1537_, v___x_1563_);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1530_, v_val_1531_, v_cmd_1532_, v_onUnsolved_1533_, v___y_1534_, v_as_1535_, v_sz_1536_, v___x_1564_, v___x_1562_, v___y_1539_, v___y_1540_);
return v___x_1565_;
}
}
v___jp_1567_:
{
lean_object* v___x_1569_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 1, v_snd_1549_);
lean_ctor_set(v___x_1546_, 0, v_fst_1548_);
v___x_1569_ = v___x_1546_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_fst_1548_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_snd_1549_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
v_a_1560_ = v___x_1569_;
goto v___jp_1559_;
}
}
v___jp_1571_:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_fst_1548_);
lean_ctor_set(v___x_1572_, 1, v_snd_1549_);
v_a_1560_ = v___x_1572_;
goto v___jp_1559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object* v___x_1694_, lean_object* v_val_1695_, lean_object* v_cmd_1696_, lean_object* v_onUnsolved_1697_, lean_object* v___y_1698_, lean_object* v_as_1699_, lean_object* v_sz_1700_, lean_object* v_i_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v_onUnsolved_boxed_1706_; uint8_t v___y_12616__boxed_1707_; size_t v_sz_boxed_1708_; size_t v_i_boxed_1709_; lean_object* v_res_1710_; 
v_onUnsolved_boxed_1706_ = lean_unbox(v_onUnsolved_1697_);
v___y_12616__boxed_1707_ = lean_unbox(v___y_1698_);
v_sz_boxed_1708_ = lean_unbox_usize(v_sz_1700_);
lean_dec(v_sz_1700_);
v_i_boxed_1709_ = lean_unbox_usize(v_i_1701_);
lean_dec(v_i_1701_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_1694_, v_val_1695_, v_cmd_1696_, v_onUnsolved_boxed_1706_, v___y_12616__boxed_1707_, v_as_1699_, v_sz_boxed_1708_, v_i_boxed_1709_, v_b_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v_as_1699_);
lean_dec_ref(v_val_1695_);
lean_dec_ref(v___x_1694_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(lean_object* v___x_1711_, lean_object* v_val_1712_, lean_object* v_cmd_1713_, uint8_t v_onUnsolved_1714_, uint8_t v___y_1715_, lean_object* v_as_1716_, size_t v_sz_1717_, size_t v_i_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_lt(v_i_1718_, v_sz_1717_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_dec(v_cmd_1713_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_b_1719_);
return v___x_1724_;
}
else
{
lean_object* v_snd_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1873_; 
v_snd_1725_ = lean_ctor_get(v_b_1719_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_b_1719_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_b_1719_, 0);
lean_dec(v_unused_1874_);
v___x_1727_ = v_b_1719_;
v_isShared_1728_ = v_isSharedCheck_1873_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snd_1725_);
lean_dec(v_b_1719_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1873_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_fst_1729_; lean_object* v_snd_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1872_; 
v_fst_1729_ = lean_ctor_get(v_snd_1725_, 0);
v_snd_1730_ = lean_ctor_get(v_snd_1725_, 1);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_snd_1725_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1732_ = v_snd_1725_;
v_isShared_1733_ = v_isSharedCheck_1872_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_snd_1730_);
lean_inc(v_fst_1729_);
lean_dec(v_snd_1725_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1872_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_a_1734_; lean_object* v_pos_1735_; lean_object* v_endPos_1736_; uint8_t v_severity_1737_; lean_object* v_data_1738_; lean_object* v___x_1739_; lean_object* v_a_1741_; 
v_a_1734_ = lean_array_uget_borrowed(v_as_1716_, v_i_1718_);
v_pos_1735_ = lean_ctor_get(v_a_1734_, 1);
v_endPos_1736_ = lean_ctor_get(v_a_1734_, 2);
lean_inc(v_endPos_1736_);
v_severity_1737_ = lean_ctor_get_uint8(v_a_1734_, sizeof(void*)*5 + 1);
v_data_1738_ = lean_ctor_get(v_a_1734_, 4);
v___x_1739_ = lean_box(0);
if (v_severity_1737_ == 2)
{
lean_object* v___f_1754_; uint8_t v___x_1755_; 
v___f_1754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1738_);
v___x_1755_ = l_Lean_MessageData_hasTag(v___f_1754_, v_data_1738_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_dec(v_endPos_1736_);
lean_del_object(v___x_1727_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_fst_1729_);
lean_ctor_set(v___x_1756_, 1, v_snd_1730_);
v_a_1741_ = v___x_1756_;
goto v___jp_1740_;
}
else
{
if (lean_obj_tag(v_endPos_1736_) == 1)
{
lean_object* v_val_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1869_; 
v_val_1757_ = lean_ctor_get(v_endPos_1736_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_endPos_1736_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1759_ = v_endPos_1736_;
v_isShared_1760_ = v_isSharedCheck_1869_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_val_1757_);
lean_dec(v_endPos_1736_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1869_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; uint8_t v___x_1765_; 
lean_inc_ref(v_pos_1735_);
v___x_1761_ = l_Lean_FileMap_ofPosition(v___x_1711_, v_pos_1735_);
v___x_1762_ = l_Lean_FileMap_ofPosition(v___x_1711_, v_val_1757_);
lean_inc(v___x_1762_);
lean_inc(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = 0;
v___x_1765_ = l_Lean_Syntax_Range_includes(v_val_1712_, v___x_1763_, v___x_1764_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
lean_dec_ref_known(v___x_1763_, 2);
lean_dec(v___x_1762_);
lean_dec(v___x_1761_);
lean_del_object(v___x_1759_);
lean_del_object(v___x_1727_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_fst_1729_);
lean_ctor_set(v___x_1766_, 1, v_snd_1730_);
v_a_1741_ = v___x_1766_;
goto v___jp_1740_;
}
else
{
lean_object* v___x_1767_; 
lean_inc(v_cmd_1713_);
lean_inc_ref(v___x_1763_);
v___x_1767_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1763_, v_cmd_1713_);
if (lean_obj_tag(v___x_1767_) == 1)
{
lean_object* v_val_1768_; lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v___x_1762_);
lean_dec(v___x_1761_);
lean_del_object(v___x_1759_);
v_val_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_val_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v_fst_1769_ = lean_ctor_get(v_val_1768_, 0);
v_snd_1770_ = lean_ctor_get(v_val_1768_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_val_1768_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1772_ = v_val_1768_;
v_isShared_1773_ = v_isSharedCheck_1833_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_snd_1770_);
lean_inc(v_fst_1769_);
lean_dec(v_val_1768_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1833_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; uint8_t v___y_1831_; lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Syntax_getPos_x3f(v_fst_1769_, v___x_1764_);
if (lean_obj_tag(v___x_1832_) == 0)
{
v___y_1831_ = v___x_1765_;
goto v___jp_1830_;
}
else
{
lean_dec_ref_known(v___x_1832_, 1);
v___y_1831_ = v___x_1764_;
goto v___jp_1830_;
}
v___jp_1774_:
{
lean_object* v___x_1780_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_snd_1730_);
lean_ctor_set(v___x_1772_, 0, v_fst_1729_);
v___x_1780_ = v___x_1772_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_fst_1729_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_snd_1730_);
v___x_1780_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
size_t v_sz_1781_; size_t v___x_1782_; lean_object* v___x_1783_; 
v_sz_1781_ = lean_array_size(v___y_1775_);
v___x_1782_ = ((size_t)0ULL);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1763_, v_fst_1769_, v_snd_1770_, v___y_1776_, v___y_1775_, v_sz_1781_, v___x_1782_, v___x_1780_);
lean_dec_ref(v___y_1775_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v_fst_1785_ = lean_ctor_get(v_a_1784_, 0);
v_snd_1786_ = lean_ctor_get(v_a_1784_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_a_1784_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v_a_1784_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_snd_1786_);
lean_inc(v_fst_1785_);
lean_dec(v_a_1784_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_fst_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_snd_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
v_a_1741_ = v___x_1791_;
goto v___jp_1740_;
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_del_object(v___x_1732_);
lean_dec(v_cmd_1713_);
v_a_1794_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1783_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1783_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
v___jp_1803_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_inc_ref(v___x_1763_);
v___x_1804_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1763_);
v___x_1805_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1738_);
v___x_1806_ = lean_array_get_size(v___x_1805_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_nat_dec_eq(v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
v___y_1775_ = v___x_1805_;
v___y_1776_ = v___x_1804_;
v___y_1777_ = v___y_1720_;
v___y_1778_ = v___y_1721_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_scopes_1814_; lean_object* v___x_1815_; lean_object* v_opts_1816_; uint8_t v_hasTrace_1817_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1810_ = l_Lean_inheritedTraceOptions;
v___x_1811_ = lean_st_ref_get(v___x_1810_);
v___x_1812_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1813_ = lean_st_ref_get(v___y_1721_);
v_scopes_1814_ = lean_ctor_get(v___x_1813_, 2);
lean_inc(v_scopes_1814_);
lean_dec(v___x_1813_);
v___x_1815_ = l_List_head_x21___redArg(v___x_1812_, v_scopes_1814_);
lean_dec(v_scopes_1814_);
v_opts_1816_ = lean_ctor_get(v___x_1815_, 1);
lean_inc_ref(v_opts_1816_);
lean_dec(v___x_1815_);
v_hasTrace_1817_ = lean_ctor_get_uint8(v_opts_1816_, sizeof(void*)*1);
if (v_hasTrace_1817_ == 0)
{
lean_dec_ref(v_opts_1816_);
lean_dec(v___x_1811_);
v___y_1775_ = v___x_1805_;
v___y_1776_ = v___x_1804_;
v___y_1777_ = v___y_1720_;
v___y_1778_ = v___y_1721_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1819_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1811_, v_opts_1816_, v___x_1818_);
lean_dec_ref(v_opts_1816_);
lean_dec(v___x_1811_);
if (v___x_1819_ == 0)
{
v___y_1775_ = v___x_1805_;
v___y_1776_ = v___x_1804_;
v___y_1777_ = v___y_1720_;
v___y_1778_ = v___y_1721_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1821_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1809_, v___x_1820_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_dec_ref_known(v___x_1821_, 1);
v___y_1775_ = v___x_1805_;
v___y_1776_ = v___x_1804_;
v___y_1777_ = v___y_1720_;
v___y_1778_ = v___y_1721_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v___x_1805_);
lean_dec(v___x_1804_);
lean_del_object(v___x_1772_);
lean_dec(v_snd_1770_);
lean_dec(v_fst_1769_);
lean_dec_ref_known(v___x_1763_, 2);
lean_del_object(v___x_1732_);
lean_dec(v_snd_1730_);
lean_dec(v_fst_1729_);
lean_dec(v_cmd_1713_);
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
}
}
v___jp_1830_:
{
if (v_onUnsolved_1714_ == 0)
{
if (v___y_1715_ == 0)
{
lean_del_object(v___x_1772_);
lean_dec(v_snd_1770_);
lean_dec(v_fst_1769_);
lean_dec_ref_known(v___x_1763_, 2);
goto v___jp_1748_;
}
else
{
if (v___y_1831_ == 0)
{
lean_del_object(v___x_1772_);
lean_dec(v_snd_1770_);
lean_dec(v_fst_1769_);
lean_dec_ref_known(v___x_1763_, 2);
goto v___jp_1748_;
}
else
{
lean_del_object(v___x_1727_);
goto v___jp_1803_;
}
}
}
else
{
lean_del_object(v___x_1727_);
goto v___jp_1803_;
}
}
}
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v_scopes_1839_; lean_object* v___x_1840_; lean_object* v_opts_1841_; uint8_t v_hasTrace_1842_; 
lean_dec(v___x_1767_);
lean_dec_ref_known(v___x_1763_, 2);
lean_del_object(v___x_1727_);
v___x_1834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1835_ = l_Lean_inheritedTraceOptions;
v___x_1836_ = lean_st_ref_get(v___x_1835_);
v___x_1837_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1838_ = lean_st_ref_get(v___y_1721_);
v_scopes_1839_ = lean_ctor_get(v___x_1838_, 2);
lean_inc(v_scopes_1839_);
lean_dec(v___x_1838_);
v___x_1840_ = l_List_head_x21___redArg(v___x_1837_, v_scopes_1839_);
lean_dec(v_scopes_1839_);
v_opts_1841_ = lean_ctor_get(v___x_1840_, 1);
lean_inc_ref(v_opts_1841_);
lean_dec(v___x_1840_);
v_hasTrace_1842_ = lean_ctor_get_uint8(v_opts_1841_, sizeof(void*)*1);
if (v_hasTrace_1842_ == 0)
{
lean_dec_ref(v_opts_1841_);
lean_dec(v___x_1836_);
lean_dec(v___x_1762_);
lean_dec(v___x_1761_);
lean_del_object(v___x_1759_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1844_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1836_, v_opts_1841_, v___x_1843_);
lean_dec_ref(v_opts_1841_);
lean_dec(v___x_1836_);
if (v___x_1844_ == 0)
{
lean_dec(v___x_1762_);
lean_dec(v___x_1761_);
lean_del_object(v___x_1759_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1846_ = l_Nat_reprFast(v___x_1761_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 3);
lean_ctor_set(v___x_1759_, 0, v___x_1846_);
v___x_1848_ = v___x_1759_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1849_ = l_Lean_MessageData_ofFormat(v___x_1848_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1845_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Nat_reprFast(v___x_1762_);
v___x_1854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
v___x_1855_ = l_Lean_MessageData_ofFormat(v___x_1854_);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1852_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1834_, v___x_1858_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_dec_ref_known(v___x_1859_, 1);
goto v___jp_1752_;
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1732_);
lean_dec(v_snd_1730_);
lean_dec(v_fst_1729_);
lean_dec(v_cmd_1713_);
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
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
lean_object* v___x_1870_; 
lean_dec(v_endPos_1736_);
lean_del_object(v___x_1727_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_fst_1729_);
lean_ctor_set(v___x_1870_, 1, v_snd_1730_);
v_a_1741_ = v___x_1870_;
goto v___jp_1740_;
}
}
}
else
{
lean_object* v___x_1871_; 
lean_dec(v_endPos_1736_);
lean_del_object(v___x_1727_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_fst_1729_);
lean_ctor_set(v___x_1871_, 1, v_snd_1730_);
v_a_1741_ = v___x_1871_;
goto v___jp_1740_;
}
v___jp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v_a_1741_);
lean_ctor_set(v___x_1732_, 0, v___x_1739_);
v___x_1743_ = v___x_1732_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_a_1741_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
size_t v___x_1744_; size_t v___x_1745_; 
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1718_, v___x_1744_);
v_i_1718_ = v___x_1745_;
v_b_1719_ = v___x_1743_;
goto _start;
}
}
v___jp_1748_:
{
lean_object* v___x_1750_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v_snd_1730_);
lean_ctor_set(v___x_1727_, 0, v_fst_1729_);
v___x_1750_ = v___x_1727_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_fst_1729_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_snd_1730_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
v_a_1741_ = v___x_1750_;
goto v___jp_1740_;
}
}
v___jp_1752_:
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_fst_1729_);
lean_ctor_set(v___x_1753_, 1, v_snd_1730_);
v_a_1741_ = v___x_1753_;
goto v___jp_1740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v___x_1875_, lean_object* v_val_1876_, lean_object* v_cmd_1877_, lean_object* v_onUnsolved_1878_, lean_object* v___y_1879_, lean_object* v_as_1880_, lean_object* v_sz_1881_, lean_object* v_i_1882_, lean_object* v_b_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
uint8_t v_onUnsolved_boxed_1887_; uint8_t v___y_12948__boxed_1888_; size_t v_sz_boxed_1889_; size_t v_i_boxed_1890_; lean_object* v_res_1891_; 
v_onUnsolved_boxed_1887_ = lean_unbox(v_onUnsolved_1878_);
v___y_12948__boxed_1888_ = lean_unbox(v___y_1879_);
v_sz_boxed_1889_ = lean_unbox_usize(v_sz_1881_);
lean_dec(v_sz_1881_);
v_i_boxed_1890_ = lean_unbox_usize(v_i_1882_);
lean_dec(v_i_1882_);
v_res_1891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1875_, v_val_1876_, v_cmd_1877_, v_onUnsolved_boxed_1887_, v___y_12948__boxed_1888_, v_as_1880_, v_sz_boxed_1889_, v_i_boxed_1890_, v_b_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec_ref(v_as_1880_);
lean_dec_ref(v_val_1876_);
lean_dec_ref(v___x_1875_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(lean_object* v___x_1892_, lean_object* v_val_1893_, lean_object* v_cmd_1894_, uint8_t v_onUnsolved_1895_, uint8_t v___y_1896_, lean_object* v_as_1897_, size_t v_sz_1898_, size_t v_i_1899_, lean_object* v_b_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_usize_dec_lt(v_i_1899_, v_sz_1898_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; 
lean_dec(v_cmd_1894_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_b_1900_);
return v___x_1905_;
}
else
{
lean_object* v_snd_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_2054_; 
v_snd_1906_ = lean_ctor_get(v_b_1900_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_b_1900_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v_b_1900_, 0);
lean_dec(v_unused_2055_);
v___x_1908_ = v_b_1900_;
v_isShared_1909_ = v_isSharedCheck_2054_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_snd_1906_);
lean_dec(v_b_1900_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_2054_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_fst_1910_; lean_object* v_snd_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_2053_; 
v_fst_1910_ = lean_ctor_get(v_snd_1906_, 0);
v_snd_1911_ = lean_ctor_get(v_snd_1906_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_snd_1906_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_1913_ = v_snd_1906_;
v_isShared_1914_ = v_isSharedCheck_2053_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_snd_1911_);
lean_inc(v_fst_1910_);
lean_dec(v_snd_1906_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_2053_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_a_1915_; lean_object* v_pos_1916_; lean_object* v_endPos_1917_; uint8_t v_severity_1918_; lean_object* v_data_1919_; lean_object* v___x_1920_; lean_object* v_a_1922_; 
v_a_1915_ = lean_array_uget_borrowed(v_as_1897_, v_i_1899_);
v_pos_1916_ = lean_ctor_get(v_a_1915_, 1);
v_endPos_1917_ = lean_ctor_get(v_a_1915_, 2);
lean_inc(v_endPos_1917_);
v_severity_1918_ = lean_ctor_get_uint8(v_a_1915_, sizeof(void*)*5 + 1);
v_data_1919_ = lean_ctor_get(v_a_1915_, 4);
v___x_1920_ = lean_box(0);
if (v_severity_1918_ == 2)
{
lean_object* v___f_1935_; uint8_t v___x_1936_; 
v___f_1935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1919_);
v___x_1936_ = l_Lean_MessageData_hasTag(v___f_1935_, v_data_1919_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
lean_dec(v_endPos_1917_);
lean_del_object(v___x_1908_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_fst_1910_);
lean_ctor_set(v___x_1937_, 1, v_snd_1911_);
v_a_1922_ = v___x_1937_;
goto v___jp_1921_;
}
else
{
if (lean_obj_tag(v_endPos_1917_) == 1)
{
lean_object* v_val_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_2050_; 
v_val_1938_ = lean_ctor_get(v_endPos_1917_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_endPos_1917_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_1940_ = v_endPos_1917_;
v_isShared_1941_ = v_isSharedCheck_2050_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_val_1938_);
lean_dec(v_endPos_1917_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_2050_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; uint8_t v___x_1946_; 
lean_inc_ref(v_pos_1916_);
v___x_1942_ = l_Lean_FileMap_ofPosition(v___x_1892_, v_pos_1916_);
v___x_1943_ = l_Lean_FileMap_ofPosition(v___x_1892_, v_val_1938_);
lean_inc(v___x_1943_);
lean_inc(v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = 0;
v___x_1946_ = l_Lean_Syntax_Range_includes(v_val_1893_, v___x_1944_, v___x_1945_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; 
lean_dec_ref_known(v___x_1944_, 2);
lean_dec(v___x_1943_);
lean_dec(v___x_1942_);
lean_del_object(v___x_1940_);
lean_del_object(v___x_1908_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v_fst_1910_);
lean_ctor_set(v___x_1947_, 1, v_snd_1911_);
v_a_1922_ = v___x_1947_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1948_; 
lean_inc(v_cmd_1894_);
lean_inc_ref(v___x_1944_);
v___x_1948_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1944_, v_cmd_1894_);
if (lean_obj_tag(v___x_1948_) == 1)
{
lean_object* v_val_1949_; lean_object* v_fst_1950_; lean_object* v_snd_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v___x_1943_);
lean_dec(v___x_1942_);
lean_del_object(v___x_1940_);
v_val_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_val_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v_fst_1950_ = lean_ctor_get(v_val_1949_, 0);
v_snd_1951_ = lean_ctor_get(v_val_1949_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_val_1949_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1953_ = v_val_1949_;
v_isShared_1954_ = v_isSharedCheck_2014_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_snd_1951_);
lean_inc(v_fst_1950_);
lean_dec(v_val_1949_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_2014_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; uint8_t v___y_2012_; lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_Syntax_getPos_x3f(v_fst_1950_, v___x_1945_);
if (lean_obj_tag(v___x_2013_) == 0)
{
v___y_2012_ = v___x_1946_;
goto v___jp_2011_;
}
else
{
lean_dec_ref_known(v___x_2013_, 1);
v___y_2012_ = v___x_1945_;
goto v___jp_2011_;
}
v___jp_1955_:
{
lean_object* v___x_1961_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 1, v_snd_1911_);
lean_ctor_set(v___x_1953_, 0, v_fst_1910_);
v___x_1961_ = v___x_1953_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_fst_1910_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_snd_1911_);
v___x_1961_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
size_t v_sz_1962_; size_t v___x_1963_; lean_object* v___x_1964_; 
v_sz_1962_ = lean_array_size(v___y_1957_);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1944_, v_fst_1950_, v_snd_1951_, v___y_1956_, v___y_1957_, v_sz_1962_, v___x_1963_, v___x_1961_);
lean_dec_ref(v___y_1957_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v_fst_1966_ = lean_ctor_get(v_a_1965_, 0);
v_snd_1967_ = lean_ctor_get(v_a_1965_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_a_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v_a_1965_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_snd_1967_);
lean_inc(v_fst_1966_);
lean_dec(v_a_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_fst_1966_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_snd_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v_a_1922_ = v___x_1972_;
goto v___jp_1921_;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_del_object(v___x_1913_);
lean_dec(v_cmd_1894_);
v_a_1975_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1964_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1964_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
lean_inc_ref(v___x_1944_);
v___x_1985_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1944_);
v___x_1986_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1919_);
v___x_1987_ = lean_array_get_size(v___x_1986_);
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = lean_nat_dec_eq(v___x_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
v___y_1956_ = v___x_1985_;
v___y_1957_ = v___x_1986_;
v___y_1958_ = v___y_1901_;
v___y_1959_ = v___y_1902_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v_scopes_1995_; lean_object* v___x_1996_; lean_object* v_opts_1997_; uint8_t v_hasTrace_1998_; 
v___x_1990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1991_ = l_Lean_inheritedTraceOptions;
v___x_1992_ = lean_st_ref_get(v___x_1991_);
v___x_1993_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1994_ = lean_st_ref_get(v___y_1902_);
v_scopes_1995_ = lean_ctor_get(v___x_1994_, 2);
lean_inc(v_scopes_1995_);
lean_dec(v___x_1994_);
v___x_1996_ = l_List_head_x21___redArg(v___x_1993_, v_scopes_1995_);
lean_dec(v_scopes_1995_);
v_opts_1997_ = lean_ctor_get(v___x_1996_, 1);
lean_inc_ref(v_opts_1997_);
lean_dec(v___x_1996_);
v_hasTrace_1998_ = lean_ctor_get_uint8(v_opts_1997_, sizeof(void*)*1);
if (v_hasTrace_1998_ == 0)
{
lean_dec_ref(v_opts_1997_);
lean_dec(v___x_1992_);
v___y_1956_ = v___x_1985_;
v___y_1957_ = v___x_1986_;
v___y_1958_ = v___y_1901_;
v___y_1959_ = v___y_1902_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2000_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1992_, v_opts_1997_, v___x_1999_);
lean_dec_ref(v_opts_1997_);
lean_dec(v___x_1992_);
if (v___x_2000_ == 0)
{
v___y_1956_ = v___x_1985_;
v___y_1957_ = v___x_1986_;
v___y_1958_ = v___y_1901_;
v___y_1959_ = v___y_1902_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_2002_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1990_, v___x_2001_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_dec_ref_known(v___x_2002_, 1);
v___y_1956_ = v___x_1985_;
v___y_1957_ = v___x_1986_;
v___y_1958_ = v___y_1901_;
v___y_1959_ = v___y_1902_;
goto v___jp_1955_;
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v___x_1986_);
lean_dec(v___x_1985_);
lean_del_object(v___x_1953_);
lean_dec(v_snd_1951_);
lean_dec(v_fst_1950_);
lean_dec_ref_known(v___x_1944_, 2);
lean_del_object(v___x_1913_);
lean_dec(v_snd_1911_);
lean_dec(v_fst_1910_);
lean_dec(v_cmd_1894_);
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
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
}
}
}
v___jp_2011_:
{
if (v_onUnsolved_1895_ == 0)
{
if (v___y_1896_ == 0)
{
lean_del_object(v___x_1953_);
lean_dec(v_snd_1951_);
lean_dec(v_fst_1950_);
lean_dec_ref_known(v___x_1944_, 2);
goto v___jp_1929_;
}
else
{
if (v___y_2012_ == 0)
{
lean_del_object(v___x_1953_);
lean_dec(v_snd_1951_);
lean_dec(v_fst_1950_);
lean_dec_ref_known(v___x_1944_, 2);
goto v___jp_1929_;
}
else
{
lean_del_object(v___x_1908_);
goto v___jp_1984_;
}
}
}
else
{
lean_del_object(v___x_1908_);
goto v___jp_1984_;
}
}
}
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v_scopes_2020_; lean_object* v___x_2021_; lean_object* v_opts_2022_; uint8_t v_hasTrace_2023_; 
lean_dec(v___x_1948_);
lean_dec_ref_known(v___x_1944_, 2);
lean_del_object(v___x_1908_);
v___x_2015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2016_ = l_Lean_inheritedTraceOptions;
v___x_2017_ = lean_st_ref_get(v___x_2016_);
v___x_2018_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2019_ = lean_st_ref_get(v___y_1902_);
v_scopes_2020_ = lean_ctor_get(v___x_2019_, 2);
lean_inc(v_scopes_2020_);
lean_dec(v___x_2019_);
v___x_2021_ = l_List_head_x21___redArg(v___x_2018_, v_scopes_2020_);
lean_dec(v_scopes_2020_);
v_opts_2022_ = lean_ctor_get(v___x_2021_, 1);
lean_inc_ref(v_opts_2022_);
lean_dec(v___x_2021_);
v_hasTrace_2023_ = lean_ctor_get_uint8(v_opts_2022_, sizeof(void*)*1);
if (v_hasTrace_2023_ == 0)
{
lean_dec_ref(v_opts_2022_);
lean_dec(v___x_2017_);
lean_dec(v___x_1943_);
lean_dec(v___x_1942_);
lean_del_object(v___x_1940_);
goto v___jp_1933_;
}
else
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2025_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2017_, v_opts_2022_, v___x_2024_);
lean_dec_ref(v_opts_2022_);
lean_dec(v___x_2017_);
if (v___x_2025_ == 0)
{
lean_dec(v___x_1943_);
lean_dec(v___x_1942_);
lean_del_object(v___x_1940_);
goto v___jp_1933_;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2026_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_2027_ = l_Nat_reprFast(v___x_1942_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 3);
lean_ctor_set(v___x_1940_, 0, v___x_2027_);
v___x_2029_ = v___x_1940_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2030_ = l_Lean_MessageData_ofFormat(v___x_2029_);
v___x_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2026_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = l_Nat_reprFast(v___x_1943_);
v___x_2035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
v___x_2036_ = l_Lean_MessageData_ofFormat(v___x_2035_);
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2033_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2015_, v___x_2039_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_dec_ref_known(v___x_2040_, 1);
goto v___jp_1933_;
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_del_object(v___x_1913_);
lean_dec(v_snd_1911_);
lean_dec(v_fst_1910_);
lean_dec(v_cmd_1894_);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
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
lean_object* v___x_2051_; 
lean_dec(v_endPos_1917_);
lean_del_object(v___x_1908_);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_fst_1910_);
lean_ctor_set(v___x_2051_, 1, v_snd_1911_);
v_a_1922_ = v___x_2051_;
goto v___jp_1921_;
}
}
}
else
{
lean_object* v___x_2052_; 
lean_dec(v_endPos_1917_);
lean_del_object(v___x_1908_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v_fst_1910_);
lean_ctor_set(v___x_2052_, 1, v_snd_1911_);
v_a_1922_ = v___x_2052_;
goto v___jp_1921_;
}
v___jp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v_a_1922_);
lean_ctor_set(v___x_1913_, 0, v___x_1920_);
v___x_1924_ = v___x_1913_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_a_1922_);
v___x_1924_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_add(v_i_1899_, v___x_1925_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1892_, v_val_1893_, v_cmd_1894_, v_onUnsolved_1895_, v___y_1896_, v_as_1897_, v_sz_1898_, v___x_1926_, v___x_1924_, v___y_1901_, v___y_1902_);
return v___x_1927_;
}
}
v___jp_1929_:
{
lean_object* v___x_1931_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 1, v_snd_1911_);
lean_ctor_set(v___x_1908_, 0, v_fst_1910_);
v___x_1931_ = v___x_1908_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_fst_1910_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_snd_1911_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
v_a_1922_ = v___x_1931_;
goto v___jp_1921_;
}
}
v___jp_1933_:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_fst_1910_);
lean_ctor_set(v___x_1934_, 1, v_snd_1911_);
v_a_1922_ = v___x_1934_;
goto v___jp_1921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11___boxed(lean_object* v___x_2056_, lean_object* v_val_2057_, lean_object* v_cmd_2058_, lean_object* v_onUnsolved_2059_, lean_object* v___y_2060_, lean_object* v_as_2061_, lean_object* v_sz_2062_, lean_object* v_i_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
uint8_t v_onUnsolved_boxed_2068_; uint8_t v___y_13280__boxed_2069_; size_t v_sz_boxed_2070_; size_t v_i_boxed_2071_; lean_object* v_res_2072_; 
v_onUnsolved_boxed_2068_ = lean_unbox(v_onUnsolved_2059_);
v___y_13280__boxed_2069_ = lean_unbox(v___y_2060_);
v_sz_boxed_2070_ = lean_unbox_usize(v_sz_2062_);
lean_dec(v_sz_2062_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2063_);
lean_dec(v_i_2063_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2056_, v_val_2057_, v_cmd_2058_, v_onUnsolved_boxed_2068_, v___y_13280__boxed_2069_, v_as_2061_, v_sz_boxed_2070_, v_i_boxed_2071_, v_b_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_as_2061_);
lean_dec_ref(v_val_2057_);
lean_dec_ref(v___x_2056_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(lean_object* v_init_2073_, lean_object* v___x_2074_, lean_object* v_val_2075_, lean_object* v_cmd_2076_, uint8_t v_onUnsolved_2077_, uint8_t v___y_2078_, lean_object* v_n_2079_, lean_object* v_b_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
if (lean_obj_tag(v_n_2079_) == 0)
{
lean_object* v_cs_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v_cs_2084_ = lean_ctor_get(v_n_2079_, 0);
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v_b_2080_);
v_sz_2087_ = lean_array_size(v_cs_2084_);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2073_, v___x_2074_, v_val_2075_, v_cmd_2076_, v_onUnsolved_2077_, v___y_2078_, v_cs_2084_, v_sz_2087_, v___x_2088_, v___x_2086_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_fst_2094_; 
v_fst_2094_ = lean_ctor_get(v_a_2090_, 0);
if (lean_obj_tag(v_fst_2094_) == 0)
{
lean_object* v_snd_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v_snd_2095_ = lean_ctor_get(v_a_2090_, 1);
lean_inc(v_snd_2095_);
lean_dec(v_a_2090_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_snd_2095_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2096_);
v___x_2098_ = v___x_2092_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
else
{
lean_object* v_val_2100_; lean_object* v___x_2102_; 
lean_inc_ref(v_fst_2094_);
lean_dec(v_a_2090_);
v_val_2100_ = lean_ctor_get(v_fst_2094_, 0);
lean_inc(v_val_2100_);
lean_dec_ref_known(v_fst_2094_, 1);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v_val_2100_);
v___x_2102_ = v___x_2092_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_val_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2089_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2089_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_vs_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; size_t v_sz_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v_vs_2113_ = lean_ctor_get(v_n_2079_, 0);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v_b_2080_);
v_sz_2116_ = lean_array_size(v_vs_2113_);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2074_, v_val_2075_, v_cmd_2076_, v_onUnsolved_2077_, v___y_2078_, v_vs_2113_, v_sz_2116_, v___x_2117_, v___x_2115_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2133_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2133_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2133_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_fst_2123_; 
v_fst_2123_ = lean_ctor_get(v_a_2119_, 0);
if (lean_obj_tag(v_fst_2123_) == 0)
{
lean_object* v_snd_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v_snd_2124_ = lean_ctor_get(v_a_2119_, 1);
lean_inc(v_snd_2124_);
lean_dec(v_a_2119_);
v___x_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2125_, 0, v_snd_2124_);
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
else
{
lean_object* v_val_2129_; lean_object* v___x_2131_; 
lean_inc_ref(v_fst_2123_);
lean_dec(v_a_2119_);
v_val_2129_ = lean_ctor_get(v_fst_2123_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v_fst_2123_, 1);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v_val_2129_);
v___x_2131_ = v___x_2121_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_val_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_a_2134_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2118_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2118_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(lean_object* v_init_2142_, lean_object* v___x_2143_, lean_object* v_val_2144_, lean_object* v_cmd_2145_, uint8_t v_onUnsolved_2146_, uint8_t v___y_2147_, lean_object* v_as_2148_, size_t v_sz_2149_, size_t v_i_2150_, lean_object* v_b_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_lt(v_i_2150_, v_sz_2149_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
lean_dec(v_cmd_2145_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_b_2151_);
return v___x_2156_;
}
else
{
lean_object* v_snd_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2191_; 
v_snd_2157_ = lean_ctor_get(v_b_2151_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_b_2151_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v_b_2151_, 0);
lean_dec(v_unused_2192_);
v___x_2159_ = v_b_2151_;
v_isShared_2160_ = v_isSharedCheck_2191_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_snd_2157_);
lean_dec(v_b_2151_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2191_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v_a_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_box(0);
v_a_2162_ = lean_array_uget_borrowed(v_as_2148_, v_i_2150_);
lean_inc(v_snd_2157_);
lean_inc(v_cmd_2145_);
v___x_2163_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2142_, v___x_2143_, v_val_2144_, v_cmd_2145_, v_onUnsolved_2146_, v___y_2147_, v_a_2162_, v_snd_2157_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2182_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2182_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2182_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
if (lean_obj_tag(v_a_2164_) == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_dec(v_cmd_2145_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_a_2164_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2168_);
v___x_2170_ = v___x_2159_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_snd_2157_);
v___x_2170_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2170_);
v___x_2172_ = v___x_2166_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; 
lean_del_object(v___x_2166_);
lean_dec(v_snd_2157_);
v_a_2175_ = lean_ctor_get(v_a_2164_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v_a_2164_, 1);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v_a_2175_);
lean_ctor_set(v___x_2159_, 0, v___x_2161_);
v___x_2177_ = v___x_2159_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_a_2175_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
size_t v___x_2178_; size_t v___x_2179_; 
v___x_2178_ = ((size_t)1ULL);
v___x_2179_ = lean_usize_add(v_i_2150_, v___x_2178_);
v_i_2150_ = v___x_2179_;
v_b_2151_ = v___x_2177_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2159_);
lean_dec(v_snd_2157_);
lean_dec(v_cmd_2145_);
v_a_2183_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2163_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2163_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10___boxed(lean_object* v_init_2193_, lean_object* v___x_2194_, lean_object* v_val_2195_, lean_object* v_cmd_2196_, lean_object* v_onUnsolved_2197_, lean_object* v___y_2198_, lean_object* v_as_2199_, lean_object* v_sz_2200_, lean_object* v_i_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v_onUnsolved_boxed_2206_; uint8_t v___y_13581__boxed_2207_; size_t v_sz_boxed_2208_; size_t v_i_boxed_2209_; lean_object* v_res_2210_; 
v_onUnsolved_boxed_2206_ = lean_unbox(v_onUnsolved_2197_);
v___y_13581__boxed_2207_ = lean_unbox(v___y_2198_);
v_sz_boxed_2208_ = lean_unbox_usize(v_sz_2200_);
lean_dec(v_sz_2200_);
v_i_boxed_2209_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2193_, v___x_2194_, v_val_2195_, v_cmd_2196_, v_onUnsolved_boxed_2206_, v___y_13581__boxed_2207_, v_as_2199_, v_sz_boxed_2208_, v_i_boxed_2209_, v_b_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_as_2199_);
lean_dec_ref(v_val_2195_);
lean_dec_ref(v___x_2194_);
lean_dec_ref(v_init_2193_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8___boxed(lean_object* v_init_2211_, lean_object* v___x_2212_, lean_object* v_val_2213_, lean_object* v_cmd_2214_, lean_object* v_onUnsolved_2215_, lean_object* v___y_2216_, lean_object* v_n_2217_, lean_object* v_b_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v_onUnsolved_boxed_2222_; uint8_t v___y_13603__boxed_2223_; lean_object* v_res_2224_; 
v_onUnsolved_boxed_2222_ = lean_unbox(v_onUnsolved_2215_);
v___y_13603__boxed_2223_ = lean_unbox(v___y_2216_);
v_res_2224_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2211_, v___x_2212_, v_val_2213_, v_cmd_2214_, v_onUnsolved_boxed_2222_, v___y_13603__boxed_2223_, v_n_2217_, v_b_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec_ref(v_n_2217_);
lean_dec_ref(v_val_2213_);
lean_dec_ref(v___x_2212_);
lean_dec_ref(v_init_2211_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object* v___x_2225_, lean_object* v_val_2226_, lean_object* v_cmd_2227_, uint8_t v_onUnsolved_2228_, uint8_t v___y_2229_, lean_object* v_t_2230_, lean_object* v_init_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_root_2235_; lean_object* v_tail_2236_; lean_object* v___x_2237_; 
v_root_2235_ = lean_ctor_get(v_t_2230_, 0);
v_tail_2236_ = lean_ctor_get(v_t_2230_, 1);
lean_inc(v_cmd_2227_);
lean_inc_ref(v_init_2231_);
v___x_2237_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2231_, v___x_2225_, v_val_2226_, v_cmd_2227_, v_onUnsolved_2228_, v___y_2229_, v_root_2235_, v_init_2231_, v___y_2232_, v___y_2233_);
lean_dec_ref(v_init_2231_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2274_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2274_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2274_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
if (lean_obj_tag(v_a_2238_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; 
lean_dec(v_cmd_2227_);
v_a_2242_ = lean_ctor_get(v_a_2238_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v_a_2238_, 1);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v_a_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; size_t v_sz_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
lean_del_object(v___x_2240_);
v_a_2246_ = lean_ctor_get(v_a_2238_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v_a_2238_, 1);
v___x_2247_ = lean_box(0);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v_a_2246_);
v_sz_2249_ = lean_array_size(v_tail_2236_);
v___x_2250_ = ((size_t)0ULL);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_2225_, v_val_2226_, v_cmd_2227_, v_onUnsolved_2228_, v___y_2229_, v_tail_2236_, v_sz_2249_, v___x_2250_, v___x_2248_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2265_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2265_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2265_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_fst_2256_; 
v_fst_2256_ = lean_ctor_get(v_a_2252_, 0);
if (lean_obj_tag(v_fst_2256_) == 0)
{
lean_object* v_snd_2257_; lean_object* v___x_2259_; 
v_snd_2257_ = lean_ctor_get(v_a_2252_, 1);
lean_inc(v_snd_2257_);
lean_dec(v_a_2252_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v_snd_2257_);
v___x_2259_ = v___x_2254_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_snd_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
else
{
lean_object* v_val_2261_; lean_object* v___x_2263_; 
lean_inc_ref(v_fst_2256_);
lean_dec(v_a_2252_);
v_val_2261_ = lean_ctor_get(v_fst_2256_, 0);
lean_inc(v_val_2261_);
lean_dec_ref_known(v_fst_2256_, 1);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v_val_2261_);
v___x_2263_ = v___x_2254_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_val_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_a_2266_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2251_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2251_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_cmd_2227_);
v_a_2275_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2237_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2237_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object* v___x_2283_, lean_object* v_val_2284_, lean_object* v_cmd_2285_, lean_object* v_onUnsolved_2286_, lean_object* v___y_2287_, lean_object* v_t_2288_, lean_object* v_init_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
uint8_t v_onUnsolved_boxed_2293_; uint8_t v___y_13794__boxed_2294_; lean_object* v_res_2295_; 
v_onUnsolved_boxed_2293_ = lean_unbox(v_onUnsolved_2286_);
v___y_13794__boxed_2294_ = lean_unbox(v___y_2287_);
v_res_2295_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2283_, v_val_2284_, v_cmd_2285_, v_onUnsolved_boxed_2293_, v___y_13794__boxed_2294_, v_t_2288_, v_init_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec_ref(v_t_2288_);
lean_dec_ref(v_val_2284_);
lean_dec_ref(v___x_2283_);
return v_res_2295_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_unsigned_to_nat(16u);
v___x_2298_ = lean_mk_array(v___x_2297_, v___x_2296_);
return v___x_2298_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___x_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2305_, lean_object* v_opts_2306_, lean_object* v_tree_2307_, lean_object* v_msgs_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
uint8_t v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; uint8_t v___y_2316_; lean_object* v___y_2317_; uint8_t v___y_2344_; uint8_t v___y_2345_; lean_object* v_acc_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___f_2350_; uint8_t v___y_2352_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___f_2350_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2359_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2360_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2306_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2362_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2306_, v___x_2361_);
v___y_2352_ = v___x_2362_;
goto v___jp_2351_;
}
else
{
v___y_2352_ = v___x_2360_;
goto v___jp_2351_;
}
v___jp_2312_:
{
uint8_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = 1;
v___x_2319_ = l_Lean_Syntax_getRange_x3f(v_cmd_2305_, v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 1)
{
lean_object* v_val_2320_; lean_object* v_fileMap_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_val_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v_fileMap_2321_ = lean_ctor_get(v___y_2317_, 1);
v___x_2322_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___y_2314_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v_fileMap_2321_, v_val_2320_, v_cmd_2305_, v___y_2316_, v___y_2313_, v_msgs_2308_, v___x_2323_, v___y_2317_, v___y_2315_);
lean_dec(v_val_2320_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v_fst_2329_; lean_object* v___x_2331_; 
v_fst_2329_ = lean_ctor_get(v_a_2325_, 0);
lean_inc(v_fst_2329_);
lean_dec(v_a_2325_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v_fst_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_fst_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2324_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2324_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v___x_2342_; 
lean_dec(v___x_2319_);
lean_dec(v_cmd_2305_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___y_2314_);
return v___x_2342_;
}
}
v___jp_2343_:
{
if (v___y_2345_ == 0)
{
if (v___y_2344_ == 0)
{
lean_object* v___x_2349_; 
lean_dec(v_cmd_2305_);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v_acc_2346_);
return v___x_2349_;
}
else
{
v___y_2313_ = v___y_2344_;
v___y_2314_ = v_acc_2346_;
v___y_2315_ = v___y_2348_;
v___y_2316_ = v___y_2345_;
v___y_2317_ = v___y_2347_;
goto v___jp_2312_;
}
}
else
{
v___y_2313_ = v___y_2344_;
v___y_2314_ = v_acc_2346_;
v___y_2315_ = v___y_2348_;
v___y_2316_ = v___y_2345_;
v___y_2317_ = v___y_2347_;
goto v___jp_2312_;
}
}
v___jp_2351_:
{
lean_object* v___x_2353_; uint8_t v_onUnsolved_2354_; lean_object* v___x_2355_; uint8_t v_onSorry_2356_; lean_object* v_acc_2357_; 
v___x_2353_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2354_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2306_, v___x_2353_);
v___x_2355_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2356_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2306_, v___x_2355_);
v_acc_2357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2356_ == 0)
{
lean_dec_ref(v_tree_2307_);
v___y_2344_ = v___y_2352_;
v___y_2345_ = v_onUnsolved_2354_;
v_acc_2346_ = v_acc_2357_;
v___y_2347_ = v_a_2309_;
v___y_2348_ = v_a_2310_;
goto v___jp_2343_;
}
else
{
lean_object* v_acc_2358_; 
v_acc_2358_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2350_, v_acc_2357_, v_tree_2307_);
v___y_2344_ = v___y_2352_;
v___y_2345_ = v_onUnsolved_2354_;
v_acc_2346_ = v_acc_2358_;
v___y_2347_ = v_a_2309_;
v___y_2348_ = v_a_2310_;
goto v___jp_2343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2363_, lean_object* v_opts_2364_, lean_object* v_tree_2365_, lean_object* v_msgs_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2363_, v_opts_2364_, v_tree_2365_, v_msgs_2366_, v_a_2367_, v_a_2368_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec_ref(v_msgs_2366_);
lean_dec_ref(v_opts_2364_);
return v_res_2370_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2371_, lean_object* v_m_2372_, lean_object* v_a_2373_){
_start:
{
uint8_t v___x_2374_; 
v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2372_, v_a_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object* v_00_u03b2_2375_, lean_object* v_m_2376_, lean_object* v_a_2377_){
_start:
{
uint8_t v_res_2378_; lean_object* v_r_2379_; 
v_res_2378_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(v_00_u03b2_2375_, v_m_2376_, v_a_2377_);
lean_dec_ref(v_a_2377_);
lean_dec_ref(v_m_2376_);
v_r_2379_ = lean_box(v_res_2378_);
return v_r_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v_00_u03b2_2380_, lean_object* v_m_2381_, lean_object* v_a_2382_, lean_object* v_b_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_2381_, v_a_2382_, v_b_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v___x_2385_, lean_object* v_fst_2386_, lean_object* v_snd_2387_, lean_object* v___x_2388_, lean_object* v_as_2389_, size_t v_sz_2390_, size_t v_i_2391_, lean_object* v_b_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_2385_, v_fst_2386_, v_snd_2387_, v___x_2388_, v_as_2389_, v_sz_2390_, v_i_2391_, v_b_2392_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v___x_2397_, lean_object* v_fst_2398_, lean_object* v_snd_2399_, lean_object* v___x_2400_, lean_object* v_as_2401_, lean_object* v_sz_2402_, lean_object* v_i_2403_, lean_object* v_b_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
size_t v_sz_boxed_2408_; size_t v_i_boxed_2409_; lean_object* v_res_2410_; 
v_sz_boxed_2408_ = lean_unbox_usize(v_sz_2402_);
lean_dec(v_sz_2402_);
v_i_boxed_2409_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_res_2410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2397_, v_fst_2398_, v_snd_2399_, v___x_2400_, v_as_2401_, v_sz_boxed_2408_, v_i_boxed_2409_, v_b_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec_ref(v_as_2401_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(lean_object* v_msgData_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_2411_, v___y_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___boxed(lean_object* v_msgData_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(v_msgData_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2420_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_object* v_00_u03b2_2421_, lean_object* v_a_2422_, lean_object* v_x_2423_){
_start:
{
uint8_t v___x_2424_; 
v___x_2424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_2422_, v_x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2425_, lean_object* v_a_2426_, lean_object* v_x_2427_){
_start:
{
uint8_t v_res_2428_; lean_object* v_r_2429_; 
v_res_2428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(v_00_u03b2_2425_, v_a_2426_, v_x_2427_);
lean_dec(v_x_2427_);
lean_dec_ref(v_a_2426_);
v_r_2429_ = lean_box(v_res_2428_);
return v_r_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3(lean_object* v_00_u03b2_2430_, lean_object* v_data_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_data_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2433_, lean_object* v_i_2434_, lean_object* v_source_2435_, lean_object* v_target_2436_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v_i_2434_, v_source_2435_, v_target_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2438_, lean_object* v_x_2439_, lean_object* v_x_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_x_2439_, v_x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
v___x_2450_ = lean_apply_7(v_x_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, lean_box(0));
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2460_, lean_object* v_x_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___f_2469_; lean_object* v___x_2470_; 
lean_inc(v___y_2463_);
lean_inc_ref(v___y_2462_);
v___f_2469_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2469_, 0, v_x_2461_);
lean_closure_set(v___f_2469_, 1, v___y_2462_);
lean_closure_set(v___f_2469_, 2, v___y_2463_);
v___x_2470_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2460_, v___f_2469_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
if (lean_obj_tag(v___x_2470_) == 0)
{
return v___x_2470_;
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2479_, lean_object* v_x_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2479_, v_x_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2489_, lean_object* v_mvarId_2490_, lean_object* v_x_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2490_, v_x_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2500_, lean_object* v_mvarId_2501_, lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2500_, v_mvarId_2501_, v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2552_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2553_, lean_object* v_x_2554_){
_start:
{
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2555_, lean_object* v_x_2556_){
_start:
{
uint8_t v___x_10984__boxed_2557_; uint8_t v_res_2558_; lean_object* v_r_2559_; 
v___x_10984__boxed_2557_ = lean_unbox(v___x_2555_);
v_res_2558_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_10984__boxed_2557_, v_x_2556_);
lean_dec(v_x_2556_);
v_r_2559_ = lean_box(v_res_2558_);
return v_r_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v_env_2567_; uint8_t v___x_2568_; lean_object* v_env_2569_; lean_object* v___x_2570_; lean_object* v_toCold_2571_; lean_object* v_mctx_2572_; lean_object* v_lctx_2573_; lean_object* v_options_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2566_ = lean_st_ref_get(v___y_2564_);
v_env_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc_ref(v_env_2567_);
lean_dec(v___x_2566_);
v___x_2568_ = 0;
v_env_2569_ = l_Lean_Environment_setRecordingDeps(v_env_2567_, v___x_2568_);
v___x_2570_ = lean_st_ref_get(v___y_2562_);
v_toCold_2571_ = lean_ctor_get(v___y_2563_, 0);
v_mctx_2572_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_ref(v_mctx_2572_);
lean_dec(v___x_2570_);
v_lctx_2573_ = lean_ctor_get(v___y_2561_, 2);
v_options_2574_ = lean_ctor_get(v_toCold_2571_, 2);
lean_inc_ref(v_options_2574_);
lean_inc_ref(v_lctx_2573_);
v___x_2575_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2575_, 0, v_env_2569_);
lean_ctor_set(v___x_2575_, 1, v_mctx_2572_);
lean_ctor_set(v___x_2575_, 2, v_lctx_2573_);
lean_ctor_set(v___x_2575_, 3, v_options_2574_);
v___x_2576_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v_msgData_2560_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2585_, lean_object* v_msg_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_ref_2592_; lean_object* v___x_2593_; lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2639_; 
v_ref_2592_ = lean_ctor_get(v___y_2589_, 2);
v___x_2593_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2639_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2639_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v_traceState_2599_; lean_object* v_env_2600_; lean_object* v_nextMacroScope_2601_; lean_object* v_ngen_2602_; lean_object* v_auxDeclNGen_2603_; lean_object* v_cache_2604_; lean_object* v_recordedDeps_2605_; lean_object* v_messages_2606_; lean_object* v_infoState_2607_; lean_object* v_snapshotTasks_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2638_; 
v___x_2598_ = lean_st_ref_take(v___y_2590_);
v_traceState_2599_ = lean_ctor_get(v___x_2598_, 4);
v_env_2600_ = lean_ctor_get(v___x_2598_, 0);
v_nextMacroScope_2601_ = lean_ctor_get(v___x_2598_, 1);
v_ngen_2602_ = lean_ctor_get(v___x_2598_, 2);
v_auxDeclNGen_2603_ = lean_ctor_get(v___x_2598_, 3);
v_cache_2604_ = lean_ctor_get(v___x_2598_, 5);
v_recordedDeps_2605_ = lean_ctor_get(v___x_2598_, 6);
v_messages_2606_ = lean_ctor_get(v___x_2598_, 7);
v_infoState_2607_ = lean_ctor_get(v___x_2598_, 8);
v_snapshotTasks_2608_ = lean_ctor_get(v___x_2598_, 9);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2610_ = v___x_2598_;
v_isShared_2611_ = v_isSharedCheck_2638_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_snapshotTasks_2608_);
lean_inc(v_infoState_2607_);
lean_inc(v_messages_2606_);
lean_inc(v_recordedDeps_2605_);
lean_inc(v_cache_2604_);
lean_inc(v_traceState_2599_);
lean_inc(v_auxDeclNGen_2603_);
lean_inc(v_ngen_2602_);
lean_inc(v_nextMacroScope_2601_);
lean_inc(v_env_2600_);
lean_dec(v___x_2598_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2638_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
uint64_t v_tid_2612_; lean_object* v_traces_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2637_; 
v_tid_2612_ = lean_ctor_get_uint64(v_traceState_2599_, sizeof(void*)*1);
v_traces_2613_ = lean_ctor_get(v_traceState_2599_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_traceState_2599_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2615_ = v_traceState_2599_;
v_isShared_2616_ = v_isSharedCheck_2637_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_traces_2613_);
lean_dec(v_traceState_2599_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2637_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; double v___x_2619_; uint8_t v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_box(0);
v___x_2619_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2620_ = 0;
v___x_2621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2622_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2622_, 0, v_cls_2585_);
lean_ctor_set(v___x_2622_, 1, v___x_2618_);
lean_ctor_set(v___x_2622_, 2, v___x_2621_);
lean_ctor_set_float(v___x_2622_, sizeof(void*)*3, v___x_2619_);
lean_ctor_set_float(v___x_2622_, sizeof(void*)*3 + 8, v___x_2619_);
lean_ctor_set_uint8(v___x_2622_, sizeof(void*)*3 + 16, v___x_2620_);
v___x_2623_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2624_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v_a_2594_);
lean_ctor_set(v___x_2624_, 2, v___x_2623_);
lean_inc(v_ref_2592_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v_ref_2592_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = l_Lean_PersistentArray_push___redArg(v_traces_2613_, v___x_2625_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2626_);
v___x_2628_ = v___x_2615_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2626_);
lean_ctor_set_uint64(v_reuseFailAlloc_2636_, sizeof(void*)*1, v_tid_2612_);
v___x_2628_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 4, v___x_2628_);
v___x_2630_ = v___x_2610_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_env_2600_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_nextMacroScope_2601_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v_ngen_2602_);
lean_ctor_set(v_reuseFailAlloc_2635_, 3, v_auxDeclNGen_2603_);
lean_ctor_set(v_reuseFailAlloc_2635_, 4, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2635_, 5, v_cache_2604_);
lean_ctor_set(v_reuseFailAlloc_2635_, 6, v_recordedDeps_2605_);
lean_ctor_set(v_reuseFailAlloc_2635_, 7, v_messages_2606_);
lean_ctor_set(v_reuseFailAlloc_2635_, 8, v_infoState_2607_);
lean_ctor_set(v_reuseFailAlloc_2635_, 9, v_snapshotTasks_2608_);
v___x_2630_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = lean_st_ref_put(v___y_2590_, v___x_2630_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2617_);
v___x_2633_ = v___x_2596_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2617_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2640_, lean_object* v_msg_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2640_, v_msg_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2650_ = l_Lean_stringToMessageData(v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2651_, lean_object* v___f_2652_, lean_object* v___x_2653_, lean_object* v___x_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; lean_object* v_a_2664_; lean_object* v___y_2668_; lean_object* v___x_2682_; 
v___x_2662_ = lean_st_mk_ref(v___x_2651_);
v___x_2682_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2662_, v___y_2656_, v___y_2658_, v___y_2660_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2654_, v___x_2653_, v___x_2662_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; 
lean_dec(v_a_2683_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___f_2652_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v_a_2664_ = v_a_2685_;
goto v___jp_2663_;
}
else
{
lean_object* v_a_2686_; uint8_t v___x_2687_; 
v_a_2686_ = lean_ctor_get(v___x_2684_, 0);
v___x_2687_ = l_Lean_Exception_isInterrupt(v_a_2686_);
if (v___x_2687_ == 0)
{
uint8_t v___x_2688_; 
lean_inc(v_a_2686_);
v___x_2688_ = l_Lean_Exception_isRuntime(v_a_2686_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; 
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2689_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2683_, v___x_2688_, v___x_2662_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2718_; 
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v___x_2689_, 0);
lean_dec(v_unused_2719_);
v___x_2691_ = v___x_2689_;
v_isShared_2692_ = v_isSharedCheck_2718_;
goto v_resetjp_2690_;
}
else
{
lean_dec(v___x_2689_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2718_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
uint8_t v___x_2693_; 
lean_inc(v_a_2686_);
v___x_2693_ = l_Lean_Exception_isMaxRecDepth(v_a_2686_);
if (v___x_2693_ == 0)
{
lean_object* v_toCold_2694_; lean_object* v_options_2695_; uint8_t v_hasTrace_2696_; 
lean_del_object(v___x_2691_);
v_toCold_2694_ = lean_ctor_get(v___y_2659_, 0);
v_options_2695_ = lean_ctor_get(v_toCold_2694_, 2);
v_hasTrace_2696_ = lean_ctor_get_uint8(v_options_2695_, sizeof(void*)*1);
if (v_hasTrace_2696_ == 0)
{
lean_dec(v_a_2686_);
goto v___jp_2679_;
}
else
{
lean_object* v_inheritedTraceOptions_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v_inheritedTraceOptions_2697_ = lean_ctor_get(v_toCold_2694_, 11);
v___x_2698_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2699_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2700_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2697_, v_options_2695_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_dec(v_a_2686_);
goto v___jp_2679_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2701_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2702_ = l_Lean_Exception_toMessageData(v_a_2686_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2698_, v___x_2703_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
lean_inc(v___x_2662_);
v___x_2706_ = lean_apply_10(v___f_2652_, v_a_2705_, v___x_2653_, v___x_2662_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, lean_box(0));
v___y_2668_ = v___x_2706_;
goto v___jp_2667_;
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v___x_2662_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___f_2652_);
v_a_2707_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2704_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2704_);
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
}
}
}
else
{
lean_object* v___x_2716_; 
lean_dec(v___x_2662_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___f_2652_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 1);
lean_ctor_set(v___x_2691_, 0, v_a_2686_);
v___x_2716_ = v___x_2691_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2686_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2686_);
lean_dec(v___x_2662_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___f_2652_);
v_a_2720_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2689_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2689_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_dec(v_a_2683_);
lean_dec(v___x_2662_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___f_2652_);
return v___x_2684_;
}
}
else
{
lean_dec(v_a_2683_);
lean_dec(v___x_2662_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___f_2652_);
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v___x_2662_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___f_2652_);
v_a_2728_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2682_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2682_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
v___jp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_st_ref_get(v___x_2662_);
lean_dec(v___x_2662_);
lean_dec(v___x_2665_);
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_a_2664_);
return v___x_2666_;
}
v___jp_2667_:
{
if (lean_obj_tag(v___y_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v_a_2670_; 
v_a_2669_ = lean_ctor_get(v___y_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___y_2668_, 1);
v_a_2670_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_a_2670_);
lean_dec(v_a_2669_);
v_a_2664_ = v_a_2670_;
goto v___jp_2663_;
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v___x_2662_);
v_a_2671_ = lean_ctor_get(v___y_2668_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___y_2668_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___y_2668_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___y_2668_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
v___jp_2679_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = lean_box(0);
lean_inc(v___x_2662_);
v___x_2681_ = lean_apply_10(v___f_2652_, v___x_2680_, v___x_2653_, v___x_2662_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, lean_box(0));
v___y_2668_ = v___x_2681_;
goto v___jp_2667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2736_, lean_object* v___f_2737_, lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2736_, v___f_2737_, v___x_2738_, v___x_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2748_, uint8_t v___x_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2748_, v___x_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2758_, lean_object* v___x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
uint8_t v___x_11303__boxed_2767_; lean_object* v_res_2768_; 
v___x_11303__boxed_2767_ = lean_unbox(v___x_2759_);
v_res_2768_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2758_, v___x_11303__boxed_2767_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2769_, lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_ref_2776_; lean_object* v___x_2777_; lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2823_; 
v_ref_2776_ = lean_ctor_get(v___y_2773_, 2);
v___x_2777_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2823_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2823_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v_traceState_2783_; lean_object* v_env_2784_; lean_object* v_nextMacroScope_2785_; lean_object* v_ngen_2786_; lean_object* v_auxDeclNGen_2787_; lean_object* v_cache_2788_; lean_object* v_recordedDeps_2789_; lean_object* v_messages_2790_; lean_object* v_infoState_2791_; lean_object* v_snapshotTasks_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2822_; 
v___x_2782_ = lean_st_ref_take(v___y_2774_);
v_traceState_2783_ = lean_ctor_get(v___x_2782_, 4);
v_env_2784_ = lean_ctor_get(v___x_2782_, 0);
v_nextMacroScope_2785_ = lean_ctor_get(v___x_2782_, 1);
v_ngen_2786_ = lean_ctor_get(v___x_2782_, 2);
v_auxDeclNGen_2787_ = lean_ctor_get(v___x_2782_, 3);
v_cache_2788_ = lean_ctor_get(v___x_2782_, 5);
v_recordedDeps_2789_ = lean_ctor_get(v___x_2782_, 6);
v_messages_2790_ = lean_ctor_get(v___x_2782_, 7);
v_infoState_2791_ = lean_ctor_get(v___x_2782_, 8);
v_snapshotTasks_2792_ = lean_ctor_get(v___x_2782_, 9);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2794_ = v___x_2782_;
v_isShared_2795_ = v_isSharedCheck_2822_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_snapshotTasks_2792_);
lean_inc(v_infoState_2791_);
lean_inc(v_messages_2790_);
lean_inc(v_recordedDeps_2789_);
lean_inc(v_cache_2788_);
lean_inc(v_traceState_2783_);
lean_inc(v_auxDeclNGen_2787_);
lean_inc(v_ngen_2786_);
lean_inc(v_nextMacroScope_2785_);
lean_inc(v_env_2784_);
lean_dec(v___x_2782_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2822_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
uint64_t v_tid_2796_; lean_object* v_traces_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2821_; 
v_tid_2796_ = lean_ctor_get_uint64(v_traceState_2783_, sizeof(void*)*1);
v_traces_2797_ = lean_ctor_get(v_traceState_2783_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_traceState_2783_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2799_ = v_traceState_2783_;
v_isShared_2800_ = v_isSharedCheck_2821_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_traces_2797_);
lean_dec(v_traceState_2783_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2821_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; double v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2804_ = 0;
v___x_2805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2806_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2806_, 0, v_cls_2769_);
lean_ctor_set(v___x_2806_, 1, v___x_2802_);
lean_ctor_set(v___x_2806_, 2, v___x_2805_);
lean_ctor_set_float(v___x_2806_, sizeof(void*)*3, v___x_2803_);
lean_ctor_set_float(v___x_2806_, sizeof(void*)*3 + 8, v___x_2803_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*3 + 16, v___x_2804_);
v___x_2807_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2808_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v_a_2778_);
lean_ctor_set(v___x_2808_, 2, v___x_2807_);
lean_inc(v_ref_2776_);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v_ref_2776_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = l_Lean_PersistentArray_push___redArg(v_traces_2797_, v___x_2809_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2810_);
v___x_2812_ = v___x_2799_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2810_);
lean_ctor_set_uint64(v_reuseFailAlloc_2820_, sizeof(void*)*1, v_tid_2796_);
v___x_2812_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2814_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 4, v___x_2812_);
v___x_2814_ = v___x_2794_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_env_2784_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_nextMacroScope_2785_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_ngen_2786_);
lean_ctor_set(v_reuseFailAlloc_2819_, 3, v_auxDeclNGen_2787_);
lean_ctor_set(v_reuseFailAlloc_2819_, 4, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2819_, 5, v_cache_2788_);
lean_ctor_set(v_reuseFailAlloc_2819_, 6, v_recordedDeps_2789_);
lean_ctor_set(v_reuseFailAlloc_2819_, 7, v_messages_2790_);
lean_ctor_set(v_reuseFailAlloc_2819_, 8, v_infoState_2791_);
lean_ctor_set(v_reuseFailAlloc_2819_, 9, v_snapshotTasks_2792_);
v___x_2814_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = lean_st_ref_put(v___y_2774_, v___x_2814_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2801_);
v___x_2817_ = v___x_2780_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2801_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2824_, lean_object* v_msg_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2824_, v_msg_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
return v_res_2831_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2834_ = l_Lean_stringToMessageData(v___x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v___f_2835_, lean_object* v_term_2836_, lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v___y_2845_; lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2836_, v___x_2837_, v___x_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___f_2835_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2875_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2875_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v_fst_2871_; lean_object* v___x_2873_; 
v_fst_2871_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_fst_2871_);
lean_dec(v_a_2867_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v_fst_2871_);
v___x_2873_ = v___x_2869_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_fst_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2913_; 
v_a_2876_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2878_ = v___x_2866_;
v_isShared_2879_ = v_isSharedCheck_2913_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2866_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2913_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint8_t v___x_2880_; 
v___x_2880_ = l_Lean_Exception_isInterrupt(v_a_2876_);
if (v___x_2880_ == 0)
{
uint8_t v___x_2881_; 
lean_inc(v_a_2876_);
v___x_2881_ = l_Lean_Exception_isRuntime(v_a_2876_);
if (v___x_2881_ == 0)
{
uint8_t v___x_2882_; 
lean_inc(v_a_2876_);
v___x_2882_ = l_Lean_Exception_isMaxRecDepth(v_a_2876_);
if (v___x_2882_ == 0)
{
lean_object* v_toCold_2883_; lean_object* v_options_2884_; uint8_t v_hasTrace_2885_; 
lean_del_object(v___x_2878_);
v_toCold_2883_ = lean_ctor_get(v___y_2841_, 0);
v_options_2884_ = lean_ctor_get(v_toCold_2883_, 2);
v_hasTrace_2885_ = lean_ctor_get_uint8(v_options_2884_, sizeof(void*)*1);
if (v_hasTrace_2885_ == 0)
{
lean_dec(v_a_2876_);
goto v___jp_2863_;
}
else
{
lean_object* v_inheritedTraceOptions_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v_inheritedTraceOptions_2886_ = lean_ctor_get(v_toCold_2883_, 11);
v___x_2887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2888_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2889_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2886_, v_options_2884_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_dec(v_a_2876_);
goto v___jp_2863_;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2890_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2891_ = l_Lean_Exception_toMessageData(v_a_2876_);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2887_, v___x_2892_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = lean_apply_6(v___f_2835_, v_a_2894_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, lean_box(0));
v___y_2845_ = v___x_2895_;
goto v___jp_2844_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___f_2835_);
v_a_2896_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2893_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2893_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
}
else
{
lean_object* v___x_2905_; 
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___f_2835_);
if (v_isShared_2879_ == 0)
{
v___x_2905_ = v___x_2878_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2876_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
lean_object* v___x_2908_; 
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___f_2835_);
if (v_isShared_2879_ == 0)
{
v___x_2908_ = v___x_2878_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2876_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
else
{
lean_object* v___x_2911_; 
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___f_2835_);
if (v_isShared_2879_ == 0)
{
v___x_2911_ = v___x_2878_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2876_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
v___jp_2844_:
{
if (lean_obj_tag(v___y_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2854_; 
v_a_2846_ = lean_ctor_get(v___y_2845_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___y_2845_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2848_ = v___y_2845_;
v_isShared_2849_ = v_isSharedCheck_2854_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___y_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2854_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v_a_2850_; lean_object* v___x_2852_; 
v_a_2850_ = lean_ctor_get(v_a_2846_, 0);
lean_inc(v_a_2850_);
lean_dec(v_a_2846_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v_a_2850_);
v___x_2852_ = v___x_2848_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
v_a_2855_ = lean_ctor_get(v___y_2845_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___y_2845_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___y_2845_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___y_2845_);
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
v___jp_2863_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_apply_6(v___f_2835_, v___x_2864_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, lean_box(0));
v___y_2845_ = v___x_2865_;
goto v___jp_2844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v___f_2914_, lean_object* v_term_2915_, lean_object* v___x_2916_, lean_object* v___x_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v___f_2914_, v_term_2915_, v___x_2916_, v___x_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2924_, lean_object* v_vals_2925_, lean_object* v_i_2926_, lean_object* v_k_2927_){
_start:
{
lean_object* v___x_2928_; uint8_t v___x_2929_; 
v___x_2928_ = lean_array_get_size(v_keys_2924_);
v___x_2929_ = lean_nat_dec_lt(v_i_2926_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; 
lean_dec(v_i_2926_);
v___x_2930_ = lean_box(0);
return v___x_2930_;
}
else
{
lean_object* v_k_x27_2931_; uint8_t v___x_2932_; 
v_k_x27_2931_ = lean_array_fget_borrowed(v_keys_2924_, v_i_2926_);
v___x_2932_ = l_Lean_instBEqMVarId_beq(v_k_2927_, v_k_x27_2931_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_unsigned_to_nat(1u);
v___x_2934_ = lean_nat_add(v_i_2926_, v___x_2933_);
lean_dec(v_i_2926_);
v_i_2926_ = v___x_2934_;
goto _start;
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_array_fget_borrowed(v_vals_2925_, v_i_2926_);
lean_dec(v_i_2926_);
lean_inc(v___x_2936_);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2938_, lean_object* v_vals_2939_, lean_object* v_i_2940_, lean_object* v_k_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2938_, v_vals_2939_, v_i_2940_, v_k_2941_);
lean_dec(v_k_2941_);
lean_dec_ref(v_vals_2939_);
lean_dec_ref(v_keys_2938_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2943_, size_t v_x_2944_, lean_object* v_x_2945_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
lean_object* v_es_2946_; lean_object* v___x_2947_; size_t v___x_2948_; size_t v___x_2949_; lean_object* v_j_2950_; lean_object* v___x_2951_; 
v_es_2946_ = lean_ctor_get(v_x_2943_, 0);
v___x_2947_ = lean_box(2);
v___x_2948_ = ((size_t)31ULL);
v___x_2949_ = lean_usize_land(v_x_2944_, v___x_2948_);
v_j_2950_ = lean_usize_to_nat(v___x_2949_);
v___x_2951_ = lean_array_get_borrowed(v___x_2947_, v_es_2946_, v_j_2950_);
lean_dec(v_j_2950_);
switch(lean_obj_tag(v___x_2951_))
{
case 0:
{
lean_object* v_key_2952_; lean_object* v_val_2953_; uint8_t v___x_2954_; 
v_key_2952_ = lean_ctor_get(v___x_2951_, 0);
v_val_2953_ = lean_ctor_get(v___x_2951_, 1);
v___x_2954_ = l_Lean_instBEqMVarId_beq(v_x_2945_, v_key_2952_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_box(0);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; 
lean_inc(v_val_2953_);
v___x_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2956_, 0, v_val_2953_);
return v___x_2956_;
}
}
case 1:
{
lean_object* v_node_2957_; size_t v___x_2958_; size_t v___x_2959_; 
v_node_2957_ = lean_ctor_get(v___x_2951_, 0);
v___x_2958_ = ((size_t)5ULL);
v___x_2959_ = lean_usize_shift_right(v_x_2944_, v___x_2958_);
v_x_2943_ = v_node_2957_;
v_x_2944_ = v___x_2959_;
goto _start;
}
default: 
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_box(0);
return v___x_2961_;
}
}
}
else
{
lean_object* v_ks_2962_; lean_object* v_vs_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_ks_2962_ = lean_ctor_get(v_x_2943_, 0);
v_vs_2963_ = lean_ctor_get(v_x_2943_, 1);
v___x_2964_ = lean_unsigned_to_nat(0u);
v___x_2965_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2962_, v_vs_2963_, v___x_2964_, v_x_2945_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v_x_2968_){
_start:
{
size_t v_x_11616__boxed_2969_; lean_object* v_res_2970_; 
v_x_11616__boxed_2969_ = lean_unbox_usize(v_x_2967_);
lean_dec(v_x_2967_);
v_res_2970_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2966_, v_x_11616__boxed_2969_, v_x_2968_);
lean_dec(v_x_2968_);
lean_dec_ref(v_x_2966_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2971_, lean_object* v_x_2972_){
_start:
{
uint64_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = l_Lean_instHashableMVarId_hash(v_x_2972_);
v___x_2974_ = lean_uint64_to_usize(v___x_2973_);
v___x_2975_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2971_, v___x_2974_, v_x_2972_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2976_, lean_object* v_x_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2976_, v_x_2977_);
lean_dec(v_x_2977_);
lean_dec_ref(v_x_2976_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_mctx_3008_; lean_object* v_env_3009_; lean_object* v_opts_3010_; lean_object* v_namingCtx_3011_; lean_object* v_goal_3012_; lean_object* v_decls_3013_; lean_object* v___x_3014_; 
v_mctx_3008_ = lean_ctor_get(v_c_3004_, 3);
lean_inc_ref(v_mctx_3008_);
v_env_3009_ = lean_ctor_get(v_c_3004_, 2);
lean_inc_ref(v_env_3009_);
v_opts_3010_ = lean_ctor_get(v_c_3004_, 4);
lean_inc_ref(v_opts_3010_);
v_namingCtx_3011_ = lean_ctor_get(v_c_3004_, 5);
lean_inc_ref(v_namingCtx_3011_);
v_goal_3012_ = lean_ctor_get(v_c_3004_, 6);
lean_inc(v_goal_3012_);
lean_dec_ref(v_c_3004_);
v_decls_3013_ = lean_ctor_get(v_mctx_3008_, 5);
v___x_3014_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3013_, v_goal_3012_);
if (lean_obj_tag(v___x_3014_) == 1)
{
lean_object* v_val_3015_; lean_object* v_lctx_3016_; lean_object* v___f_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v_term_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___f_3030_; lean_object* v___x_3031_; 
v_val_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_val_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v_lctx_3016_ = lean_ctor_get(v_val_3015_, 1);
lean_inc_ref(v_lctx_3016_);
lean_dec(v_val_3015_);
v___f_3017_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_3018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_3019_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_3020_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_3021_ = lean_box(0);
lean_inc(v_goal_3012_);
v___x_3022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_goal_3012_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___f_3023_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3023_, 0, v___x_3022_);
lean_closure_set(v___f_3023_, 1, v___f_3017_);
lean_closure_set(v___f_3023_, 2, v___x_3020_);
lean_closure_set(v___f_3023_, 3, v___x_3019_);
v___x_3024_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_3024_, 0, lean_box(0));
lean_closure_set(v___x_3024_, 1, v_goal_3012_);
lean_closure_set(v___x_3024_, 2, v___f_3023_);
v___x_3025_ = 1;
v___x_3026_ = lean_box(v___x_3025_);
v_term_3027_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3027_, 0, v___x_3024_);
lean_closure_set(v_term_3027_, 1, v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3029_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3030_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3030_, 0, v___f_3018_);
lean_closure_set(v___f_3030_, 1, v_term_3027_);
lean_closure_set(v___f_3030_, 2, v___x_3028_);
lean_closure_set(v___f_3030_, 3, v___x_3029_);
v___x_3031_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3009_, v_mctx_3008_, v_lctx_3016_, v_opts_3010_, v_namingCtx_3011_, v___f_3030_, v_a_3005_, v_a_3006_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec(v___x_3014_);
lean_dec(v_goal_3012_);
lean_dec_ref(v_namingCtx_3011_);
lean_dec_ref(v_opts_3010_);
lean_dec_ref(v_env_3009_);
lean_dec_ref(v_mctx_3008_);
v___x_3032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3040_, v_x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3043_, lean_object* v_x_3044_, lean_object* v_x_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3043_, v_x_3044_, v_x_3045_);
lean_dec(v_x_3045_);
lean_dec_ref(v_x_3044_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3047_, lean_object* v_msg_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3047_, v_msg_3048_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3059_, lean_object* v_msg_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3059_, v_msg_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3071_, lean_object* v_x_3072_, size_t v_x_3073_, lean_object* v_x_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3072_, v_x_3073_, v_x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_, lean_object* v_x_3079_){
_start:
{
size_t v_x_11873__boxed_3080_; lean_object* v_res_3081_; 
v_x_11873__boxed_3080_ = lean_unbox_usize(v_x_3078_);
lean_dec(v_x_3078_);
v_res_3081_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3076_, v_x_3077_, v_x_11873__boxed_3080_, v_x_3079_);
lean_dec(v_x_3079_);
lean_dec_ref(v_x_3077_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3082_, lean_object* v_keys_3083_, lean_object* v_vals_3084_, lean_object* v_heq_3085_, lean_object* v_i_3086_, lean_object* v_k_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3083_, v_vals_3084_, v_i_3086_, v_k_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3089_, lean_object* v_keys_3090_, lean_object* v_vals_3091_, lean_object* v_heq_3092_, lean_object* v_i_3093_, lean_object* v_k_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3089_, v_keys_3090_, v_vals_3091_, v_heq_3092_, v_i_3093_, v_k_3094_);
lean_dec(v_k_3094_);
lean_dec_ref(v_vals_3091_);
lean_dec_ref(v_keys_3090_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3098_, lean_object* v___x_3099_, lean_object* v_ref_3100_, lean_object* v_a_3101_, lean_object* v___x_3102_, lean_object* v___x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
if (v___x_3098_ == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3099_);
v___x_3108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3109_ = lean_box(0);
v___x_3110_ = 4;
v___x_3111_ = l_Lean_MessageData_nil;
v___x_3112_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3100_, v_a_3101_, v___x_3107_, v___x_3108_, v___x_3109_, v___x_3110_, v___x_3111_, v___y_3104_, v___y_3105_);
return v___x_3112_;
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3113_ = lean_array_get(v___x_3102_, v_a_3101_, v___x_3103_);
lean_dec_ref(v_a_3101_);
v___x_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3099_);
v___x_3115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3116_ = lean_box(0);
v___x_3117_ = 4;
v___x_3118_ = l_Lean_MessageData_nil;
v___x_3119_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3100_, v___x_3113_, v___x_3114_, v___x_3115_, v___x_3116_, v___x_3117_, v___x_3118_, v___y_3104_, v___y_3105_);
return v___x_3119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3120_, lean_object* v___x_3121_, lean_object* v_ref_3122_, lean_object* v_a_3123_, lean_object* v___x_3124_, lean_object* v___x_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v___x_3507__boxed_3129_; lean_object* v_res_3130_; 
v___x_3507__boxed_3129_ = lean_unbox(v___x_3120_);
v_res_3130_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3507__boxed_3129_, v___x_3121_, v_ref_3122_, v_a_3123_, v___x_3124_, v___x_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___x_3125_);
lean_dec_ref(v___x_3124_);
return v_res_3130_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3131_, lean_object* v_x_3132_){
_start:
{
if (lean_obj_tag(v_x_3132_) == 1)
{
lean_object* v_pre_3133_; 
v_pre_3133_ = lean_ctor_get(v_x_3132_, 0);
if (lean_obj_tag(v_pre_3133_) == 0)
{
lean_object* v_str_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_str_3134_ = lean_ctor_get(v_x_3132_, 1);
v___x_3135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1));
v___x_3136_ = lean_string_dec_eq(v_str_3134_, v___x_3135_);
if (v___x_3136_ == 0)
{
return v___x_3136_;
}
else
{
return v_suppressElabErrors_3131_;
}
}
else
{
uint8_t v___x_3137_; 
v___x_3137_ = 0;
return v___x_3137_;
}
}
else
{
uint8_t v___x_3138_; 
v___x_3138_ = 0;
return v___x_3138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3139_, lean_object* v_x_3140_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3141_; uint8_t v_res_3142_; lean_object* v_r_3143_; 
v_suppressElabErrors_boxed_3141_ = lean_unbox(v_suppressElabErrors_3139_);
v_res_3142_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3141_, v_x_3140_);
lean_dec(v_x_3140_);
v_r_3143_ = lean_box(v_res_3142_);
return v_r_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3144_, lean_object* v_msgData_3145_, uint8_t v_severity_3146_, uint8_t v_isSilent_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
uint8_t v___y_3152_; uint8_t v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3217_; uint8_t v___y_3218_; uint8_t v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3243_; uint8_t v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; uint8_t v___y_3250_; uint8_t v___y_3251_; uint8_t v___x_3266_; uint8_t v___y_3268_; uint8_t v___x_3278_; 
v___x_3266_ = 2;
v___x_3278_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3146_, v___x_3266_);
if (v___x_3278_ == 0)
{
v___y_3268_ = v___x_3278_;
goto v___jp_3267_;
}
else
{
uint8_t v___x_3279_; 
lean_inc_ref(v_msgData_3145_);
v___x_3279_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3145_);
if (v___x_3279_ == 0)
{
v___y_3268_ = v___x_3279_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec_ref(v_msgData_3145_);
v___x_3280_ = lean_box(0);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
}
v___jp_3151_:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_Elab_Command_getScope___redArg(v___y_3159_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v_currNamespace_3162_; lean_object* v___x_3163_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v_currNamespace_3162_ = lean_ctor_get(v_a_3161_, 2);
lean_inc(v_currNamespace_3162_);
lean_dec(v_a_3161_);
v___x_3163_ = l_Lean_Elab_Command_getScope___redArg(v___y_3159_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3199_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3199_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3199_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v_openDecls_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v_env_3173_; lean_object* v_messages_3174_; lean_object* v_scopes_3175_; lean_object* v_usedQuotCtxts_3176_; lean_object* v_nextMacroScope_3177_; lean_object* v_maxRecDepth_3178_; lean_object* v_ngen_3179_; lean_object* v_auxDeclNGen_3180_; lean_object* v_infoState_3181_; lean_object* v_traceState_3182_; lean_object* v_snapshotTasks_3183_; lean_object* v_prevLinterStates_3184_; lean_object* v_codeQualityEntryTasks_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3198_; 
v_openDecls_3168_ = lean_ctor_get(v_a_3164_, 3);
lean_inc(v_openDecls_3168_);
lean_dec(v_a_3164_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_currNamespace_3162_);
lean_ctor_set(v___x_3169_, 1, v_openDecls_3168_);
v___x_3170_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___y_3154_);
lean_inc_ref(v___y_3155_);
lean_inc_ref(v___y_3157_);
v___x_3171_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3171_, 0, v___y_3157_);
lean_ctor_set(v___x_3171_, 1, v___y_3158_);
lean_ctor_set(v___x_3171_, 2, v___y_3156_);
lean_ctor_set(v___x_3171_, 3, v___y_3155_);
lean_ctor_set(v___x_3171_, 4, v___x_3170_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*5, v___y_3153_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*5 + 1, v___y_3152_);
lean_ctor_set_uint8(v___x_3171_, sizeof(void*)*5 + 2, v_isSilent_3147_);
v___x_3172_ = lean_st_ref_take(v___y_3159_);
v_env_3173_ = lean_ctor_get(v___x_3172_, 0);
v_messages_3174_ = lean_ctor_get(v___x_3172_, 1);
v_scopes_3175_ = lean_ctor_get(v___x_3172_, 2);
v_usedQuotCtxts_3176_ = lean_ctor_get(v___x_3172_, 3);
v_nextMacroScope_3177_ = lean_ctor_get(v___x_3172_, 4);
v_maxRecDepth_3178_ = lean_ctor_get(v___x_3172_, 5);
v_ngen_3179_ = lean_ctor_get(v___x_3172_, 6);
v_auxDeclNGen_3180_ = lean_ctor_get(v___x_3172_, 7);
v_infoState_3181_ = lean_ctor_get(v___x_3172_, 8);
v_traceState_3182_ = lean_ctor_get(v___x_3172_, 9);
v_snapshotTasks_3183_ = lean_ctor_get(v___x_3172_, 10);
v_prevLinterStates_3184_ = lean_ctor_get(v___x_3172_, 11);
v_codeQualityEntryTasks_3185_ = lean_ctor_get(v___x_3172_, 12);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3187_ = v___x_3172_;
v_isShared_3188_ = v_isSharedCheck_3198_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3185_);
lean_inc(v_prevLinterStates_3184_);
lean_inc(v_snapshotTasks_3183_);
lean_inc(v_traceState_3182_);
lean_inc(v_infoState_3181_);
lean_inc(v_auxDeclNGen_3180_);
lean_inc(v_ngen_3179_);
lean_inc(v_maxRecDepth_3178_);
lean_inc(v_nextMacroScope_3177_);
lean_inc(v_usedQuotCtxts_3176_);
lean_inc(v_scopes_3175_);
lean_inc(v_messages_3174_);
lean_inc(v_env_3173_);
lean_dec(v___x_3172_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3198_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3189_ = lean_box(0);
v___x_3190_ = l_Lean_MessageLog_add(v___x_3171_, v_messages_3174_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 1, v___x_3190_);
v___x_3192_ = v___x_3187_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_env_3173_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v_scopes_3175_);
lean_ctor_set(v_reuseFailAlloc_3197_, 3, v_usedQuotCtxts_3176_);
lean_ctor_set(v_reuseFailAlloc_3197_, 4, v_nextMacroScope_3177_);
lean_ctor_set(v_reuseFailAlloc_3197_, 5, v_maxRecDepth_3178_);
lean_ctor_set(v_reuseFailAlloc_3197_, 6, v_ngen_3179_);
lean_ctor_set(v_reuseFailAlloc_3197_, 7, v_auxDeclNGen_3180_);
lean_ctor_set(v_reuseFailAlloc_3197_, 8, v_infoState_3181_);
lean_ctor_set(v_reuseFailAlloc_3197_, 9, v_traceState_3182_);
lean_ctor_set(v_reuseFailAlloc_3197_, 10, v_snapshotTasks_3183_);
lean_ctor_set(v_reuseFailAlloc_3197_, 11, v_prevLinterStates_3184_);
lean_ctor_set(v_reuseFailAlloc_3197_, 12, v_codeQualityEntryTasks_3185_);
v___x_3192_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
v___x_3193_ = lean_st_ref_put(v___y_3159_, v___x_3192_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3189_);
v___x_3195_ = v___x_3166_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3189_);
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
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_currNamespace_3162_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3154_);
v_a_3200_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3163_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3163_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3154_);
v_a_3208_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3160_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3160_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
v___jp_3216_:
{
lean_object* v_fileName_3221_; lean_object* v_fileMap_3222_; uint8_t v_suppressElabErrors_3223_; lean_object* v___x_3224_; lean_object* v___f_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3241_; 
v_fileName_3221_ = lean_ctor_get(v___y_3148_, 0);
v_fileMap_3222_ = lean_ctor_get(v___y_3148_, 1);
v_suppressElabErrors_3223_ = lean_ctor_get_uint8(v___y_3148_, sizeof(void*)*10);
v___x_3224_ = lean_box(v_suppressElabErrors_3223_);
v___f_3225_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3225_, 0, v___x_3224_);
v___x_3226_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3145_);
v___x_3227_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v___x_3226_, v___y_3149_);
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3241_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3241_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_inc_ref_n(v_fileMap_3222_, 2);
v___x_3232_ = l_Lean_FileMap_toPosition(v_fileMap_3222_, v___y_3217_);
lean_dec(v___y_3217_);
v___x_3233_ = l_Lean_FileMap_toPosition(v_fileMap_3222_, v___y_3220_);
lean_dec(v___y_3220_);
v___x_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3223_ == 0)
{
lean_del_object(v___x_3230_);
lean_dec_ref(v___f_3225_);
v___y_3152_ = v___y_3218_;
v___y_3153_ = v___y_3219_;
v___y_3154_ = v_a_3228_;
v___y_3155_ = v___x_3235_;
v___y_3156_ = v___x_3234_;
v___y_3157_ = v_fileName_3221_;
v___y_3158_ = v___x_3232_;
v___y_3159_ = v___y_3149_;
goto v___jp_3151_;
}
else
{
uint8_t v___x_3236_; 
lean_inc(v_a_3228_);
v___x_3236_ = l_Lean_MessageData_hasTag(v___f_3225_, v_a_3228_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_dec_ref_known(v___x_3234_, 1);
lean_dec_ref(v___x_3232_);
lean_dec(v_a_3228_);
v___x_3237_ = lean_box(0);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v___x_3237_);
v___x_3239_ = v___x_3230_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
else
{
lean_del_object(v___x_3230_);
v___y_3152_ = v___y_3218_;
v___y_3153_ = v___y_3219_;
v___y_3154_ = v_a_3228_;
v___y_3155_ = v___x_3235_;
v___y_3156_ = v___x_3234_;
v___y_3157_ = v_fileName_3221_;
v___y_3158_ = v___x_3232_;
v___y_3159_ = v___y_3149_;
goto v___jp_3151_;
}
}
}
}
v___jp_3242_:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_Syntax_getTailPos_x3f(v___y_3245_, v___y_3244_);
lean_dec(v___y_3245_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_inc(v___y_3246_);
v___y_3217_ = v___y_3246_;
v___y_3218_ = v___y_3243_;
v___y_3219_ = v___y_3244_;
v___y_3220_ = v___y_3246_;
goto v___jp_3216_;
}
else
{
lean_object* v_val_3248_; 
v_val_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_val_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v___y_3217_ = v___y_3246_;
v___y_3218_ = v___y_3243_;
v___y_3219_ = v___y_3244_;
v___y_3220_ = v_val_3248_;
goto v___jp_3216_;
}
}
v___jp_3249_:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Lean_Elab_Command_getRef___redArg(v___y_3148_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v_ref_3254_; lean_object* v___x_3255_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
v_ref_3254_ = l_Lean_replaceRef(v_ref_3144_, v_a_3253_);
lean_dec(v_a_3253_);
v___x_3255_ = l_Lean_Syntax_getPos_x3f(v_ref_3254_, v___y_3250_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_unsigned_to_nat(0u);
v___y_3243_ = v___y_3251_;
v___y_3244_ = v___y_3250_;
v___y_3245_ = v_ref_3254_;
v___y_3246_ = v___x_3256_;
goto v___jp_3242_;
}
else
{
lean_object* v_val_3257_; 
v_val_3257_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_val_3257_);
lean_dec_ref_known(v___x_3255_, 1);
v___y_3243_ = v___y_3251_;
v___y_3244_ = v___y_3250_;
v___y_3245_ = v_ref_3254_;
v___y_3246_ = v_val_3257_;
goto v___jp_3242_;
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v_msgData_3145_);
v_a_3258_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3252_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3252_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
v___jp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v_scopes_3271_; lean_object* v___x_3272_; lean_object* v_opts_3273_; uint8_t v___x_3274_; uint8_t v___x_3275_; 
v___x_3269_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3270_ = lean_st_ref_get(v___y_3149_);
v_scopes_3271_ = lean_ctor_get(v___x_3270_, 2);
lean_inc(v_scopes_3271_);
lean_dec(v___x_3270_);
v___x_3272_ = l_List_head_x21___redArg(v___x_3269_, v_scopes_3271_);
lean_dec(v_scopes_3271_);
v_opts_3273_ = lean_ctor_get(v___x_3272_, 1);
lean_inc_ref(v_opts_3273_);
lean_dec(v___x_3272_);
v___x_3274_ = 1;
v___x_3275_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3146_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_dec_ref(v_opts_3273_);
v___y_3250_ = v___y_3268_;
v___y_3251_ = v_severity_3146_;
goto v___jp_3249_;
}
else
{
lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = l_Lean_warningAsError;
v___x_3277_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3273_, v___x_3276_);
lean_dec_ref(v_opts_3273_);
if (v___x_3277_ == 0)
{
v___y_3250_ = v___y_3268_;
v___y_3251_ = v_severity_3146_;
goto v___jp_3249_;
}
else
{
v___y_3250_ = v___y_3268_;
v___y_3251_ = v___x_3266_;
goto v___jp_3249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3282_, lean_object* v_msgData_3283_, lean_object* v_severity_3284_, lean_object* v_isSilent_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
uint8_t v_severity_boxed_3289_; uint8_t v_isSilent_boxed_3290_; lean_object* v_res_3291_; 
v_severity_boxed_3289_ = lean_unbox(v_severity_3284_);
v_isSilent_boxed_3290_ = lean_unbox(v_isSilent_3285_);
v_res_3291_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3282_, v_msgData_3283_, v_severity_boxed_3289_, v_isSilent_boxed_3290_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v_ref_3282_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3292_, lean_object* v_msgData_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = 0;
v___x_3298_ = 0;
v___x_3299_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3292_, v_msgData_3293_, v___x_3297_, v___x_3298_, v___y_3294_, v___y_3295_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3300_, lean_object* v_msgData_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3300_, v_msgData_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v_ref_3300_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3307_, lean_object* v_x_3308_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3310_ = lean_string_append(v___x_3309_, v___x_3307_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3311_, lean_object* v_x_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3311_, v_x_3312_);
lean_dec_ref(v_x_3312_);
lean_dec_ref(v___x_3311_);
return v_res_3313_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3323_, uint8_t v___x_3324_, lean_object* v___x_3325_, lean_object* v_insertPos_3326_, lean_object* v_cmdLine_3327_, lean_object* v_ref_3328_, size_t v_sz_3329_, size_t v_i_3330_, lean_object* v_bs_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_lt(v_i_3330_, v_sz_3329_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_dec_ref(v___x_3325_);
lean_dec_ref(v___x_3323_);
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_bs_3331_);
return v___x_3336_;
}
else
{
lean_object* v_v_3337_; lean_object* v___x_3338_; lean_object* v_bs_x27_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_v_3337_ = lean_array_uget(v_bs_3331_, v_i_3330_);
v___x_3338_ = lean_unsigned_to_nat(0u);
v_bs_x27_3339_ = lean_array_uset(v_bs_3331_, v_i_3330_, v___x_3338_);
lean_inc(v_v_3337_);
v___x_3340_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3340_, 0, v_v_3337_);
v___x_3341_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3340_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___f_3345_; lean_object* v___x_3346_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = l_Std_Format_defWidth;
v___x_3344_ = l_Std_Format_pretty(v_a_3342_, v___x_3343_, v___x_3338_, v___x_3338_);
lean_inc_ref(v___x_3344_);
v___f_3345_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3345_, 0, v___x_3344_);
lean_inc_ref(v___x_3323_);
v___x_3346_ = lean_string_append(v___x_3323_, v___x_3344_);
lean_dec_ref(v___x_3344_);
if (v___x_3324_ == 0)
{
goto v___jp_3347_;
}
else
{
lean_object* v___x_3358_; lean_object* v_line_3359_; lean_object* v_column_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3395_; 
lean_inc_ref(v___x_3325_);
v___x_3358_ = l_Lean_FileMap_toPosition(v___x_3325_, v_insertPos_3326_);
v_line_3359_ = lean_ctor_get(v___x_3358_, 0);
v_column_3360_ = lean_ctor_get(v___x_3358_, 1);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3362_ = v___x_3358_;
v_isShared_3363_ = v_isSharedCheck_3395_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_column_3360_);
lean_inc(v_line_3359_);
lean_dec(v___x_3358_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3395_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3364_ = lean_nat_sub(v_line_3359_, v_cmdLine_3327_);
lean_dec(v_line_3359_);
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = lean_nat_add(v___x_3364_, v___x_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3346_);
v___x_3368_ = l_String_quote(v___x_3346_);
v___x_3369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
v___x_3370_ = l_Lean_MessageData_ofFormat(v___x_3369_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set_tag(v___x_3362_, 7);
lean_ctor_set(v___x_3362_, 1, v___x_3370_);
lean_ctor_set(v___x_3362_, 0, v___x_3367_);
v___x_3372_ = v___x_3362_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3373_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Nat_reprFast(v___x_3366_);
v___x_3376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
v___x_3377_ = l_Lean_MessageData_ofFormat(v___x_3376_);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3374_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = l_Nat_reprFast(v_column_3360_);
v___x_3382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
v___x_3383_ = l_Lean_MessageData_ofFormat(v___x_3382_);
v___x_3384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3380_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3328_, v___x_3384_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_dec_ref_known(v___x_3385_, 1);
goto v___jp_3347_;
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec_ref(v___x_3346_);
lean_dec_ref(v___f_3345_);
lean_dec_ref(v_bs_x27_3339_);
lean_dec(v_v_3337_);
lean_dec_ref(v___x_3325_);
lean_dec_ref(v___x_3323_);
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
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
v___jp_3347_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; size_t v___x_3354_; size_t v___x_3355_; lean_object* v___x_3356_; 
v___x_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
v___x_3349_ = lean_box(0);
v___x_3350_ = l_Lean_MessageData_ofSyntax(v_v_3337_);
v___x_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___f_3345_);
v___x_3353_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3348_);
lean_ctor_set(v___x_3353_, 1, v___x_3349_);
lean_ctor_set(v___x_3353_, 2, v___x_3349_);
lean_ctor_set(v___x_3353_, 3, v___x_3349_);
lean_ctor_set(v___x_3353_, 4, v___x_3351_);
lean_ctor_set(v___x_3353_, 5, v___x_3352_);
v___x_3354_ = ((size_t)1ULL);
v___x_3355_ = lean_usize_add(v_i_3330_, v___x_3354_);
v___x_3356_ = lean_array_uset(v_bs_x27_3339_, v_i_3330_, v___x_3353_);
v_i_3330_ = v___x_3355_;
v_bs_3331_ = v___x_3356_;
goto _start;
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v_bs_x27_3339_);
lean_dec(v_v_3337_);
lean_dec_ref(v___x_3325_);
lean_dec_ref(v___x_3323_);
v_a_3396_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3341_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3341_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3404_, lean_object* v___x_3405_, lean_object* v___x_3406_, lean_object* v_insertPos_3407_, lean_object* v_cmdLine_3408_, lean_object* v_ref_3409_, lean_object* v_sz_3410_, lean_object* v_i_3411_, lean_object* v_bs_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
uint8_t v___x_3853__boxed_3416_; size_t v_sz_boxed_3417_; size_t v_i_boxed_3418_; lean_object* v_res_3419_; 
v___x_3853__boxed_3416_ = lean_unbox(v___x_3405_);
v_sz_boxed_3417_ = lean_unbox_usize(v_sz_3410_);
lean_dec(v_sz_3410_);
v_i_boxed_3418_ = lean_unbox_usize(v_i_3411_);
lean_dec(v_i_3411_);
v_res_3419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3404_, v___x_3853__boxed_3416_, v___x_3406_, v_insertPos_3407_, v_cmdLine_3408_, v_ref_3409_, v_sz_boxed_3417_, v_i_boxed_3418_, v_bs_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v_ref_3409_);
lean_dec(v_cmdLine_3408_);
lean_dec(v_insertPos_3407_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3420_, lean_object* v_ref_3421_, lean_object* v_insertPos_3422_, lean_object* v_suggs_3423_, lean_object* v_cmdLine_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3428_ = lean_array_get_size(v_suggs_3423_);
v___x_3429_ = lean_unsigned_to_nat(0u);
v___x_3430_ = lean_nat_dec_eq(v___x_3428_, v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v_fileMap_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v_scopes_3437_; lean_object* v___x_3438_; lean_object* v_opts_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; size_t v_sz_3442_; size_t v___x_3443_; lean_object* v___x_3444_; 
v_fileMap_3431_ = lean_ctor_get(v_a_3425_, 1);
v___x_3432_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_inc_ref_n(v_fileMap_3431_, 2);
v___x_3433_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3420_, v_fileMap_3431_);
lean_inc(v_insertPos_3422_);
v___x_3434_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3422_);
v___x_3435_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3436_ = lean_st_ref_get(v_a_3426_);
v_scopes_3437_ = lean_ctor_get(v___x_3436_, 2);
lean_inc(v_scopes_3437_);
lean_dec(v___x_3436_);
v___x_3438_ = l_List_head_x21___redArg(v___x_3435_, v_scopes_3437_);
lean_dec(v_scopes_3437_);
v_opts_3439_ = lean_ctor_get(v___x_3438_, 1);
lean_inc_ref(v_opts_3439_);
lean_dec(v___x_3438_);
v___x_3440_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3441_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3439_, v___x_3440_);
lean_dec_ref(v_opts_3439_);
v_sz_3442_ = lean_array_size(v_suggs_3423_);
v___x_3443_ = ((size_t)0ULL);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3433_, v___x_3441_, v_fileMap_3431_, v_insertPos_3422_, v_cmdLine_3424_, v_ref_3421_, v_sz_3442_, v___x_3443_, v_suggs_3423_, v_a_3425_, v_a_3426_);
lean_dec(v_insertPos_3422_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___y_3450_; lean_object* v___x_3451_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3444_, 1);
v___x_3446_ = lean_array_get_size(v_a_3445_);
v___x_3447_ = lean_unsigned_to_nat(1u);
v___x_3448_ = lean_nat_dec_eq(v___x_3446_, v___x_3447_);
v___x_3449_ = lean_box(v___x_3448_);
v___y_3450_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3450_, 0, v___x_3449_);
lean_closure_set(v___y_3450_, 1, v___x_3434_);
lean_closure_set(v___y_3450_, 2, v_ref_3421_);
lean_closure_set(v___y_3450_, 3, v_a_3445_);
lean_closure_set(v___y_3450_, 4, v___x_3432_);
lean_closure_set(v___y_3450_, 5, v___x_3429_);
v___x_3451_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3450_, v_a_3425_, v_a_3426_);
return v___x_3451_;
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v___x_3434_);
lean_dec(v_ref_3421_);
v_a_3452_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3444_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3444_);
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
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec_ref(v_suggs_3423_);
lean_dec(v_insertPos_3422_);
lean_dec(v_ref_3421_);
v___x_3460_ = lean_box(0);
v___x_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
return v___x_3461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3462_, lean_object* v_ref_3463_, lean_object* v_insertPos_3464_, lean_object* v_suggs_3465_, lean_object* v_cmdLine_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3462_, v_ref_3463_, v_insertPos_3464_, v_suggs_3465_, v_cmdLine_3466_, v_a_3467_, v_a_3468_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
lean_dec(v_cmdLine_3466_);
lean_dec(v_tacticSeq_3462_);
return v_res_3470_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3471_){
_start:
{
uint8_t v___x_3472_; 
v___x_3472_ = 0;
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3473_){
_start:
{
uint8_t v_res_3474_; lean_object* v_r_3475_; 
v_res_3474_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3473_);
lean_dec(v_x_3473_);
v_r_3475_ = lean_box(v_res_3474_);
return v_r_3475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Array_mkArray0___redArg();
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3496_, lean_object* v_ref_3497_, lean_object* v_goal_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_toCold_3507_; lean_object* v_currRecDepth_3508_; lean_object* v_ref_3509_; uint16_t v_optionFlags_3510_; uint8_t v_suppressElabErrors_3511_; uint8_t v_checkDeprecated_3512_; uint8_t v_isRecordingDeps_3513_; uint8_t v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v_ref_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v_toCold_3507_ = lean_ctor_get(v___y_3501_, 0);
v_currRecDepth_3508_ = lean_ctor_get(v___y_3501_, 1);
v_ref_3509_ = lean_ctor_get(v___y_3501_, 2);
v_optionFlags_3510_ = lean_ctor_get_uint16(v___y_3501_, sizeof(void*)*3);
v_suppressElabErrors_3511_ = lean_ctor_get_uint8(v___y_3501_, sizeof(void*)*3 + 2);
v_checkDeprecated_3512_ = lean_ctor_get_uint8(v___y_3501_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3513_ = lean_ctor_get_uint8(v___y_3501_, sizeof(void*)*3 + 4);
v___x_3514_ = 0;
v___x_3515_ = l_Lean_SourceInfo_fromRef(v_ref_3509_, v___x_3514_);
v___x_3516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0));
lean_inc_n(v___x_3515_, 3);
v___x_3517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3515_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
v___x_3518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
v___x_3519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3520_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5);
v___x_3521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3515_);
lean_ctor_set(v___x_3521_, 1, v___x_3519_);
lean_ctor_set(v___x_3521_, 2, v___x_3520_);
v___x_3522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7));
v___x_3523_ = l_Lean_Syntax_node1(v___x_3515_, v___x_3522_, v___x_3521_);
v___x_3524_ = l_Lean_Syntax_node2(v___x_3515_, v___x_3518_, v___x_3517_, v___x_3523_);
v___x_3525_ = lean_box(0);
v___x_3526_ = lean_box(0);
v___x_3527_ = 1;
v___x_3528_ = lean_box(1);
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3530_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_3530_, 0, v___x_3525_);
lean_ctor_set(v___x_3530_, 1, v___x_3526_);
lean_ctor_set(v___x_3530_, 2, v___x_3525_);
lean_ctor_set(v___x_3530_, 3, v___f_3496_);
lean_ctor_set(v___x_3530_, 4, v___x_3528_);
lean_ctor_set(v___x_3530_, 5, v___x_3528_);
lean_ctor_set(v___x_3530_, 6, v___x_3525_);
lean_ctor_set(v___x_3530_, 7, v___x_3529_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8, v___x_3527_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 1, v___x_3527_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 2, v___x_3527_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 3, v___x_3527_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 4, v___x_3514_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 5, v___x_3514_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 6, v___x_3514_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 7, v___x_3514_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 8, v___x_3527_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*8 + 9, v___x_3514_);
v___x_3531_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v___x_3532_ = lean_box(0);
v_ref_3533_ = l_Lean_replaceRef(v_ref_3497_, v_ref_3509_);
lean_inc(v_currRecDepth_3508_);
lean_inc_ref(v_toCold_3507_);
v___x_3534_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3534_, 0, v_toCold_3507_);
lean_ctor_set(v___x_3534_, 1, v_currRecDepth_3508_);
lean_ctor_set(v___x_3534_, 2, v_ref_3533_);
lean_ctor_set_uint16(v___x_3534_, sizeof(void*)*3, v_optionFlags_3510_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 2, v_suppressElabErrors_3511_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 3, v_checkDeprecated_3512_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 4, v_isRecordingDeps_3513_);
v___x_3535_ = l_Lean_Elab_runTactic(v_goal_3498_, v___x_3524_, v___x_3530_, v___x_3531_, v___y_3499_, v___y_3500_, v___x_3534_, v___y_3502_);
lean_dec_ref_known(v___x_3534_, 3);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v___x_3535_, 0);
lean_dec(v_unused_3543_);
v___x_3537_ = v___x_3535_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v___x_3535_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3532_);
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3532_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3564_; 
v_a_3544_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3546_ = v___x_3535_;
v_isShared_3547_ = v_isSharedCheck_3564_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3535_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3564_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
lean_inc(v_a_3544_);
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
uint8_t v___x_3550_; 
v___x_3550_ = l_Lean_Exception_isInterrupt(v_a_3544_);
if (v___x_3550_ == 0)
{
uint8_t v___x_3551_; 
lean_inc(v_a_3544_);
v___x_3551_ = l_Lean_Exception_isRuntime(v_a_3544_);
if (v___x_3551_ == 0)
{
uint8_t v___x_3552_; 
lean_inc(v_a_3544_);
v___x_3552_ = l_Lean_Exception_isMaxRecDepth(v_a_3544_);
if (v___x_3552_ == 0)
{
lean_object* v_options_3553_; uint8_t v_hasTrace_3554_; 
lean_dec_ref(v___x_3549_);
v_options_3553_ = lean_ctor_get(v_toCold_3507_, 2);
v_hasTrace_3554_ = lean_ctor_get_uint8(v_options_3553_, sizeof(void*)*1);
if (v_hasTrace_3554_ == 0)
{
lean_dec(v_a_3544_);
goto v___jp_3504_;
}
else
{
lean_object* v_inheritedTraceOptions_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v_inheritedTraceOptions_3555_ = lean_ctor_get(v_toCold_3507_, 11);
v___x_3556_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3557_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3555_, v_options_3553_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_dec(v_a_3544_);
goto v___jp_3504_;
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3559_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3560_ = l_Lean_Exception_toMessageData(v_a_3544_);
v___x_3561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3559_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v___x_3562_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3556_, v___x_3561_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
return v___x_3562_;
}
}
}
else
{
lean_dec(v_a_3544_);
return v___x_3549_;
}
}
else
{
lean_dec(v_a_3544_);
return v___x_3549_;
}
}
else
{
lean_dec(v_a_3544_);
return v___x_3549_;
}
}
}
}
v___jp_3504_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_box(0);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3565_, lean_object* v_ref_3566_, lean_object* v_goal_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3565_, v_ref_3566_, v_goal_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v_ref_3566_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v_mctx_3579_; lean_object* v_ref_3580_; lean_object* v_env_3581_; lean_object* v_opts_3582_; lean_object* v_namingCtx_3583_; lean_object* v_goal_3584_; lean_object* v_decls_3585_; lean_object* v___x_3586_; 
v_mctx_3579_ = lean_ctor_get(v_c_3575_, 3);
lean_inc_ref(v_mctx_3579_);
v_ref_3580_ = lean_ctor_get(v_c_3575_, 1);
lean_inc(v_ref_3580_);
v_env_3581_ = lean_ctor_get(v_c_3575_, 2);
lean_inc_ref(v_env_3581_);
v_opts_3582_ = lean_ctor_get(v_c_3575_, 4);
lean_inc_ref(v_opts_3582_);
v_namingCtx_3583_ = lean_ctor_get(v_c_3575_, 5);
lean_inc_ref(v_namingCtx_3583_);
v_goal_3584_ = lean_ctor_get(v_c_3575_, 6);
lean_inc(v_goal_3584_);
lean_dec_ref(v_c_3575_);
v_decls_3585_ = lean_ctor_get(v_mctx_3579_, 5);
v___x_3586_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3585_, v_goal_3584_);
if (lean_obj_tag(v___x_3586_) == 1)
{
lean_object* v_val_3587_; lean_object* v_lctx_3588_; lean_object* v___f_3589_; lean_object* v___f_3590_; lean_object* v___x_3591_; 
v_val_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_val_3587_);
lean_dec_ref_known(v___x_3586_, 1);
v_lctx_3588_ = lean_ctor_get(v_val_3587_, 1);
lean_inc_ref(v_lctx_3588_);
lean_dec(v_val_3587_);
v___f_3589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3590_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3590_, 0, v___f_3589_);
lean_closure_set(v___f_3590_, 1, v_ref_3580_);
lean_closure_set(v___f_3590_, 2, v_goal_3584_);
v___x_3591_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3581_, v_mctx_3579_, v_lctx_3588_, v_opts_3582_, v_namingCtx_3583_, v___f_3590_, v_a_3576_, v_a_3577_);
return v___x_3591_;
}
else
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec(v___x_3586_);
lean_dec(v_goal_3584_);
lean_dec_ref(v_namingCtx_3583_);
lean_dec_ref(v_opts_3582_);
lean_dec_ref(v_env_3581_);
lean_dec(v_ref_3580_);
lean_dec_ref(v_mctx_3579_);
v___x_3592_ = lean_box(0);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3594_, v_a_3595_, v_a_3596_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
return v_res_3598_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3599_, lean_object* v_val_3600_, lean_object* v_as_3601_, size_t v_i_3602_, size_t v_stop_3603_){
_start:
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_usize_dec_eq(v_i_3602_, v_stop_3603_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; lean_object* v_pos_3610_; uint8_t v_severity_3611_; lean_object* v_data_3612_; lean_object* v___f_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; uint8_t v___y_3618_; 
v___x_3609_ = lean_array_uget_borrowed(v_as_3601_, v_i_3602_);
v_pos_3610_ = lean_ctor_get(v___x_3609_, 1);
v_severity_3611_ = lean_ctor_get_uint8(v___x_3609_, sizeof(void*)*5 + 1);
v_data_3612_ = lean_ctor_get(v___x_3609_, 4);
v___f_3613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
v___x_3614_ = 1;
lean_inc_ref(v_pos_3610_);
v___x_3615_ = l_Lean_FileMap_ofPosition(v___x_3599_, v_pos_3610_);
v___x_3616_ = l_Lean_Syntax_Range_contains(v_val_3600_, v___x_3615_, v___x_3614_);
lean_dec(v___x_3615_);
if (v_severity_3611_ == 2)
{
v___y_3618_ = v___x_3614_;
goto v___jp_3617_;
}
else
{
v___y_3618_ = v___x_3608_;
goto v___jp_3617_;
}
v___jp_3617_:
{
if (v___x_3616_ == 0)
{
goto v___jp_3604_;
}
else
{
if (v___y_3618_ == 0)
{
goto v___jp_3604_;
}
else
{
uint8_t v___x_3619_; 
lean_inc(v_data_3612_);
v___x_3619_ = l_Lean_MessageData_hasTag(v___f_3613_, v_data_3612_);
if (v___x_3619_ == 0)
{
return v___x_3614_;
}
else
{
goto v___jp_3604_;
}
}
}
}
}
else
{
uint8_t v___x_3620_; 
v___x_3620_ = 0;
return v___x_3620_;
}
v___jp_3604_:
{
size_t v___x_3605_; size_t v___x_3606_; 
v___x_3605_ = ((size_t)1ULL);
v___x_3606_ = lean_usize_add(v_i_3602_, v___x_3605_);
v_i_3602_ = v___x_3606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3621_, lean_object* v_val_3622_, lean_object* v_as_3623_, lean_object* v_i_3624_, lean_object* v_stop_3625_){
_start:
{
size_t v_i_boxed_3626_; size_t v_stop_boxed_3627_; uint8_t v_res_3628_; lean_object* v_r_3629_; 
v_i_boxed_3626_ = lean_unbox_usize(v_i_3624_);
lean_dec(v_i_3624_);
v_stop_boxed_3627_ = lean_unbox_usize(v_stop_3625_);
lean_dec(v_stop_3625_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3621_, v_val_3622_, v_as_3623_, v_i_boxed_3626_, v_stop_boxed_3627_);
lean_dec_ref(v_as_3623_);
lean_dec_ref(v_val_3622_);
lean_dec_ref(v___x_3621_);
v_r_3629_ = lean_box(v_res_3628_);
return v_r_3629_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3630_, lean_object* v_val_3631_, lean_object* v_x_3632_){
_start:
{
if (lean_obj_tag(v_x_3632_) == 0)
{
lean_object* v_cs_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v_cs_3633_ = lean_ctor_get(v_x_3632_, 0);
v___x_3634_ = lean_unsigned_to_nat(0u);
v___x_3635_ = lean_array_get_size(v_cs_3633_);
v___x_3636_ = lean_nat_dec_lt(v___x_3634_, v___x_3635_);
if (v___x_3636_ == 0)
{
return v___x_3636_;
}
else
{
size_t v___x_3637_; size_t v___x_3638_; uint8_t v___x_3639_; 
v___x_3637_ = ((size_t)0ULL);
v___x_3638_ = lean_usize_of_nat(v___x_3635_);
v___x_3639_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3630_, v_val_3631_, v_cs_3633_, v___x_3637_, v___x_3638_);
return v___x_3639_;
}
}
else
{
lean_object* v_vs_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
v_vs_3640_ = lean_ctor_get(v_x_3632_, 0);
v___x_3641_ = lean_unsigned_to_nat(0u);
v___x_3642_ = lean_array_get_size(v_vs_3640_);
v___x_3643_ = lean_nat_dec_lt(v___x_3641_, v___x_3642_);
if (v___x_3643_ == 0)
{
return v___x_3643_;
}
else
{
size_t v___x_3644_; size_t v___x_3645_; uint8_t v___x_3646_; 
v___x_3644_ = ((size_t)0ULL);
v___x_3645_ = lean_usize_of_nat(v___x_3642_);
v___x_3646_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3630_, v_val_3631_, v_vs_3640_, v___x_3644_, v___x_3645_);
return v___x_3646_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3647_, lean_object* v_val_3648_, lean_object* v_as_3649_, size_t v_i_3650_, size_t v_stop_3651_){
_start:
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_usize_dec_eq(v_i_3650_, v_stop_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = lean_array_uget_borrowed(v_as_3649_, v_i_3650_);
v___x_3654_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3647_, v_val_3648_, v___x_3653_);
if (v___x_3654_ == 0)
{
size_t v___x_3655_; size_t v___x_3656_; 
v___x_3655_ = ((size_t)1ULL);
v___x_3656_ = lean_usize_add(v_i_3650_, v___x_3655_);
v_i_3650_ = v___x_3656_;
goto _start;
}
else
{
return v___x_3654_;
}
}
else
{
uint8_t v___x_3658_; 
v___x_3658_ = 0;
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3659_, lean_object* v_val_3660_, lean_object* v_as_3661_, lean_object* v_i_3662_, lean_object* v_stop_3663_){
_start:
{
size_t v_i_boxed_3664_; size_t v_stop_boxed_3665_; uint8_t v_res_3666_; lean_object* v_r_3667_; 
v_i_boxed_3664_ = lean_unbox_usize(v_i_3662_);
lean_dec(v_i_3662_);
v_stop_boxed_3665_ = lean_unbox_usize(v_stop_3663_);
lean_dec(v_stop_3663_);
v_res_3666_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3659_, v_val_3660_, v_as_3661_, v_i_boxed_3664_, v_stop_boxed_3665_);
lean_dec_ref(v_as_3661_);
lean_dec_ref(v_val_3660_);
lean_dec_ref(v___x_3659_);
v_r_3667_ = lean_box(v_res_3666_);
return v_r_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3668_, lean_object* v_val_3669_, lean_object* v_x_3670_){
_start:
{
uint8_t v_res_3671_; lean_object* v_r_3672_; 
v_res_3671_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3668_, v_val_3669_, v_x_3670_);
lean_dec_ref(v_x_3670_);
lean_dec_ref(v_val_3669_);
lean_dec_ref(v___x_3668_);
v_r_3672_ = lean_box(v_res_3671_);
return v_r_3672_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3673_, lean_object* v_val_3674_, lean_object* v_t_3675_){
_start:
{
lean_object* v_root_3676_; lean_object* v_tail_3677_; uint8_t v___x_3678_; 
v_root_3676_ = lean_ctor_get(v_t_3675_, 0);
v_tail_3677_ = lean_ctor_get(v_t_3675_, 1);
v___x_3678_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3673_, v_val_3674_, v_root_3676_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = lean_array_get_size(v_tail_3677_);
v___x_3681_ = lean_nat_dec_lt(v___x_3679_, v___x_3680_);
if (v___x_3681_ == 0)
{
return v___x_3681_;
}
else
{
size_t v___x_3682_; size_t v___x_3683_; uint8_t v___x_3684_; 
v___x_3682_ = ((size_t)0ULL);
v___x_3683_ = lean_usize_of_nat(v___x_3680_);
v___x_3684_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3673_, v_val_3674_, v_tail_3677_, v___x_3682_, v___x_3683_);
return v___x_3684_;
}
}
else
{
return v___x_3678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3685_, lean_object* v_val_3686_, lean_object* v_t_3687_){
_start:
{
uint8_t v_res_3688_; lean_object* v_r_3689_; 
v_res_3688_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3685_, v_val_3686_, v_t_3687_);
lean_dec_ref(v_t_3687_);
lean_dec_ref(v_val_3686_);
lean_dec_ref(v___x_3685_);
v_r_3689_ = lean_box(v_res_3688_);
return v_r_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_){
_start:
{
uint8_t v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = 0;
v___x_3695_ = l_Lean_Syntax_getRange_x3f(v_stx_3690_, v___x_3694_);
if (lean_obj_tag(v___x_3695_) == 1)
{
lean_object* v_val_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3709_; 
v_val_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3709_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_val_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3709_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v_fileMap_3700_; lean_object* v___x_3701_; lean_object* v_messages_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
v_fileMap_3700_ = lean_ctor_get(v_a_3691_, 1);
v___x_3701_ = lean_st_ref_get(v_a_3692_);
v_messages_3702_ = lean_ctor_get(v___x_3701_, 1);
lean_inc_ref(v_messages_3702_);
lean_dec(v___x_3701_);
v___x_3703_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3702_);
v___x_3704_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3700_, v_val_3696_, v___x_3703_);
lean_dec_ref(v___x_3703_);
lean_dec(v_val_3696_);
v___x_3705_ = lean_box(v___x_3704_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set_tag(v___x_3698_, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3705_);
v___x_3707_ = v___x_3698_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
lean_dec(v___x_3695_);
v___x_3710_ = lean_box(v___x_3694_);
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3712_, v_a_3713_, v_a_3714_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_stx_3712_);
return v_res_3716_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3717_, lean_object* v_fileMap_3718_, lean_object* v_c_3719_){
_start:
{
lean_object* v___y_3721_; lean_object* v_kind_3725_; lean_object* v_ref_3726_; lean_object* v___y_3728_; 
v_kind_3725_ = lean_ctor_get(v_c_3719_, 0);
lean_inc(v_kind_3725_);
v_ref_3726_ = lean_ctor_get(v_c_3719_, 1);
lean_inc(v_ref_3726_);
lean_dec_ref(v_c_3719_);
if (lean_obj_tag(v_kind_3725_) == 0)
{
lean_object* v_insertPos_3744_; 
lean_dec(v_ref_3726_);
v_insertPos_3744_ = lean_ctor_get(v_kind_3725_, 1);
lean_inc(v_insertPos_3744_);
v___y_3728_ = v_insertPos_3744_;
goto v___jp_3727_;
}
else
{
uint8_t v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = 0;
v___x_3746_ = l_Lean_Syntax_getPos_x3f(v_ref_3726_, v___x_3745_);
lean_dec(v_ref_3726_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v___x_3747_; 
v___x_3747_ = lean_unsigned_to_nat(0u);
v___y_3728_ = v___x_3747_;
goto v___jp_3727_;
}
else
{
lean_object* v_val_3748_; 
v_val_3748_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_val_3748_);
lean_dec_ref_known(v___x_3746_, 1);
v___y_3728_ = v_val_3748_;
goto v___jp_3727_;
}
}
v___jp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3722_ = l_List_lengthTR___redArg(v___y_3721_);
lean_dec(v___y_3721_);
v___x_3723_ = lean_unsigned_to_nat(1u);
v___x_3724_ = lean_nat_dec_eq(v___x_3722_, v___x_3723_);
lean_dec(v___x_3722_);
return v___x_3724_;
}
v___jp_3727_:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3718_, v_tree_3717_, v___y_3728_);
if (lean_obj_tag(v___x_3729_) == 1)
{
lean_object* v_tail_3730_; 
v_tail_3730_ = lean_ctor_get(v___x_3729_, 1);
if (lean_obj_tag(v_tail_3730_) == 0)
{
if (lean_obj_tag(v_kind_3725_) == 0)
{
lean_object* v_head_3731_; lean_object* v_tacticSeq_3732_; uint8_t v___x_3733_; lean_object* v___x_3734_; 
v_head_3731_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_head_3731_);
lean_dec_ref_known(v___x_3729_, 2);
v_tacticSeq_3732_ = lean_ctor_get(v_kind_3725_, 0);
lean_inc(v_tacticSeq_3732_);
lean_dec_ref_known(v_kind_3725_, 2);
v___x_3733_ = 0;
v___x_3734_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3732_, v___x_3733_);
lean_dec(v_tacticSeq_3732_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_tacticInfo_3735_; lean_object* v_goalsBefore_3736_; 
v_tacticInfo_3735_ = lean_ctor_get(v_head_3731_, 1);
lean_inc_ref(v_tacticInfo_3735_);
lean_dec(v_head_3731_);
v_goalsBefore_3736_ = lean_ctor_get(v_tacticInfo_3735_, 2);
lean_inc(v_goalsBefore_3736_);
lean_dec_ref(v_tacticInfo_3735_);
v___y_3721_ = v_goalsBefore_3736_;
goto v___jp_3720_;
}
else
{
lean_object* v_tacticInfo_3737_; lean_object* v_goalsAfter_3738_; 
lean_dec_ref_known(v___x_3734_, 1);
v_tacticInfo_3737_ = lean_ctor_get(v_head_3731_, 1);
lean_inc_ref(v_tacticInfo_3737_);
lean_dec(v_head_3731_);
v_goalsAfter_3738_ = lean_ctor_get(v_tacticInfo_3737_, 4);
lean_inc(v_goalsAfter_3738_);
lean_dec_ref(v_tacticInfo_3737_);
v___y_3721_ = v_goalsAfter_3738_;
goto v___jp_3720_;
}
}
else
{
lean_object* v_head_3739_; lean_object* v_tacticInfo_3740_; lean_object* v_goalsBefore_3741_; 
v_head_3739_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_head_3739_);
lean_dec_ref_known(v___x_3729_, 2);
v_tacticInfo_3740_ = lean_ctor_get(v_head_3739_, 1);
lean_inc_ref(v_tacticInfo_3740_);
lean_dec(v_head_3739_);
v_goalsBefore_3741_ = lean_ctor_get(v_tacticInfo_3740_, 2);
lean_inc(v_goalsBefore_3741_);
lean_dec_ref(v_tacticInfo_3740_);
v___y_3721_ = v_goalsBefore_3741_;
goto v___jp_3720_;
}
}
else
{
uint8_t v___x_3742_; 
lean_dec_ref_known(v___x_3729_, 2);
lean_dec(v_kind_3725_);
v___x_3742_ = 0;
return v___x_3742_;
}
}
else
{
uint8_t v___x_3743_; 
lean_dec(v___x_3729_);
lean_dec(v_kind_3725_);
v___x_3743_ = 0;
return v___x_3743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3749_, lean_object* v_fileMap_3750_, lean_object* v_c_3751_){
_start:
{
uint8_t v_res_3752_; lean_object* v_r_3753_; 
v_res_3752_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3749_, v_fileMap_3750_, v_c_3751_);
v_r_3753_ = lean_box(v_res_3752_);
return v_r_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3756_; lean_object* v_infoState_3757_; lean_object* v_trees_3758_; lean_object* v___x_3759_; 
v___x_3756_ = lean_st_ref_get(v___y_3754_);
v_infoState_3757_ = lean_ctor_get(v___x_3756_, 8);
lean_inc_ref(v_infoState_3757_);
lean_dec(v___x_3756_);
v_trees_3758_ = lean_ctor_get(v_infoState_3757_, 2);
lean_inc_ref(v_trees_3758_);
lean_dec_ref(v_infoState_3757_);
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v_trees_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3760_);
lean_dec(v___y_3760_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3764_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
return v_res_3770_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3773_ = l_Lean_stringToMessageData(v___x_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3774_, lean_object* v___x_3775_, lean_object* v___x_3776_, lean_object* v_as_3777_, size_t v_sz_3778_, size_t v_i_3779_, lean_object* v_b_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_a_3785_; uint8_t v___x_3789_; 
v___x_3789_ = lean_usize_dec_lt(v_i_3779_, v_sz_3778_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; 
lean_dec_ref(v___x_3775_);
lean_dec_ref(v_tree_3774_);
v___x_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3790_, 0, v_b_3780_);
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; lean_object* v_a_3792_; uint8_t v___x_3793_; 
v___x_3791_ = lean_box(0);
v_a_3792_ = lean_array_uget_borrowed(v_as_3777_, v_i_3779_);
lean_inc(v_a_3792_);
lean_inc_ref(v___x_3775_);
lean_inc_ref(v_tree_3774_);
v___x_3793_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3774_, v___x_3775_, v_a_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v_scopes_3799_; lean_object* v___x_3800_; lean_object* v_opts_3801_; uint8_t v_hasTrace_3802_; 
v___x_3794_ = l_Lean_inheritedTraceOptions;
v___x_3795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3796_ = lean_st_ref_get(v___x_3794_);
v___x_3797_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3798_ = lean_st_ref_get(v___y_3782_);
v_scopes_3799_ = lean_ctor_get(v___x_3798_, 2);
lean_inc(v_scopes_3799_);
lean_dec(v___x_3798_);
v___x_3800_ = l_List_head_x21___redArg(v___x_3797_, v_scopes_3799_);
lean_dec(v_scopes_3799_);
v_opts_3801_ = lean_ctor_get(v___x_3800_, 1);
lean_inc_ref(v_opts_3801_);
lean_dec(v___x_3800_);
v_hasTrace_3802_ = lean_ctor_get_uint8(v_opts_3801_, sizeof(void*)*1);
if (v_hasTrace_3802_ == 0)
{
lean_dec_ref(v_opts_3801_);
lean_dec(v___x_3796_);
v_a_3785_ = v___x_3791_;
goto v___jp_3784_;
}
else
{
lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3803_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3796_, v_opts_3801_, v___x_3803_);
lean_dec_ref(v_opts_3801_);
lean_dec(v___x_3796_);
if (v___x_3804_ == 0)
{
v_a_3785_ = v___x_3791_;
goto v___jp_3784_;
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3806_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3795_, v___x_3805_, v___y_3781_, v___y_3782_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_dec_ref_known(v___x_3806_, 1);
v_a_3785_ = v___x_3791_;
goto v___jp_3784_;
}
else
{
lean_dec_ref(v___x_3775_);
lean_dec_ref(v_tree_3774_);
return v___x_3806_;
}
}
}
}
else
{
lean_object* v_kind_3807_; 
v_kind_3807_ = lean_ctor_get(v_a_3792_, 0);
if (lean_obj_tag(v_kind_3807_) == 0)
{
lean_object* v_ref_3808_; lean_object* v_tacticSeq_3809_; lean_object* v_insertPos_3810_; lean_object* v___x_3811_; 
v_ref_3808_ = lean_ctor_get(v_a_3792_, 1);
v_tacticSeq_3809_ = lean_ctor_get(v_kind_3807_, 0);
v_insertPos_3810_ = lean_ctor_get(v_kind_3807_, 1);
lean_inc(v_a_3792_);
v___x_3811_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3792_, v___y_3781_, v___y_3782_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3813_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3811_, 1);
lean_inc(v_insertPos_3810_);
lean_inc(v_ref_3808_);
v___x_3813_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3809_, v_ref_3808_, v_insertPos_3810_, v_a_3812_, v___x_3776_, v___y_3781_, v___y_3782_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_dec_ref_known(v___x_3813_, 1);
v_a_3785_ = v___x_3791_;
goto v___jp_3784_;
}
else
{
lean_dec_ref(v___x_3775_);
lean_dec_ref(v_tree_3774_);
return v___x_3813_;
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v___x_3775_);
lean_dec_ref(v_tree_3774_);
v_a_3814_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3811_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3811_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v___x_3822_; 
lean_inc(v_a_3792_);
v___x_3822_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3792_, v___y_3781_, v___y_3782_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_dec_ref_known(v___x_3822_, 1);
v_a_3785_ = v___x_3791_;
goto v___jp_3784_;
}
else
{
lean_dec_ref(v___x_3775_);
lean_dec_ref(v_tree_3774_);
return v___x_3822_;
}
}
}
}
v___jp_3784_:
{
size_t v___x_3786_; size_t v___x_3787_; 
v___x_3786_ = ((size_t)1ULL);
v___x_3787_ = lean_usize_add(v_i_3779_, v___x_3786_);
v_i_3779_ = v___x_3787_;
v_b_3780_ = v_a_3785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3823_, lean_object* v___x_3824_, lean_object* v___x_3825_, lean_object* v_as_3826_, lean_object* v_sz_3827_, lean_object* v_i_3828_, lean_object* v_b_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
size_t v_sz_boxed_3833_; size_t v_i_boxed_3834_; lean_object* v_res_3835_; 
v_sz_boxed_3833_ = lean_unbox_usize(v_sz_3827_);
lean_dec(v_sz_3827_);
v_i_boxed_3834_ = lean_unbox_usize(v_i_3828_);
lean_dec(v_i_3828_);
v_res_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3823_, v___x_3824_, v___x_3825_, v_as_3826_, v_sz_boxed_3833_, v_i_boxed_3834_, v_b_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v_as_3826_);
lean_dec(v___x_3825_);
return v_res_3835_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3841_ = l_Lean_stringToMessageData(v___x_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3842_, lean_object* v___x_3843_, lean_object* v___x_3844_, lean_object* v___x_3845_, lean_object* v___x_3846_, lean_object* v_as_3847_, size_t v_sz_3848_, size_t v_i_3849_, lean_object* v_b_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
uint8_t v___x_3854_; 
v___x_3854_ = lean_usize_dec_lt(v_i_3849_, v_sz_3848_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
lean_dec_ref(v___x_3845_);
lean_dec(v_stx_3842_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v_b_3850_);
return v___x_3855_;
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v_a_3859_; lean_object* v___x_3860_; 
lean_dec_ref(v_b_3850_);
v___x_3856_ = lean_box(0);
v___x_3857_ = l_Lean_inheritedTraceOptions;
v___x_3858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3859_ = lean_array_uget_borrowed(v_as_3847_, v_i_3849_);
lean_inc(v_a_3859_);
lean_inc(v_stx_3842_);
v___x_3860_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3842_, v___x_3843_, v_a_3859_, v___x_3844_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_scopes_3883_; lean_object* v___x_3884_; lean_object* v_opts_3885_; uint8_t v_hasTrace_3886_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3880_ = lean_st_ref_get(v___x_3857_);
v___x_3881_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3882_ = lean_st_ref_get(v___y_3852_);
v_scopes_3883_ = lean_ctor_get(v___x_3882_, 2);
lean_inc(v_scopes_3883_);
lean_dec(v___x_3882_);
v___x_3884_ = l_List_head_x21___redArg(v___x_3881_, v_scopes_3883_);
lean_dec(v_scopes_3883_);
v_opts_3885_ = lean_ctor_get(v___x_3884_, 1);
lean_inc_ref(v_opts_3885_);
lean_dec(v___x_3884_);
v_hasTrace_3886_ = lean_ctor_get_uint8(v_opts_3885_, sizeof(void*)*1);
if (v_hasTrace_3886_ == 0)
{
lean_dec_ref(v_opts_3885_);
lean_dec(v___x_3880_);
v___y_3863_ = v___y_3851_;
v___y_3864_ = v___y_3852_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3887_; uint8_t v___x_3888_; 
v___x_3887_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3888_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3880_, v_opts_3885_, v___x_3887_);
lean_dec_ref(v_opts_3885_);
lean_dec(v___x_3880_);
if (v___x_3888_ == 0)
{
v___y_3863_ = v___y_3851_;
v___y_3864_ = v___y_3852_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3890_ = lean_array_get_size(v_a_3861_);
v___x_3891_ = l_Nat_reprFast(v___x_3890_);
v___x_3892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
v___x_3893_ = l_Lean_MessageData_ofFormat(v___x_3892_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3889_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3858_, v___x_3894_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_dec_ref_known(v___x_3895_, 1);
v___y_3863_ = v___y_3851_;
v___y_3864_ = v___y_3852_;
goto v___jp_3862_;
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec(v_a_3861_);
lean_dec_ref(v___x_3845_);
lean_dec(v_stx_3842_);
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
v___jp_3862_:
{
size_t v_sz_3865_; size_t v___x_3866_; lean_object* v___x_3867_; 
v_sz_3865_ = lean_array_size(v_a_3861_);
v___x_3866_ = ((size_t)0ULL);
lean_inc_ref(v___x_3845_);
lean_inc(v_a_3859_);
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3859_, v___x_3845_, v___x_3846_, v_a_3861_, v_sz_3865_, v___x_3866_, v___x_3856_, v___y_3863_, v___y_3864_);
lean_dec(v_a_3861_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v___x_3868_; size_t v___x_3869_; size_t v___x_3870_; 
lean_dec_ref_known(v___x_3867_, 1);
v___x_3868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3869_ = ((size_t)1ULL);
v___x_3870_ = lean_usize_add(v_i_3849_, v___x_3869_);
v_i_3849_ = v___x_3870_;
v_b_3850_ = v___x_3868_;
goto _start;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec_ref(v___x_3845_);
lean_dec(v_stx_3842_);
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
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec_ref(v___x_3845_);
lean_dec(v_stx_3842_);
v_a_3904_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3860_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3860_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3912_, lean_object* v___x_3913_, lean_object* v___x_3914_, lean_object* v___x_3915_, lean_object* v___x_3916_, lean_object* v_as_3917_, lean_object* v_sz_3918_, lean_object* v_i_3919_, lean_object* v_b_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
size_t v_sz_boxed_3924_; size_t v_i_boxed_3925_; lean_object* v_res_3926_; 
v_sz_boxed_3924_ = lean_unbox_usize(v_sz_3918_);
lean_dec(v_sz_3918_);
v_i_boxed_3925_ = lean_unbox_usize(v_i_3919_);
lean_dec(v_i_3919_);
v_res_3926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3912_, v___x_3913_, v___x_3914_, v___x_3915_, v___x_3916_, v_as_3917_, v_sz_boxed_3924_, v_i_boxed_3925_, v_b_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec_ref(v_as_3917_);
lean_dec(v___x_3916_);
lean_dec_ref(v___x_3914_);
lean_dec_ref(v___x_3913_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3927_, lean_object* v___x_3928_, lean_object* v___x_3929_, lean_object* v___x_3930_, lean_object* v___x_3931_, lean_object* v_as_3932_, size_t v_sz_3933_, size_t v_i_3934_, lean_object* v_b_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
uint8_t v___x_3939_; 
v___x_3939_ = lean_usize_dec_lt(v_i_3934_, v_sz_3933_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; 
lean_dec_ref(v___x_3930_);
lean_dec(v_stx_3927_);
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v_b_3935_);
return v___x_3940_;
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v_a_3944_; lean_object* v___x_3945_; 
lean_dec_ref(v_b_3935_);
v___x_3941_ = lean_box(0);
v___x_3942_ = l_Lean_inheritedTraceOptions;
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3944_ = lean_array_uget_borrowed(v_as_3932_, v_i_3934_);
lean_inc(v_a_3944_);
lean_inc(v_stx_3927_);
v___x_3945_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3927_, v___x_3928_, v_a_3944_, v___x_3929_, v___y_3936_, v___y_3937_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v_scopes_3968_; lean_object* v___x_3969_; lean_object* v_opts_3970_; uint8_t v_hasTrace_3971_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v___x_3965_ = lean_st_ref_get(v___x_3942_);
v___x_3966_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3967_ = lean_st_ref_get(v___y_3937_);
v_scopes_3968_ = lean_ctor_get(v___x_3967_, 2);
lean_inc(v_scopes_3968_);
lean_dec(v___x_3967_);
v___x_3969_ = l_List_head_x21___redArg(v___x_3966_, v_scopes_3968_);
lean_dec(v_scopes_3968_);
v_opts_3970_ = lean_ctor_get(v___x_3969_, 1);
lean_inc_ref(v_opts_3970_);
lean_dec(v___x_3969_);
v_hasTrace_3971_ = lean_ctor_get_uint8(v_opts_3970_, sizeof(void*)*1);
if (v_hasTrace_3971_ == 0)
{
lean_dec_ref(v_opts_3970_);
lean_dec(v___x_3965_);
v___y_3948_ = v___y_3936_;
v___y_3949_ = v___y_3937_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3972_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3973_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3965_, v_opts_3970_, v___x_3972_);
lean_dec_ref(v_opts_3970_);
lean_dec(v___x_3965_);
if (v___x_3973_ == 0)
{
v___y_3948_ = v___y_3936_;
v___y_3949_ = v___y_3937_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3974_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3975_ = lean_array_get_size(v_a_3946_);
v___x_3976_ = l_Nat_reprFast(v___x_3975_);
v___x_3977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
v___x_3978_ = l_Lean_MessageData_ofFormat(v___x_3977_);
v___x_3979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3974_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3943_, v___x_3979_, v___y_3936_, v___y_3937_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_dec_ref_known(v___x_3980_, 1);
v___y_3948_ = v___y_3936_;
v___y_3949_ = v___y_3937_;
goto v___jp_3947_;
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec(v_a_3946_);
lean_dec_ref(v___x_3930_);
lean_dec(v_stx_3927_);
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
v___jp_3947_:
{
size_t v_sz_3950_; size_t v___x_3951_; lean_object* v___x_3952_; 
v_sz_3950_ = lean_array_size(v_a_3946_);
v___x_3951_ = ((size_t)0ULL);
lean_inc_ref(v___x_3930_);
lean_inc(v_a_3944_);
v___x_3952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3944_, v___x_3930_, v___x_3931_, v_a_3946_, v_sz_3950_, v___x_3951_, v___x_3941_, v___y_3948_, v___y_3949_);
lean_dec(v_a_3946_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v___x_3953_; size_t v___x_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
lean_dec_ref_known(v___x_3952_, 1);
v___x_3953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3954_ = ((size_t)1ULL);
v___x_3955_ = lean_usize_add(v_i_3934_, v___x_3954_);
v___x_3956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3927_, v___x_3928_, v___x_3929_, v___x_3930_, v___x_3931_, v_as_3932_, v_sz_3933_, v___x_3955_, v___x_3953_, v___y_3936_, v___y_3937_);
return v___x_3956_;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec_ref(v___x_3930_);
lean_dec(v_stx_3927_);
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
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_dec_ref(v___x_3930_);
lean_dec(v_stx_3927_);
v_a_3989_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3945_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3945_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3997_, lean_object* v___x_3998_, lean_object* v___x_3999_, lean_object* v___x_4000_, lean_object* v___x_4001_, lean_object* v_as_4002_, lean_object* v_sz_4003_, lean_object* v_i_4004_, lean_object* v_b_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
size_t v_sz_boxed_4009_; size_t v_i_boxed_4010_; lean_object* v_res_4011_; 
v_sz_boxed_4009_ = lean_unbox_usize(v_sz_4003_);
lean_dec(v_sz_4003_);
v_i_boxed_4010_ = lean_unbox_usize(v_i_4004_);
lean_dec(v_i_4004_);
v_res_4011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3997_, v___x_3998_, v___x_3999_, v___x_4000_, v___x_4001_, v_as_4002_, v_sz_boxed_4009_, v_i_boxed_4010_, v_b_4005_, v___y_4006_, v___y_4007_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec_ref(v_as_4002_);
lean_dec(v___x_4001_);
lean_dec_ref(v___x_3999_);
lean_dec_ref(v___x_3998_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_4015_, lean_object* v___x_4016_, lean_object* v___x_4017_, lean_object* v___x_4018_, lean_object* v___x_4019_, lean_object* v_as_4020_, size_t v_sz_4021_, size_t v_i_4022_, lean_object* v_b_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
uint8_t v___x_4027_; 
v___x_4027_ = lean_usize_dec_lt(v_i_4022_, v_sz_4021_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; 
lean_dec_ref(v___x_4018_);
lean_dec(v_stx_4015_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v_b_4023_);
return v___x_4028_;
}
else
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v_a_4032_; lean_object* v___x_4033_; 
lean_dec_ref(v_b_4023_);
v___x_4029_ = lean_box(0);
v___x_4030_ = l_Lean_inheritedTraceOptions;
v___x_4031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4032_ = lean_array_uget_borrowed(v_as_4020_, v_i_4022_);
lean_inc(v_a_4032_);
lean_inc(v_stx_4015_);
v___x_4033_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4015_, v___x_4016_, v_a_4032_, v___x_4017_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v_scopes_4056_; lean_object* v___x_4057_; lean_object* v_opts_4058_; uint8_t v_hasTrace_4059_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v___x_4053_ = lean_st_ref_get(v___x_4030_);
v___x_4054_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4055_ = lean_st_ref_get(v___y_4025_);
v_scopes_4056_ = lean_ctor_get(v___x_4055_, 2);
lean_inc(v_scopes_4056_);
lean_dec(v___x_4055_);
v___x_4057_ = l_List_head_x21___redArg(v___x_4054_, v_scopes_4056_);
lean_dec(v_scopes_4056_);
v_opts_4058_ = lean_ctor_get(v___x_4057_, 1);
lean_inc_ref(v_opts_4058_);
lean_dec(v___x_4057_);
v_hasTrace_4059_ = lean_ctor_get_uint8(v_opts_4058_, sizeof(void*)*1);
if (v_hasTrace_4059_ == 0)
{
lean_dec_ref(v_opts_4058_);
lean_dec(v___x_4053_);
v___y_4036_ = v___y_4024_;
v___y_4037_ = v___y_4025_;
goto v___jp_4035_;
}
else
{
lean_object* v___x_4060_; uint8_t v___x_4061_; 
v___x_4060_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4061_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4053_, v_opts_4058_, v___x_4060_);
lean_dec_ref(v_opts_4058_);
lean_dec(v___x_4053_);
if (v___x_4061_ == 0)
{
v___y_4036_ = v___y_4024_;
v___y_4037_ = v___y_4025_;
goto v___jp_4035_;
}
else
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4062_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4063_ = lean_array_get_size(v_a_4034_);
v___x_4064_ = l_Nat_reprFast(v___x_4063_);
v___x_4065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
v___x_4066_ = l_Lean_MessageData_ofFormat(v___x_4065_);
v___x_4067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4062_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4031_, v___x_4067_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_dec_ref_known(v___x_4068_, 1);
v___y_4036_ = v___y_4024_;
v___y_4037_ = v___y_4025_;
goto v___jp_4035_;
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec(v_a_4034_);
lean_dec_ref(v___x_4018_);
lean_dec(v_stx_4015_);
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4068_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4068_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
}
v___jp_4035_:
{
size_t v_sz_4038_; size_t v___x_4039_; lean_object* v___x_4040_; 
v_sz_4038_ = lean_array_size(v_a_4034_);
v___x_4039_ = ((size_t)0ULL);
lean_inc_ref(v___x_4018_);
lean_inc(v_a_4032_);
v___x_4040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4032_, v___x_4018_, v___x_4019_, v_a_4034_, v_sz_4038_, v___x_4039_, v___x_4029_, v___y_4036_, v___y_4037_);
lean_dec(v_a_4034_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v___x_4041_; size_t v___x_4042_; size_t v___x_4043_; 
lean_dec_ref_known(v___x_4040_, 1);
v___x_4041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4042_ = ((size_t)1ULL);
v___x_4043_ = lean_usize_add(v_i_4022_, v___x_4042_);
v_i_4022_ = v___x_4043_;
v_b_4023_ = v___x_4041_;
goto _start;
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec_ref(v___x_4018_);
lean_dec(v_stx_4015_);
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
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4084_; 
lean_dec_ref(v___x_4018_);
lean_dec(v_stx_4015_);
v_a_4077_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4079_ = v___x_4033_;
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4033_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4085_, lean_object* v___x_4086_, lean_object* v___x_4087_, lean_object* v___x_4088_, lean_object* v___x_4089_, lean_object* v_as_4090_, lean_object* v_sz_4091_, lean_object* v_i_4092_, lean_object* v_b_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
size_t v_sz_boxed_4097_; size_t v_i_boxed_4098_; lean_object* v_res_4099_; 
v_sz_boxed_4097_ = lean_unbox_usize(v_sz_4091_);
lean_dec(v_sz_4091_);
v_i_boxed_4098_ = lean_unbox_usize(v_i_4092_);
lean_dec(v_i_4092_);
v_res_4099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4085_, v___x_4086_, v___x_4087_, v___x_4088_, v___x_4089_, v_as_4090_, v_sz_boxed_4097_, v_i_boxed_4098_, v_b_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec_ref(v_as_4090_);
lean_dec(v___x_4089_);
lean_dec_ref(v___x_4087_);
lean_dec_ref(v___x_4086_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4100_, lean_object* v___x_4101_, lean_object* v___x_4102_, lean_object* v___x_4103_, lean_object* v___x_4104_, lean_object* v_as_4105_, size_t v_sz_4106_, size_t v_i_4107_, lean_object* v_b_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
uint8_t v___x_4112_; 
v___x_4112_ = lean_usize_dec_lt(v_i_4107_, v_sz_4106_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; 
lean_dec_ref(v___x_4103_);
lean_dec(v_stx_4100_);
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_b_4108_);
return v___x_4113_;
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v_a_4117_; lean_object* v___x_4118_; 
lean_dec_ref(v_b_4108_);
v___x_4114_ = lean_box(0);
v___x_4115_ = l_Lean_inheritedTraceOptions;
v___x_4116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4117_ = lean_array_uget_borrowed(v_as_4105_, v_i_4107_);
lean_inc(v_a_4117_);
lean_inc(v_stx_4100_);
v___x_4118_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4100_, v___x_4101_, v_a_4117_, v___x_4102_, v___y_4109_, v___y_4110_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v_scopes_4141_; lean_object* v___x_4142_; lean_object* v_opts_4143_; uint8_t v_hasTrace_4144_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
v___x_4138_ = lean_st_ref_get(v___x_4115_);
v___x_4139_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4140_ = lean_st_ref_get(v___y_4110_);
v_scopes_4141_ = lean_ctor_get(v___x_4140_, 2);
lean_inc(v_scopes_4141_);
lean_dec(v___x_4140_);
v___x_4142_ = l_List_head_x21___redArg(v___x_4139_, v_scopes_4141_);
lean_dec(v_scopes_4141_);
v_opts_4143_ = lean_ctor_get(v___x_4142_, 1);
lean_inc_ref(v_opts_4143_);
lean_dec(v___x_4142_);
v_hasTrace_4144_ = lean_ctor_get_uint8(v_opts_4143_, sizeof(void*)*1);
if (v_hasTrace_4144_ == 0)
{
lean_dec_ref(v_opts_4143_);
lean_dec(v___x_4138_);
v___y_4121_ = v___y_4109_;
v___y_4122_ = v___y_4110_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4145_; uint8_t v___x_4146_; 
v___x_4145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4146_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4138_, v_opts_4143_, v___x_4145_);
lean_dec_ref(v_opts_4143_);
lean_dec(v___x_4138_);
if (v___x_4146_ == 0)
{
v___y_4121_ = v___y_4109_;
v___y_4122_ = v___y_4110_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4147_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4148_ = lean_array_get_size(v_a_4119_);
v___x_4149_ = l_Nat_reprFast(v___x_4148_);
v___x_4150_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
v___x_4151_ = l_Lean_MessageData_ofFormat(v___x_4150_);
v___x_4152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4147_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
v___x_4153_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4116_, v___x_4152_, v___y_4109_, v___y_4110_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_dec_ref_known(v___x_4153_, 1);
v___y_4121_ = v___y_4109_;
v___y_4122_ = v___y_4110_;
goto v___jp_4120_;
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec(v_a_4119_);
lean_dec_ref(v___x_4103_);
lean_dec(v_stx_4100_);
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4153_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4153_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
v___jp_4120_:
{
size_t v_sz_4123_; size_t v___x_4124_; lean_object* v___x_4125_; 
v_sz_4123_ = lean_array_size(v_a_4119_);
v___x_4124_ = ((size_t)0ULL);
lean_inc_ref(v___x_4103_);
lean_inc(v_a_4117_);
v___x_4125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4117_, v___x_4103_, v___x_4104_, v_a_4119_, v_sz_4123_, v___x_4124_, v___x_4114_, v___y_4121_, v___y_4122_);
lean_dec(v_a_4119_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4126_; size_t v___x_4127_; size_t v___x_4128_; lean_object* v___x_4129_; 
lean_dec_ref_known(v___x_4125_, 1);
v___x_4126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4127_ = ((size_t)1ULL);
v___x_4128_ = lean_usize_add(v_i_4107_, v___x_4127_);
v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4100_, v___x_4101_, v___x_4102_, v___x_4103_, v___x_4104_, v_as_4105_, v_sz_4106_, v___x_4128_, v___x_4126_, v___y_4109_, v___y_4110_);
return v___x_4129_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v___x_4103_);
lean_dec(v_stx_4100_);
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
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec_ref(v___x_4103_);
lean_dec(v_stx_4100_);
v_a_4162_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4118_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4118_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4170_, lean_object* v___x_4171_, lean_object* v___x_4172_, lean_object* v___x_4173_, lean_object* v___x_4174_, lean_object* v_as_4175_, lean_object* v_sz_4176_, lean_object* v_i_4177_, lean_object* v_b_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
size_t v_sz_boxed_4182_; size_t v_i_boxed_4183_; lean_object* v_res_4184_; 
v_sz_boxed_4182_ = lean_unbox_usize(v_sz_4176_);
lean_dec(v_sz_4176_);
v_i_boxed_4183_ = lean_unbox_usize(v_i_4177_);
lean_dec(v_i_4177_);
v_res_4184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4170_, v___x_4171_, v___x_4172_, v___x_4173_, v___x_4174_, v_as_4175_, v_sz_boxed_4182_, v_i_boxed_4183_, v_b_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec_ref(v_as_4175_);
lean_dec(v___x_4174_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4171_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4185_, lean_object* v_stx_4186_, lean_object* v___x_4187_, lean_object* v___x_4188_, lean_object* v___x_4189_, lean_object* v___x_4190_, lean_object* v_n_4191_, lean_object* v_b_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
if (lean_obj_tag(v_n_4191_) == 0)
{
lean_object* v_cs_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; size_t v_sz_4199_; size_t v___x_4200_; lean_object* v___x_4201_; 
v_cs_4196_ = lean_ctor_get(v_n_4191_, 0);
v___x_4197_ = lean_box(0);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
lean_ctor_set(v___x_4198_, 1, v_b_4192_);
v_sz_4199_ = lean_array_size(v_cs_4196_);
v___x_4200_ = ((size_t)0ULL);
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4185_, v_stx_4186_, v___x_4187_, v___x_4188_, v___x_4189_, v___x_4190_, v_cs_4196_, v_sz_4199_, v___x_4200_, v___x_4198_, v___y_4193_, v___y_4194_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4216_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4216_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4216_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v_fst_4206_; 
v_fst_4206_ = lean_ctor_get(v_a_4202_, 0);
if (lean_obj_tag(v_fst_4206_) == 0)
{
lean_object* v_snd_4207_; lean_object* v___x_4208_; lean_object* v___x_4210_; 
v_snd_4207_ = lean_ctor_get(v_a_4202_, 1);
lean_inc(v_snd_4207_);
lean_dec(v_a_4202_);
v___x_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4208_, 0, v_snd_4207_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v___x_4208_);
v___x_4210_ = v___x_4204_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
else
{
lean_object* v_val_4212_; lean_object* v___x_4214_; 
lean_inc_ref(v_fst_4206_);
lean_dec(v_a_4202_);
v_val_4212_ = lean_ctor_get(v_fst_4206_, 0);
lean_inc(v_val_4212_);
lean_dec_ref_known(v_fst_4206_, 1);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v_val_4212_);
v___x_4214_ = v___x_4204_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_val_4212_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
v_a_4217_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4201_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4201_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
lean_object* v_vs_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; size_t v_sz_4228_; size_t v___x_4229_; lean_object* v___x_4230_; 
v_vs_4225_ = lean_ctor_get(v_n_4191_, 0);
v___x_4226_ = lean_box(0);
v___x_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
lean_ctor_set(v___x_4227_, 1, v_b_4192_);
v_sz_4228_ = lean_array_size(v_vs_4225_);
v___x_4229_ = ((size_t)0ULL);
v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4186_, v___x_4187_, v___x_4188_, v___x_4189_, v___x_4190_, v_vs_4225_, v_sz_4228_, v___x_4229_, v___x_4227_, v___y_4193_, v___y_4194_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4245_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4233_ = v___x_4230_;
v_isShared_4234_ = v_isSharedCheck_4245_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4230_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4245_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v_fst_4235_; 
v_fst_4235_ = lean_ctor_get(v_a_4231_, 0);
if (lean_obj_tag(v_fst_4235_) == 0)
{
lean_object* v_snd_4236_; lean_object* v___x_4237_; lean_object* v___x_4239_; 
v_snd_4236_ = lean_ctor_get(v_a_4231_, 1);
lean_inc(v_snd_4236_);
lean_dec(v_a_4231_);
v___x_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4237_, 0, v_snd_4236_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4237_);
v___x_4239_ = v___x_4233_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
else
{
lean_object* v_val_4241_; lean_object* v___x_4243_; 
lean_inc_ref(v_fst_4235_);
lean_dec(v_a_4231_);
v_val_4241_ = lean_ctor_get(v_fst_4235_, 0);
lean_inc(v_val_4241_);
lean_dec_ref_known(v_fst_4235_, 1);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v_val_4241_);
v___x_4243_ = v___x_4233_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_val_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
v_a_4246_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4230_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4230_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4254_, lean_object* v_stx_4255_, lean_object* v___x_4256_, lean_object* v___x_4257_, lean_object* v___x_4258_, lean_object* v___x_4259_, lean_object* v_as_4260_, size_t v_sz_4261_, size_t v_i_4262_, lean_object* v_b_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
uint8_t v___x_4267_; 
v___x_4267_ = lean_usize_dec_lt(v_i_4262_, v_sz_4261_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4268_; 
lean_dec_ref(v___x_4258_);
lean_dec(v_stx_4255_);
v___x_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4268_, 0, v_b_4263_);
return v___x_4268_;
}
else
{
lean_object* v_snd_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4303_; 
v_snd_4269_ = lean_ctor_get(v_b_4263_, 1);
v_isSharedCheck_4303_ = !lean_is_exclusive(v_b_4263_);
if (v_isSharedCheck_4303_ == 0)
{
lean_object* v_unused_4304_; 
v_unused_4304_ = lean_ctor_get(v_b_4263_, 0);
lean_dec(v_unused_4304_);
v___x_4271_ = v_b_4263_;
v_isShared_4272_ = v_isSharedCheck_4303_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_snd_4269_);
lean_dec(v_b_4263_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4303_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; lean_object* v_a_4274_; lean_object* v___x_4275_; 
v___x_4273_ = lean_box(0);
v_a_4274_ = lean_array_uget_borrowed(v_as_4260_, v_i_4262_);
lean_inc(v_snd_4269_);
lean_inc_ref(v___x_4258_);
lean_inc(v_stx_4255_);
v___x_4275_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4254_, v_stx_4255_, v___x_4256_, v___x_4257_, v___x_4258_, v___x_4259_, v_a_4274_, v_snd_4269_, v___y_4264_, v___y_4265_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4294_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4294_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4294_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
if (lean_obj_tag(v_a_4276_) == 0)
{
lean_object* v___x_4280_; lean_object* v___x_4282_; 
lean_dec_ref(v___x_4258_);
lean_dec(v_stx_4255_);
v___x_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4280_, 0, v_a_4276_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4280_);
v___x_4282_ = v___x_4271_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v___x_4280_);
lean_ctor_set(v_reuseFailAlloc_4286_, 1, v_snd_4269_);
v___x_4282_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
lean_object* v___x_4284_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v___x_4282_);
v___x_4284_ = v___x_4278_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4282_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; 
lean_del_object(v___x_4278_);
lean_dec(v_snd_4269_);
v_a_4287_ = lean_ctor_get(v_a_4276_, 0);
lean_inc(v_a_4287_);
lean_dec_ref_known(v_a_4276_, 1);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 1, v_a_4287_);
lean_ctor_set(v___x_4271_, 0, v___x_4273_);
v___x_4289_ = v___x_4271_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4273_);
lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_a_4287_);
v___x_4289_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
size_t v___x_4290_; size_t v___x_4291_; 
v___x_4290_ = ((size_t)1ULL);
v___x_4291_ = lean_usize_add(v_i_4262_, v___x_4290_);
v_i_4262_ = v___x_4291_;
v_b_4263_ = v___x_4289_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
lean_del_object(v___x_4271_);
lean_dec(v_snd_4269_);
lean_dec_ref(v___x_4258_);
lean_dec(v_stx_4255_);
v_a_4295_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4275_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4275_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4305_, lean_object* v_stx_4306_, lean_object* v___x_4307_, lean_object* v___x_4308_, lean_object* v___x_4309_, lean_object* v___x_4310_, lean_object* v_as_4311_, lean_object* v_sz_4312_, lean_object* v_i_4313_, lean_object* v_b_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
size_t v_sz_boxed_4318_; size_t v_i_boxed_4319_; lean_object* v_res_4320_; 
v_sz_boxed_4318_ = lean_unbox_usize(v_sz_4312_);
lean_dec(v_sz_4312_);
v_i_boxed_4319_ = lean_unbox_usize(v_i_4313_);
lean_dec(v_i_4313_);
v_res_4320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4305_, v_stx_4306_, v___x_4307_, v___x_4308_, v___x_4309_, v___x_4310_, v_as_4311_, v_sz_boxed_4318_, v_i_boxed_4319_, v_b_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec_ref(v_as_4311_);
lean_dec(v___x_4310_);
lean_dec_ref(v___x_4308_);
lean_dec_ref(v___x_4307_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4321_, lean_object* v_stx_4322_, lean_object* v___x_4323_, lean_object* v___x_4324_, lean_object* v___x_4325_, lean_object* v___x_4326_, lean_object* v_n_4327_, lean_object* v_b_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4321_, v_stx_4322_, v___x_4323_, v___x_4324_, v___x_4325_, v___x_4326_, v_n_4327_, v_b_4328_, v___y_4329_, v___y_4330_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec_ref(v_n_4327_);
lean_dec(v___x_4326_);
lean_dec_ref(v___x_4324_);
lean_dec_ref(v___x_4323_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4333_, lean_object* v___x_4334_, lean_object* v_stx_4335_, lean_object* v___x_4336_, lean_object* v___x_4337_, lean_object* v_t_4338_, lean_object* v_init_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_root_4343_; lean_object* v_tail_4344_; lean_object* v___x_4345_; 
v_root_4343_ = lean_ctor_get(v_t_4338_, 0);
v_tail_4344_ = lean_ctor_get(v_t_4338_, 1);
lean_inc_ref(v___x_4333_);
lean_inc(v_stx_4335_);
v___x_4345_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4339_, v_stx_4335_, v___x_4336_, v___x_4337_, v___x_4333_, v___x_4334_, v_root_4343_, v_init_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4382_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4348_ = v___x_4345_;
v_isShared_4349_ = v_isSharedCheck_4382_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4345_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4382_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
if (lean_obj_tag(v_a_4346_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4352_; 
lean_dec(v_stx_4335_);
lean_dec_ref(v___x_4333_);
v_a_4350_ = lean_ctor_get(v_a_4346_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v_a_4346_, 1);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 0, v_a_4350_);
v___x_4352_ = v___x_4348_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4350_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; size_t v_sz_4357_; size_t v___x_4358_; lean_object* v___x_4359_; 
lean_del_object(v___x_4348_);
v_a_4354_ = lean_ctor_get(v_a_4346_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v_a_4346_, 1);
v___x_4355_ = lean_box(0);
v___x_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4355_);
lean_ctor_set(v___x_4356_, 1, v_a_4354_);
v_sz_4357_ = lean_array_size(v_tail_4344_);
v___x_4358_ = ((size_t)0ULL);
v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4335_, v___x_4336_, v___x_4337_, v___x_4333_, v___x_4334_, v_tail_4344_, v_sz_4357_, v___x_4358_, v___x_4356_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4373_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4362_ = v___x_4359_;
v_isShared_4363_ = v_isSharedCheck_4373_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4359_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4373_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v_fst_4364_; 
v_fst_4364_ = lean_ctor_get(v_a_4360_, 0);
if (lean_obj_tag(v_fst_4364_) == 0)
{
lean_object* v_snd_4365_; lean_object* v___x_4367_; 
v_snd_4365_ = lean_ctor_get(v_a_4360_, 1);
lean_inc(v_snd_4365_);
lean_dec(v_a_4360_);
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v_snd_4365_);
v___x_4367_ = v___x_4362_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_snd_4365_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
else
{
lean_object* v_val_4369_; lean_object* v___x_4371_; 
lean_inc_ref(v_fst_4364_);
lean_dec(v_a_4360_);
v_val_4369_ = lean_ctor_get(v_fst_4364_, 0);
lean_inc(v_val_4369_);
lean_dec_ref_known(v_fst_4364_, 1);
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v_val_4369_);
v___x_4371_ = v___x_4362_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_val_4369_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
else
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
v_a_4374_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4359_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4359_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
lean_dec(v_stx_4335_);
lean_dec_ref(v___x_4333_);
v_a_4383_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4345_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4345_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4391_, lean_object* v___x_4392_, lean_object* v_stx_4393_, lean_object* v___x_4394_, lean_object* v___x_4395_, lean_object* v_t_4396_, lean_object* v_init_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4391_, v___x_4392_, v_stx_4393_, v___x_4394_, v___x_4395_, v_t_4396_, v_init_4397_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec_ref(v_t_4396_);
lean_dec_ref(v___x_4395_);
lean_dec_ref(v___x_4394_);
lean_dec(v___x_4392_);
return v_res_4401_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4404_ = l_Lean_stringToMessageData(v___x_4403_);
return v___x_4404_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4409_ = l_Lean_stringToMessageData(v___x_4408_);
return v___x_4409_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4412_ = l_Lean_stringToMessageData(v___x_4411_);
return v___x_4412_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4415_ = l_Lean_stringToMessageData(v___x_4414_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v_scopes_4425_; lean_object* v___x_4426_; lean_object* v_opts_4427_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; uint8_t v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; uint8_t v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4468_; uint8_t v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; uint8_t v___y_4481_; uint8_t v___y_4482_; lean_object* v___y_4483_; uint8_t v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; uint8_t v___y_4495_; uint8_t v___y_4496_; uint8_t v___y_4497_; uint8_t v___y_4531_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v___x_4423_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4424_ = lean_st_ref_get(v___y_4418_);
v_scopes_4425_ = lean_ctor_get(v___x_4424_, 2);
lean_inc(v_scopes_4425_);
lean_dec(v___x_4424_);
v___x_4426_ = l_List_head_x21___redArg(v___x_4423_, v_scopes_4425_);
lean_dec(v_scopes_4425_);
v_opts_4427_ = lean_ctor_get(v___x_4426_, 1);
lean_inc_ref(v_opts_4427_);
lean_dec(v___x_4426_);
v___x_4538_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4539_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4427_, v___x_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4540_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4541_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4427_, v___x_4540_);
v___y_4531_ = v___x_4541_;
goto v___jp_4530_;
}
else
{
v___y_4531_ = v___x_4539_;
goto v___jp_4530_;
}
v___jp_4420_:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = lean_box(0);
v___x_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
return v___x_4422_;
}
v___jp_4428_:
{
lean_object* v___x_4433_; lean_object* v_line_4434_; lean_object* v___x_4435_; lean_object* v_messages_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v_a_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_inc_ref_n(v___y_4431_, 2);
v___x_4433_ = l_Lean_FileMap_toPosition(v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
v_line_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_line_4434_);
lean_dec_ref(v___x_4433_);
v___x_4435_ = lean_st_ref_get(v___y_4430_);
v_messages_4436_ = lean_ctor_get(v___x_4435_, 1);
lean_inc_ref(v_messages_4436_);
lean_dec(v___x_4435_);
v___x_4437_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4436_);
v___x_4438_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4430_);
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_a_4439_);
lean_dec_ref(v___x_4438_);
v___x_4440_ = lean_box(0);
v___x_4441_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4431_, v_line_4434_, v_stx_4416_, v_opts_4427_, v___x_4437_, v_a_4439_, v___x_4440_, v___y_4429_, v___y_4430_);
lean_dec(v_a_4439_);
lean_dec_ref(v___x_4437_);
lean_dec_ref(v_opts_4427_);
lean_dec(v_line_4434_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4448_ == 0)
{
lean_object* v_unused_4449_; 
v_unused_4449_ = lean_ctor_get(v___x_4441_, 0);
lean_dec(v_unused_4449_);
v___x_4443_ = v___x_4441_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_dec(v___x_4441_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 0, v___x_4440_);
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4440_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
else
{
return v___x_4441_;
}
}
v___jp_4450_:
{
lean_object* v_fileMap_4454_; lean_object* v___x_4455_; 
v_fileMap_4454_ = lean_ctor_get(v___y_4452_, 1);
v___x_4455_ = l_Lean_Syntax_getPos_x3f(v_stx_4416_, v___y_4451_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = lean_unsigned_to_nat(0u);
v___y_4429_ = v___y_4452_;
v___y_4430_ = v___y_4453_;
v___y_4431_ = v_fileMap_4454_;
v___y_4432_ = v___x_4456_;
goto v___jp_4428_;
}
else
{
lean_object* v_val_4457_; 
v_val_4457_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_val_4457_);
lean_dec_ref_known(v___x_4455_, 1);
v___y_4429_ = v___y_4452_;
v___y_4430_ = v___y_4453_;
v___y_4431_ = v_fileMap_4454_;
v___y_4432_ = v_val_4457_;
goto v___jp_4428_;
}
}
v___jp_4458_:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
lean_inc_ref(v___y_4462_);
v___x_4463_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___y_4462_);
v___x_4464_ = l_Lean_MessageData_ofFormat(v___x_4463_);
v___x_4465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___y_4461_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
lean_inc(v___y_4460_);
v___x_4466_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___y_4460_, v___x_4465_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_dec_ref_known(v___x_4466_, 1);
v___y_4451_ = v___y_4459_;
v___y_4452_ = v___y_4417_;
v___y_4453_ = v___y_4418_;
goto v___jp_4450_;
}
else
{
lean_dec_ref(v_opts_4427_);
lean_dec(v_stx_4416_);
return v___x_4466_;
}
}
v___jp_4467_:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
lean_inc_ref(v___y_4472_);
v___x_4473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___y_4472_);
v___x_4474_ = l_Lean_MessageData_ofFormat(v___x_4473_);
v___x_4475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4475_, 0, v___y_4471_);
lean_ctor_set(v___x_4475_, 1, v___x_4474_);
v___x_4476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4475_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
if (v___y_4469_ == 0)
{
lean_object* v___x_4478_; 
v___x_4478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4459_ = v___y_4468_;
v___y_4460_ = v___y_4470_;
v___y_4461_ = v___x_4477_;
v___y_4462_ = v___x_4478_;
goto v___jp_4458_;
}
else
{
lean_object* v___x_4479_; 
v___x_4479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4459_ = v___y_4468_;
v___y_4460_ = v___y_4470_;
v___y_4461_ = v___x_4477_;
v___y_4462_ = v___x_4479_;
goto v___jp_4458_;
}
}
v___jp_4480_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
lean_inc_ref(v___y_4486_);
v___x_4487_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4487_, 0, v___y_4486_);
v___x_4488_ = l_Lean_MessageData_ofFormat(v___x_4487_);
lean_inc_ref(v___y_4485_);
v___x_4489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___y_4485_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
v___x_4490_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4489_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
if (v___y_4484_ == 0)
{
lean_object* v___x_4492_; 
v___x_4492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4468_ = v___y_4481_;
v___y_4469_ = v___y_4482_;
v___y_4470_ = v___y_4483_;
v___y_4471_ = v___x_4491_;
v___y_4472_ = v___x_4492_;
goto v___jp_4467_;
}
else
{
lean_object* v___x_4493_; 
v___x_4493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4468_ = v___y_4481_;
v___y_4469_ = v___y_4482_;
v___y_4470_ = v___y_4483_;
v___y_4471_ = v___x_4491_;
v___y_4472_ = v___x_4493_;
goto v___jp_4467_;
}
}
v___jp_4494_:
{
lean_object* v___x_4498_; lean_object* v_a_4499_; uint8_t v___x_4500_; 
v___x_4498_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4416_, v___y_4417_, v___y_4418_);
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref(v___x_4498_);
v___x_4500_ = lean_unbox(v_a_4499_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v_scopes_4505_; lean_object* v___x_4506_; lean_object* v_opts_4507_; uint8_t v_hasTrace_4508_; 
v___x_4501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4502_ = l_Lean_inheritedTraceOptions;
v___x_4503_ = lean_st_ref_get(v___x_4502_);
v___x_4504_ = lean_st_ref_get(v___y_4418_);
v_scopes_4505_ = lean_ctor_get(v___x_4504_, 2);
lean_inc(v_scopes_4505_);
lean_dec(v___x_4504_);
v___x_4506_ = l_List_head_x21___redArg(v___x_4423_, v_scopes_4505_);
lean_dec(v_scopes_4505_);
v_opts_4507_ = lean_ctor_get(v___x_4506_, 1);
lean_inc_ref(v_opts_4507_);
lean_dec(v___x_4506_);
v_hasTrace_4508_ = lean_ctor_get_uint8(v_opts_4507_, sizeof(void*)*1);
if (v_hasTrace_4508_ == 0)
{
uint8_t v___x_4509_; 
lean_dec_ref(v_opts_4507_);
lean_dec(v___x_4503_);
v___x_4509_ = lean_unbox(v_a_4499_);
lean_dec(v_a_4499_);
v___y_4451_ = v___x_4509_;
v___y_4452_ = v___y_4417_;
v___y_4453_ = v___y_4418_;
goto v___jp_4450_;
}
else
{
lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4511_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4503_, v_opts_4507_, v___x_4510_);
lean_dec_ref(v_opts_4507_);
lean_dec(v___x_4503_);
if (v___x_4511_ == 0)
{
uint8_t v___x_4512_; 
v___x_4512_ = lean_unbox(v_a_4499_);
lean_dec(v_a_4499_);
v___y_4451_ = v___x_4512_;
v___y_4452_ = v___y_4417_;
v___y_4453_ = v___y_4418_;
goto v___jp_4450_;
}
else
{
lean_object* v___x_4513_; 
v___x_4513_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4497_ == 0)
{
lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4515_ = lean_unbox(v_a_4499_);
lean_dec(v_a_4499_);
v___y_4481_ = v___x_4515_;
v___y_4482_ = v___y_4495_;
v___y_4483_ = v___x_4501_;
v___y_4484_ = v___y_4496_;
v___y_4485_ = v___x_4513_;
v___y_4486_ = v___x_4514_;
goto v___jp_4480_;
}
else
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4517_ = lean_unbox(v_a_4499_);
lean_dec(v_a_4499_);
v___y_4481_ = v___x_4517_;
v___y_4482_ = v___y_4495_;
v___y_4483_ = v___x_4501_;
v___y_4484_ = v___y_4496_;
v___y_4485_ = v___x_4513_;
v___y_4486_ = v___x_4516_;
goto v___jp_4480_;
}
}
}
}
else
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v_scopes_4522_; lean_object* v___x_4523_; lean_object* v_opts_4524_; uint8_t v_hasTrace_4525_; 
lean_dec(v_a_4499_);
lean_dec_ref(v_opts_4427_);
lean_dec(v_stx_4416_);
v___x_4518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4519_ = l_Lean_inheritedTraceOptions;
v___x_4520_ = lean_st_ref_get(v___x_4519_);
v___x_4521_ = lean_st_ref_get(v___y_4418_);
v_scopes_4522_ = lean_ctor_get(v___x_4521_, 2);
lean_inc(v_scopes_4522_);
lean_dec(v___x_4521_);
v___x_4523_ = l_List_head_x21___redArg(v___x_4423_, v_scopes_4522_);
lean_dec(v_scopes_4522_);
v_opts_4524_ = lean_ctor_get(v___x_4523_, 1);
lean_inc_ref(v_opts_4524_);
lean_dec(v___x_4523_);
v_hasTrace_4525_ = lean_ctor_get_uint8(v_opts_4524_, sizeof(void*)*1);
if (v_hasTrace_4525_ == 0)
{
lean_dec_ref(v_opts_4524_);
lean_dec(v___x_4520_);
goto v___jp_4420_;
}
else
{
lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4527_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4520_, v_opts_4524_, v___x_4526_);
lean_dec_ref(v_opts_4524_);
lean_dec(v___x_4520_);
if (v___x_4527_ == 0)
{
goto v___jp_4420_;
}
else
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4529_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4518_, v___x_4528_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_dec_ref_known(v___x_4529_, 1);
goto v___jp_4420_;
}
else
{
return v___x_4529_;
}
}
}
}
}
v___jp_4530_:
{
lean_object* v___x_4532_; uint8_t v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4532_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4533_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4427_, v___x_4532_);
v___x_4534_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4535_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4427_, v___x_4534_);
if (v___y_4531_ == 0)
{
if (v___x_4533_ == 0)
{
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
lean_dec_ref(v_opts_4427_);
lean_dec(v_stx_4416_);
v___x_4536_ = lean_box(0);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
else
{
v___y_4495_ = v___x_4535_;
v___y_4496_ = v___x_4533_;
v___y_4497_ = v___y_4531_;
goto v___jp_4494_;
}
}
else
{
v___y_4495_ = v___x_4535_;
v___y_4496_ = v___x_4533_;
v___y_4497_ = v___y_4531_;
goto v___jp_4494_;
}
}
else
{
v___y_4495_ = v___x_4535_;
v___y_4496_ = v___x_4533_;
v___y_4497_ = v___y_4531_;
goto v___jp_4494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4560_ = l_Lean_Elab_Command_addLinter(v___x_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4562_;
}
}
lean_object* runtime_initialize_Init_Try(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
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
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
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
res = initialize_Lean_Elab_InfoTree_Util(builtin);
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
