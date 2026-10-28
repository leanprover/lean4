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
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static uint16_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11;
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27;
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
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_273_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_274_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_272_);
lean_ctor_set(v___x_274_, 3, v___x_272_);
lean_ctor_set(v___x_274_, 4, v___x_272_);
lean_ctor_set(v___x_274_, 5, v___x_272_);
lean_ctor_set(v___x_274_, 6, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_unsigned_to_nat(32u);
v___x_276_ = lean_mk_empty_array_with_capacity(v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8(void){
_start:
{
size_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_278_ = ((size_t)5ULL);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_unsigned_to_nat(32u);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_280_);
v___x_282_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7);
v___x_283_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
lean_ctor_set(v___x_283_, 2, v___x_279_);
lean_ctor_set(v___x_283_, 3, v___x_279_);
lean_ctor_set_usize(v___x_283_, 4, v___x_278_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
lean_ctor_set(v___x_285_, 2, v___x_284_);
lean_ctor_set(v___x_285_, 3, v___x_284_);
lean_ctor_set(v___x_285_, 4, v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = l_Lean_Options_empty;
v___x_287_ = l_Lean_Core_getMaxHeartbeats(v___x_286_);
return v___x_287_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11(void){
_start:
{
lean_object* v___x_288_; uint16_t v___x_289_; 
v___x_288_ = l_Lean_Options_empty;
v___x_289_ = l_Lean_OptionFlags_ofOptions(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = l_Lean_firstFrontendMacroScope;
v___x_292_ = lean_nat_add(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17(void){
_start:
{
lean_object* v___x_303_; uint64_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_304_ = 0ULL;
v___x_305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set_uint64(v___x_305_, sizeof(void*)*1, v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = l_Lean_Options_empty;
v___x_310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_311_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
lean_ctor_set(v___x_311_, 3, v___x_308_);
lean_ctor_set(v___x_311_, 4, v___x_308_);
lean_ctor_set(v___x_311_, 5, v___x_308_);
return v___x_311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20(void){
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
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21(void){
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
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = l_Lean_maxRecDepth;
v___x_323_ = l_Lean_Options_empty;
v___x_324_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26(void){
_start:
{
uint16_t v___x_325_; uint16_t v___x_326_; uint16_t v___x_327_; 
v___x_325_ = 512;
v___x_326_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_327_ = lean_uint16_land(v___x_326_, v___x_325_);
return v___x_327_;
}
}
static uint8_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27(void){
_start:
{
uint16_t v___x_328_; uint16_t v___x_329_; uint8_t v___x_330_; 
v___x_328_ = 0;
v___x_329_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26);
v___x_330_ = lean_uint16_dec_eq(v___x_329_, v___x_328_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object* v_env_331_, lean_object* v_mctx_332_, lean_object* v_lctx_333_, lean_object* v_opts_334_, lean_object* v_namingCtx_335_, lean_object* v_x_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_fileName_352_; lean_object* v_fileMap_353_; lean_object* v_ref_354_; lean_object* v_cancelTk_x3f_355_; lean_object* v_a_357_; lean_object* v_a_364_; lean_object* v_currNamespace_366_; lean_object* v_openDecls_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint16_t v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___y_388_; lean_object* v___y_389_; uint16_t v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_491_; uint8_t v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; uint16_t v___y_496_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v_fileName_531_; lean_object* v_fileMap_532_; lean_object* v_currNamespace_533_; lean_object* v_openDecls_534_; lean_object* v_initHeartbeats_535_; lean_object* v_maxHeartbeats_536_; lean_object* v_quotContext_537_; lean_object* v_currMacroScope_538_; lean_object* v_cancelTk_x3f_539_; lean_object* v_inheritedTraceOptions_540_; lean_object* v_currRecDepth_541_; lean_object* v_ref_542_; uint8_t v_suppressElabErrors_543_; uint8_t v_checkDeprecated_544_; uint8_t v_isRecordingDeps_545_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___y_554_; lean_object* v_env_575_; uint8_t v___x_576_; uint8_t v___x_577_; 
v___x_340_ = lean_box(1);
v___x_341_ = 0;
v___x_342_ = l_Lean_Environment_setExporting(v_env_331_, v___x_341_);
v___x_343_ = 1;
v___x_344_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_348_, 0, v___x_344_);
lean_ctor_set(v___x_348_, 1, v___x_340_);
lean_ctor_set(v___x_348_, 2, v_lctx_333_);
lean_ctor_set(v___x_348_, 3, v___x_346_);
lean_ctor_set(v___x_348_, 4, v___x_347_);
lean_ctor_set(v___x_348_, 5, v___x_345_);
lean_ctor_set(v___x_348_, 6, v___x_347_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*7, v___x_341_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*7 + 1, v___x_341_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*7 + 2, v___x_341_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*7 + 3, v___x_343_);
v___x_349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6);
v___x_350_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_351_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9);
v_fileName_352_ = lean_ctor_get(v_a_337_, 0);
v_fileMap_353_ = lean_ctor_get(v_a_337_, 1);
v_ref_354_ = lean_ctor_get(v_a_337_, 7);
v_cancelTk_x3f_355_ = lean_ctor_get(v_a_337_, 9);
v_currNamespace_366_ = lean_ctor_get(v_namingCtx_335_, 0);
lean_inc(v_currNamespace_366_);
v_openDecls_367_ = lean_ctor_get(v_namingCtx_335_, 1);
lean_inc(v_openDecls_367_);
lean_dec_ref(v_namingCtx_335_);
v___x_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_368_, 0, v_mctx_332_);
lean_ctor_set(v___x_368_, 1, v___x_349_);
lean_ctor_set(v___x_368_, 2, v___x_340_);
lean_ctor_set(v___x_368_, 3, v___x_350_);
lean_ctor_set(v___x_368_, 4, v___x_351_);
v___x_369_ = l_Lean_Options_empty;
v___x_370_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_371_ = lean_box(0);
v___x_372_ = l_Lean_firstFrontendMacroScope;
v___x_373_ = lean_box(0);
v___x_374_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_375_ = 0;
v___x_376_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12);
v___x_377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15));
v___x_378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16));
v___x_379_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17);
v___x_380_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18);
v___x_381_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
v___x_382_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20);
v___x_383_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21);
v___x_384_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_384_, 0, v___x_342_);
lean_ctor_set(v___x_384_, 1, v___x_376_);
lean_ctor_set(v___x_384_, 2, v___x_377_);
lean_ctor_set(v___x_384_, 3, v___x_378_);
lean_ctor_set(v___x_384_, 4, v___x_379_);
lean_ctor_set(v___x_384_, 5, v___x_380_);
lean_ctor_set(v___x_384_, 6, v___x_381_);
lean_ctor_set(v___x_384_, 7, v___x_382_);
lean_ctor_set(v___x_384_, 8, v___x_383_);
lean_ctor_set(v___x_384_, 9, v___x_346_);
v___x_385_ = lean_io_get_num_heartbeats();
v___x_386_ = lean_st_mk_ref(v___x_384_);
v___x_550_ = l_Lean_inheritedTraceOptions;
v___x_551_ = lean_st_ref_get(v___x_550_);
v___x_552_ = lean_st_ref_get(v___x_386_);
v_env_575_ = lean_ctor_get(v___x_552_, 0);
lean_inc_ref(v_env_575_);
lean_dec(v___x_552_);
v___x_576_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_575_);
lean_dec_ref(v_env_575_);
v___x_577_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27);
if (v___x_577_ == 0)
{
if (v___x_576_ == 0)
{
v___y_554_ = v___x_343_;
goto v___jp_553_;
}
else
{
v_fileName_531_ = v_fileName_352_;
v_fileMap_532_ = v_fileMap_353_;
v_currNamespace_533_ = v_currNamespace_366_;
v_openDecls_534_ = v_openDecls_367_;
v_initHeartbeats_535_ = v___x_385_;
v_maxHeartbeats_536_ = v___x_370_;
v_quotContext_537_ = v___x_371_;
v_currMacroScope_538_ = v___x_372_;
v_cancelTk_x3f_539_ = v_cancelTk_x3f_355_;
v_inheritedTraceOptions_540_ = v___x_551_;
v_currRecDepth_541_ = v___x_345_;
v_ref_542_ = v___x_373_;
v_suppressElabErrors_543_ = v___x_341_;
v_checkDeprecated_544_ = v___x_375_;
v_isRecordingDeps_545_ = v___x_341_;
goto v___jp_530_;
}
}
else
{
if (v___x_576_ == 0)
{
v_fileName_531_ = v_fileName_352_;
v_fileMap_532_ = v_fileMap_353_;
v_currNamespace_533_ = v_currNamespace_366_;
v_openDecls_534_ = v_openDecls_367_;
v_initHeartbeats_535_ = v___x_385_;
v_maxHeartbeats_536_ = v___x_370_;
v_quotContext_537_ = v___x_371_;
v_currMacroScope_538_ = v___x_372_;
v_cancelTk_x3f_539_ = v_cancelTk_x3f_355_;
v_inheritedTraceOptions_540_ = v___x_551_;
v_currRecDepth_541_ = v___x_345_;
v_ref_542_ = v___x_373_;
v_suppressElabErrors_543_ = v___x_341_;
v_checkDeprecated_544_ = v___x_375_;
v_isRecordingDeps_545_ = v___x_341_;
goto v___jp_530_;
}
else
{
v___y_554_ = v___x_341_;
goto v___jp_553_;
}
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_358_ = lean_io_error_to_string(v_a_357_);
v___x_359_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
v___x_360_ = l_Lean_MessageData_ofFormat(v___x_359_);
lean_inc(v_ref_354_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_ref_354_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
v___jp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_mk_io_user_error(v_a_364_);
v_a_357_ = v___x_365_;
goto v___jp_356_;
}
v___jp_387_:
{
lean_object* v_toCold_393_; lean_object* v_currRecDepth_394_; lean_object* v_ref_395_; uint8_t v_suppressElabErrors_396_; uint8_t v_checkDeprecated_397_; uint8_t v_isRecordingDeps_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_489_; 
v_toCold_393_ = lean_ctor_get(v___y_391_, 0);
v_currRecDepth_394_ = lean_ctor_get(v___y_391_, 1);
v_ref_395_ = lean_ctor_get(v___y_391_, 2);
v_suppressElabErrors_396_ = lean_ctor_get_uint8(v___y_391_, sizeof(void*)*3 + 2);
v_checkDeprecated_397_ = lean_ctor_get_uint8(v___y_391_, sizeof(void*)*3 + 3);
v_isRecordingDeps_398_ = lean_ctor_get_uint8(v___y_391_, sizeof(void*)*3 + 4);
v_isSharedCheck_489_ = !lean_is_exclusive(v___y_391_);
if (v_isSharedCheck_489_ == 0)
{
v___x_400_ = v___y_391_;
v_isShared_401_ = v_isSharedCheck_489_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_ref_395_);
lean_inc(v_currRecDepth_394_);
lean_inc(v_toCold_393_);
lean_dec(v___y_391_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_489_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_fileName_402_; lean_object* v_fileMap_403_; lean_object* v_currNamespace_404_; lean_object* v_openDecls_405_; lean_object* v_initHeartbeats_406_; lean_object* v_maxHeartbeats_407_; lean_object* v_quotContext_408_; lean_object* v_currMacroScope_409_; lean_object* v_cancelTk_x3f_410_; lean_object* v_inheritedTraceOptions_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_486_; 
v_fileName_402_ = lean_ctor_get(v_toCold_393_, 0);
v_fileMap_403_ = lean_ctor_get(v_toCold_393_, 1);
v_currNamespace_404_ = lean_ctor_get(v_toCold_393_, 4);
v_openDecls_405_ = lean_ctor_get(v_toCold_393_, 5);
v_initHeartbeats_406_ = lean_ctor_get(v_toCold_393_, 6);
v_maxHeartbeats_407_ = lean_ctor_get(v_toCold_393_, 7);
v_quotContext_408_ = lean_ctor_get(v_toCold_393_, 8);
v_currMacroScope_409_ = lean_ctor_get(v_toCold_393_, 9);
v_cancelTk_x3f_410_ = lean_ctor_get(v_toCold_393_, 10);
v_inheritedTraceOptions_411_ = lean_ctor_get(v_toCold_393_, 11);
v_isSharedCheck_486_ = !lean_is_exclusive(v_toCold_393_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; lean_object* v_unused_488_; 
v_unused_487_ = lean_ctor_get(v_toCold_393_, 3);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_toCold_393_, 2);
lean_dec(v_unused_488_);
v___x_413_ = v_toCold_393_;
v_isShared_414_ = v_isSharedCheck_486_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_inheritedTraceOptions_411_);
lean_inc(v_cancelTk_x3f_410_);
lean_inc(v_currMacroScope_409_);
lean_inc(v_quotContext_408_);
lean_inc(v_maxHeartbeats_407_);
lean_inc(v_initHeartbeats_406_);
lean_inc(v_openDecls_405_);
lean_inc(v_currNamespace_404_);
lean_inc(v_fileMap_403_);
lean_inc(v_fileName_402_);
lean_dec(v_toCold_393_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_486_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__1(v___y_389_, v___y_388_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 3, v___x_415_);
lean_ctor_set(v___x_413_, 2, v___y_389_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_fileName_402_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_fileMap_403_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v___y_389_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_currNamespace_404_);
lean_ctor_set(v_reuseFailAlloc_485_, 5, v_openDecls_405_);
lean_ctor_set(v_reuseFailAlloc_485_, 6, v_initHeartbeats_406_);
lean_ctor_set(v_reuseFailAlloc_485_, 7, v_maxHeartbeats_407_);
lean_ctor_set(v_reuseFailAlloc_485_, 8, v_quotContext_408_);
lean_ctor_set(v_reuseFailAlloc_485_, 9, v_currMacroScope_409_);
lean_ctor_set(v_reuseFailAlloc_485_, 10, v_cancelTk_x3f_410_);
lean_ctor_set(v_reuseFailAlloc_485_, 11, v_inheritedTraceOptions_411_);
v___x_417_ = v_reuseFailAlloc_485_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_417_);
v___x_419_ = v___x_400_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_currRecDepth_394_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_ref_395_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*3 + 2, v_suppressElabErrors_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*3 + 3, v_checkDeprecated_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*3 + 4, v_isRecordingDeps_398_);
v___x_419_ = v_reuseFailAlloc_484_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_ctor_set_uint16(v___x_419_, sizeof(void*)*3, v___y_390_);
v___x_420_ = lean_st_mk_ref(v___x_368_);
lean_inc(v___x_420_);
v___x_421_ = lean_apply_5(v_x_336_, v___x_348_, v___x_420_, v___x_419_, v___y_392_, lean_box(0));
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_468_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_468_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_468_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_468_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_traceState_429_; lean_object* v_traceState_430_; lean_object* v_env_431_; lean_object* v_messages_432_; lean_object* v_scopes_433_; lean_object* v_usedQuotCtxts_434_; lean_object* v_nextMacroScope_435_; lean_object* v_maxRecDepth_436_; lean_object* v_ngen_437_; lean_object* v_auxDeclNGen_438_; lean_object* v_infoState_439_; lean_object* v_snapshotTasks_440_; lean_object* v_prevLinterStates_441_; lean_object* v_codeQualityEntryTasks_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_466_; 
v___x_426_ = lean_st_ref_get(v___x_420_);
lean_dec(v___x_420_);
lean_dec(v___x_426_);
v___x_427_ = lean_st_ref_get(v___x_386_);
lean_dec(v___x_386_);
v___x_428_ = lean_st_ref_take(v_a_338_);
v_traceState_429_ = lean_ctor_get(v___x_428_, 9);
lean_inc_ref(v_traceState_429_);
v_traceState_430_ = lean_ctor_get(v___x_427_, 4);
lean_inc_ref(v_traceState_430_);
v_env_431_ = lean_ctor_get(v___x_428_, 0);
v_messages_432_ = lean_ctor_get(v___x_428_, 1);
v_scopes_433_ = lean_ctor_get(v___x_428_, 2);
v_usedQuotCtxts_434_ = lean_ctor_get(v___x_428_, 3);
v_nextMacroScope_435_ = lean_ctor_get(v___x_428_, 4);
v_maxRecDepth_436_ = lean_ctor_get(v___x_428_, 5);
v_ngen_437_ = lean_ctor_get(v___x_428_, 6);
v_auxDeclNGen_438_ = lean_ctor_get(v___x_428_, 7);
v_infoState_439_ = lean_ctor_get(v___x_428_, 8);
v_snapshotTasks_440_ = lean_ctor_get(v___x_428_, 10);
v_prevLinterStates_441_ = lean_ctor_get(v___x_428_, 11);
v_codeQualityEntryTasks_442_ = lean_ctor_get(v___x_428_, 12);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v___x_428_, 9);
lean_dec(v_unused_467_);
v___x_444_ = v___x_428_;
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_codeQualityEntryTasks_442_);
lean_inc(v_prevLinterStates_441_);
lean_inc(v_snapshotTasks_440_);
lean_inc(v_infoState_439_);
lean_inc(v_auxDeclNGen_438_);
lean_inc(v_ngen_437_);
lean_inc(v_maxRecDepth_436_);
lean_inc(v_nextMacroScope_435_);
lean_inc(v_usedQuotCtxts_434_);
lean_inc(v_scopes_433_);
lean_inc(v_messages_432_);
lean_inc(v_env_431_);
lean_dec(v___x_428_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_messages_446_; uint64_t v_tid_447_; lean_object* v_traces_448_; lean_object* v_traces_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_465_; 
v_messages_446_ = lean_ctor_get(v___x_427_, 7);
lean_inc_ref(v_messages_446_);
lean_dec(v___x_427_);
v_tid_447_ = lean_ctor_get_uint64(v_traceState_429_, sizeof(void*)*1);
v_traces_448_ = lean_ctor_get(v_traceState_429_, 0);
lean_inc_ref(v_traces_448_);
lean_dec_ref(v_traceState_429_);
v_traces_449_ = lean_ctor_get(v_traceState_430_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v_traceState_430_);
if (v_isSharedCheck_465_ == 0)
{
v___x_451_ = v_traceState_430_;
v_isShared_452_ = v_isSharedCheck_465_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_traces_449_);
lean_dec(v_traceState_430_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_465_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_453_ = l_Lean_MessageLog_append(v_messages_432_, v_messages_446_);
v___x_454_ = l_Lean_PersistentArray_append___redArg(v_traces_448_, v_traces_449_);
lean_dec_ref(v_traces_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_454_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_464_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
lean_ctor_set_uint64(v___x_456_, sizeof(void*)*1, v_tid_447_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 9, v___x_456_);
lean_ctor_set(v___x_444_, 1, v___x_453_);
v___x_458_ = v___x_444_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_env_431_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_scopes_433_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_usedQuotCtxts_434_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_nextMacroScope_435_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_maxRecDepth_436_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_ngen_437_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_auxDeclNGen_438_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_infoState_439_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 10, v_snapshotTasks_440_);
lean_ctor_set(v_reuseFailAlloc_463_, 11, v_prevLinterStates_441_);
lean_ctor_set(v_reuseFailAlloc_463_, 12, v_codeQualityEntryTasks_442_);
v___x_458_ = v_reuseFailAlloc_463_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_st_ref_put(v_a_338_, v___x_458_);
if (v_isShared_425_ == 0)
{
v___x_461_ = v___x_424_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_422_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_469_; 
lean_dec(v___x_420_);
lean_dec(v___x_386_);
v_a_469_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_421_, 1);
if (lean_obj_tag(v_a_469_) == 0)
{
lean_object* v_msg_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_msg_470_ = lean_ctor_get(v_a_469_, 1);
lean_inc_ref(v_msg_470_);
lean_dec_ref_known(v_a_469_, 2);
v___x_471_ = l_Lean_MessageData_toString(v_msg_470_);
v___x_472_ = lean_mk_io_user_error(v___x_471_);
v_a_357_ = v___x_472_;
goto v___jp_356_;
}
else
{
lean_object* v_id_473_; lean_object* v___x_474_; 
v_id_473_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_id_473_);
lean_dec_ref_known(v_a_469_, 2);
v___x_474_ = l_Lean_InternalExceptionId_getName(v_id_473_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_id_473_);
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_477_ = l_Lean_Name_toString(v_a_475_, v___x_343_);
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
lean_dec_ref(v___x_477_);
v_a_364_ = v___x_478_;
goto v___jp_363_;
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec_ref_known(v___x_474_, 1);
v___x_479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23));
v___x_480_ = l_Nat_reprFast(v_id_473_);
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v_a_364_ = v___x_483_;
goto v___jp_363_;
}
}
}
}
}
}
}
}
v___jp_490_:
{
lean_object* v___x_497_; lean_object* v_env_498_; lean_object* v_nextMacroScope_499_; lean_object* v_ngen_500_; lean_object* v_auxDeclNGen_501_; lean_object* v_traceState_502_; lean_object* v_recordedDeps_503_; lean_object* v_messages_504_; lean_object* v_infoState_505_; lean_object* v_snapshotTasks_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_515_; 
v___x_497_ = lean_st_ref_take(v___y_495_);
v_env_498_ = lean_ctor_get(v___x_497_, 0);
v_nextMacroScope_499_ = lean_ctor_get(v___x_497_, 1);
v_ngen_500_ = lean_ctor_get(v___x_497_, 2);
v_auxDeclNGen_501_ = lean_ctor_get(v___x_497_, 3);
v_traceState_502_ = lean_ctor_get(v___x_497_, 4);
v_recordedDeps_503_ = lean_ctor_get(v___x_497_, 6);
v_messages_504_ = lean_ctor_get(v___x_497_, 7);
v_infoState_505_ = lean_ctor_get(v___x_497_, 8);
v_snapshotTasks_506_ = lean_ctor_get(v___x_497_, 9);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v___x_497_, 5);
lean_dec(v_unused_516_);
v___x_508_ = v___x_497_;
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snapshotTasks_506_);
lean_inc(v_infoState_505_);
lean_inc(v_messages_504_);
lean_inc(v_recordedDeps_503_);
lean_inc(v_traceState_502_);
lean_inc(v_auxDeclNGen_501_);
lean_inc(v_ngen_500_);
lean_inc(v_nextMacroScope_499_);
lean_inc(v_env_498_);
lean_dec(v___x_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = l_Lean_Kernel_enableDiag(v_env_498_, v___y_492_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 5, v___x_380_);
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_nextMacroScope_499_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_ngen_500_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_auxDeclNGen_501_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_traceState_502_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v_recordedDeps_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 7, v_messages_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 8, v_infoState_505_);
lean_ctor_set(v_reuseFailAlloc_514_, 9, v_snapshotTasks_506_);
v___x_512_ = v_reuseFailAlloc_514_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; 
v___x_513_ = lean_st_ref_put(v___y_495_, v___x_512_);
v___y_388_ = v___y_493_;
v___y_389_ = v___y_494_;
v___y_390_ = v___y_496_;
v___y_391_ = v___y_491_;
v___y_392_ = v___y_495_;
goto v___jp_387_;
}
}
}
v___jp_517_:
{
uint16_t v___x_522_; lean_object* v___x_523_; lean_object* v_env_524_; uint8_t v___x_525_; uint16_t v___x_526_; uint16_t v___x_527_; uint16_t v___x_528_; uint8_t v___x_529_; 
v___x_522_ = l_Lean_OptionFlags_ofOptions(v___y_521_);
v___x_523_ = lean_st_ref_get(v___y_520_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_523_);
v___x_525_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_524_);
lean_dec_ref(v_env_524_);
v___x_526_ = 512;
v___x_527_ = lean_uint16_land(v___x_522_, v___x_526_);
v___x_528_ = 0;
v___x_529_ = lean_uint16_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
if (v___x_525_ == 0)
{
v___y_491_ = v___y_518_;
v___y_492_ = v___x_343_;
v___y_493_ = v___y_519_;
v___y_494_ = v___y_521_;
v___y_495_ = v___y_520_;
v___y_496_ = v___x_522_;
goto v___jp_490_;
}
else
{
v___y_388_ = v___y_519_;
v___y_389_ = v___y_521_;
v___y_390_ = v___x_522_;
v___y_391_ = v___y_518_;
v___y_392_ = v___y_520_;
goto v___jp_387_;
}
}
else
{
if (v___x_525_ == 0)
{
v___y_388_ = v___y_519_;
v___y_389_ = v___y_521_;
v___y_390_ = v___x_522_;
v___y_391_ = v___y_518_;
v___y_392_ = v___y_520_;
goto v___jp_387_;
}
else
{
v___y_491_ = v___y_518_;
v___y_492_ = v___x_341_;
v___y_493_ = v___y_519_;
v___y_494_ = v___y_521_;
v___y_495_ = v___y_520_;
v___y_496_ = v___x_522_;
goto v___jp_490_;
}
}
}
v___jp_530_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_546_ = l_Lean_maxRecDepth;
v___x_547_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25);
lean_inc(v_cancelTk_x3f_539_);
lean_inc(v_currMacroScope_538_);
lean_inc(v_quotContext_537_);
lean_inc(v_maxHeartbeats_536_);
lean_inc_ref(v_fileMap_532_);
lean_inc_ref(v_fileName_531_);
v___x_548_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_548_, 0, v_fileName_531_);
lean_ctor_set(v___x_548_, 1, v_fileMap_532_);
lean_ctor_set(v___x_548_, 2, v___x_369_);
lean_ctor_set(v___x_548_, 3, v___x_547_);
lean_ctor_set(v___x_548_, 4, v_currNamespace_533_);
lean_ctor_set(v___x_548_, 5, v_openDecls_534_);
lean_ctor_set(v___x_548_, 6, v_initHeartbeats_535_);
lean_ctor_set(v___x_548_, 7, v_maxHeartbeats_536_);
lean_ctor_set(v___x_548_, 8, v_quotContext_537_);
lean_ctor_set(v___x_548_, 9, v_currMacroScope_538_);
lean_ctor_set(v___x_548_, 10, v_cancelTk_x3f_539_);
lean_ctor_set(v___x_548_, 11, v_inheritedTraceOptions_540_);
lean_inc(v_ref_542_);
v___x_549_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v_currRecDepth_541_);
lean_ctor_set(v___x_549_, 2, v_ref_542_);
lean_ctor_set_uint16(v___x_549_, sizeof(void*)*3, v___x_374_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*3 + 2, v_suppressElabErrors_543_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*3 + 3, v_checkDeprecated_544_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*3 + 4, v_isRecordingDeps_545_);
lean_inc(v___x_386_);
v___y_518_ = v___x_549_;
v___y_519_ = v___x_546_;
v___y_520_ = v___x_386_;
v___y_521_ = v_opts_334_;
goto v___jp_517_;
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v_env_556_; lean_object* v_nextMacroScope_557_; lean_object* v_ngen_558_; lean_object* v_auxDeclNGen_559_; lean_object* v_traceState_560_; lean_object* v_recordedDeps_561_; lean_object* v_messages_562_; lean_object* v_infoState_563_; lean_object* v_snapshotTasks_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
v___x_555_ = lean_st_ref_take(v___x_386_);
v_env_556_ = lean_ctor_get(v___x_555_, 0);
v_nextMacroScope_557_ = lean_ctor_get(v___x_555_, 1);
v_ngen_558_ = lean_ctor_get(v___x_555_, 2);
v_auxDeclNGen_559_ = lean_ctor_get(v___x_555_, 3);
v_traceState_560_ = lean_ctor_get(v___x_555_, 4);
v_recordedDeps_561_ = lean_ctor_get(v___x_555_, 6);
v_messages_562_ = lean_ctor_get(v___x_555_, 7);
v_infoState_563_ = lean_ctor_get(v___x_555_, 8);
v_snapshotTasks_564_ = lean_ctor_get(v___x_555_, 9);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v___x_555_, 5);
lean_dec(v_unused_574_);
v___x_566_ = v___x_555_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_snapshotTasks_564_);
lean_inc(v_infoState_563_);
lean_inc(v_messages_562_);
lean_inc(v_recordedDeps_561_);
lean_inc(v_traceState_560_);
lean_inc(v_auxDeclNGen_559_);
lean_inc(v_ngen_558_);
lean_inc(v_nextMacroScope_557_);
lean_inc(v_env_556_);
lean_dec(v___x_555_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Lean_Kernel_enableDiag(v_env_556_, v___y_554_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 5, v___x_380_);
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_nextMacroScope_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_ngen_558_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_auxDeclNGen_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_traceState_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_recordedDeps_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_messages_562_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_infoState_563_);
lean_ctor_set(v_reuseFailAlloc_572_, 9, v_snapshotTasks_564_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_st_ref_put(v___x_386_, v___x_570_);
v_fileName_531_ = v_fileName_352_;
v_fileMap_532_ = v_fileMap_353_;
v_currNamespace_533_ = v_currNamespace_366_;
v_openDecls_534_ = v_openDecls_367_;
v_initHeartbeats_535_ = v___x_385_;
v_maxHeartbeats_536_ = v___x_370_;
v_quotContext_537_ = v___x_371_;
v_currMacroScope_538_ = v___x_372_;
v_cancelTk_x3f_539_ = v_cancelTk_x3f_355_;
v_inheritedTraceOptions_540_ = v___x_551_;
v_currRecDepth_541_ = v___x_345_;
v_ref_542_ = v___x_373_;
v_suppressElabErrors_543_ = v___x_341_;
v_checkDeprecated_544_ = v___x_375_;
v_isRecordingDeps_545_ = v___x_341_;
goto v___jp_530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_578_, lean_object* v_mctx_579_, lean_object* v_lctx_580_, lean_object* v_opts_581_, lean_object* v_namingCtx_582_, lean_object* v_x_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_578_, v_mctx_579_, v_lctx_580_, v_opts_581_, v_namingCtx_582_, v_x_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_588_, lean_object* v_env_589_, lean_object* v_mctx_590_, lean_object* v_lctx_591_, lean_object* v_opts_592_, lean_object* v_namingCtx_593_, lean_object* v_x_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_589_, v_mctx_590_, v_lctx_591_, v_opts_592_, v_namingCtx_593_, v_x_594_, v_a_595_, v_a_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_599_, lean_object* v_env_600_, lean_object* v_mctx_601_, lean_object* v_lctx_602_, lean_object* v_opts_603_, lean_object* v_namingCtx_604_, lean_object* v_x_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_599_, v_env_600_, v_mctx_601_, v_lctx_602_, v_opts_603_, v_namingCtx_604_, v_x_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0(lean_object* v_00_u03b2_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___redArg(){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___redArg___boxed(lean_object* v___dummy_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___redArg();
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object* v_00_u03b2_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
return v___x_617_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Syntax_getKind(v_stx_621_);
if (lean_obj_tag(v___x_622_) == 1)
{
lean_object* v_pre_623_; 
v_pre_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_pre_623_);
if (lean_obj_tag(v_pre_623_) == 1)
{
lean_object* v_pre_624_; 
v_pre_624_ = lean_ctor_get(v_pre_623_, 0);
lean_inc(v_pre_624_);
if (lean_obj_tag(v_pre_624_) == 1)
{
lean_object* v_pre_625_; 
v_pre_625_ = lean_ctor_get(v_pre_624_, 0);
lean_inc(v_pre_625_);
if (lean_obj_tag(v_pre_625_) == 1)
{
lean_object* v_pre_626_; 
v_pre_626_ = lean_ctor_get(v_pre_625_, 0);
if (lean_obj_tag(v_pre_626_) == 0)
{
lean_object* v_str_627_; lean_object* v_str_628_; lean_object* v_str_629_; lean_object* v_str_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_str_627_ = lean_ctor_get(v___x_622_, 1);
lean_inc_ref(v_str_627_);
lean_dec_ref_known(v___x_622_, 2);
v_str_628_ = lean_ctor_get(v_pre_623_, 1);
lean_inc_ref(v_str_628_);
lean_dec_ref_known(v_pre_623_, 2);
v_str_629_ = lean_ctor_get(v_pre_624_, 1);
lean_inc_ref(v_str_629_);
lean_dec_ref_known(v_pre_624_, 2);
v_str_630_ = lean_ctor_get(v_pre_625_, 1);
lean_inc_ref(v_str_630_);
lean_dec_ref_known(v_pre_625_, 2);
v___x_631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_632_ = lean_string_dec_eq(v_str_630_, v___x_631_);
lean_dec_ref(v_str_630_);
if (v___x_632_ == 0)
{
lean_dec_ref(v_str_629_);
lean_dec_ref(v_str_628_);
lean_dec_ref(v_str_627_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_634_ = lean_string_dec_eq(v_str_629_, v___x_633_);
lean_dec_ref(v_str_629_);
if (v___x_634_ == 0)
{
lean_dec_ref(v_str_628_);
lean_dec_ref(v_str_627_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_636_ = lean_string_dec_eq(v_str_628_, v___x_635_);
lean_dec_ref(v_str_628_);
if (v___x_636_ == 0)
{
lean_dec_ref(v_str_627_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_638_ = lean_string_dec_eq(v_str_627_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_640_ = lean_string_dec_eq(v_str_627_, v___x_639_);
lean_dec_ref(v_str_627_);
return v___x_640_;
}
else
{
lean_dec_ref(v_str_627_);
return v___x_638_;
}
}
}
}
}
else
{
uint8_t v___x_641_; 
lean_dec_ref_known(v_pre_625_, 2);
lean_dec_ref_known(v_pre_624_, 2);
lean_dec_ref_known(v_pre_623_, 2);
lean_dec_ref_known(v___x_622_, 2);
v___x_641_ = 0;
return v___x_641_;
}
}
else
{
uint8_t v___x_642_; 
lean_dec(v_pre_625_);
lean_dec_ref_known(v_pre_624_, 2);
lean_dec_ref_known(v_pre_623_, 2);
lean_dec_ref_known(v___x_622_, 2);
v___x_642_ = 0;
return v___x_642_;
}
}
else
{
uint8_t v___x_643_; 
lean_dec(v_pre_624_);
lean_dec_ref_known(v_pre_623_, 2);
lean_dec_ref_known(v___x_622_, 2);
v___x_643_ = 0;
return v___x_643_;
}
}
else
{
uint8_t v___x_644_; 
lean_dec_ref_known(v___x_622_, 2);
lean_dec(v_pre_623_);
v___x_644_ = 0;
return v___x_644_;
}
}
else
{
uint8_t v___x_645_; 
lean_dec(v___x_622_);
v___x_645_ = 0;
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(lean_object* v_x_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_obj_tag_nat(v_x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl___boxed(lean_object* v_x_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(v_x_651_);
lean_dec(v_x_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_653_, lean_object* v_k_654_){
_start:
{
if (lean_obj_tag(v_t_653_) == 0)
{
lean_object* v_tacticSeq_655_; lean_object* v_insertPos_656_; lean_object* v___x_657_; 
v_tacticSeq_655_ = lean_ctor_get(v_t_653_, 0);
lean_inc(v_tacticSeq_655_);
v_insertPos_656_ = lean_ctor_get(v_t_653_, 1);
lean_inc(v_insertPos_656_);
lean_dec_ref_known(v_t_653_, 2);
v___x_657_ = lean_apply_2(v_k_654_, v_tacticSeq_655_, v_insertPos_656_);
return v___x_657_;
}
else
{
return v_k_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_658_, lean_object* v_ctorIdx_659_, lean_object* v_t_660_, lean_object* v_h_661_, lean_object* v_k_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_660_, v_k_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_664_, lean_object* v_ctorIdx_665_, lean_object* v_t_666_, lean_object* v_h_667_, lean_object* v_k_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_664_, v_ctorIdx_665_, v_t_666_, v_h_667_, v_k_668_);
lean_dec(v_ctorIdx_665_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_670_, lean_object* v_unsolvedGoal_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_670_, v_unsolvedGoal_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_673_, lean_object* v_t_674_, lean_object* v_h_675_, lean_object* v_unsolvedGoal_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_674_, v_unsolvedGoal_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_678_, lean_object* v_sorryTactic_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_678_, v_sorryTactic_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_681_, lean_object* v_t_682_, lean_object* v_h_683_, lean_object* v_sorryTactic_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_682_, v_sorryTactic_684_);
return v___x_685_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_689_; lean_object* v___x_690_; 
v___x_689_ = 32;
v___x_690_ = lean_box_uint32(v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_691_, lean_object* v_fileMap_692_){
_start:
{
uint8_t v___x_693_; lean_object* v___x_694_; 
v___x_693_ = 0;
v___x_694_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_691_, v___x_693_);
if (lean_obj_tag(v___x_694_) == 1)
{
lean_object* v_val_695_; lean_object* v___x_696_; 
v_val_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_val_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_691_, v___x_693_);
if (lean_obj_tag(v___x_696_) == 1)
{
lean_object* v_val_697_; lean_object* v_startPos_698_; lean_object* v_line_699_; lean_object* v_column_700_; lean_object* v_endPos_701_; lean_object* v_line_702_; uint8_t v___x_703_; 
v_val_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v___x_696_, 1);
lean_inc_ref(v_fileMap_692_);
v_startPos_698_ = l_Lean_FileMap_toPosition(v_fileMap_692_, v_val_695_);
lean_dec(v_val_695_);
v_line_699_ = lean_ctor_get(v_startPos_698_, 0);
lean_inc(v_line_699_);
v_column_700_ = lean_ctor_get(v_startPos_698_, 1);
lean_inc(v_column_700_);
lean_dec_ref(v_startPos_698_);
v_endPos_701_ = l_Lean_FileMap_toPosition(v_fileMap_692_, v_val_697_);
lean_dec(v_val_697_);
v_line_702_ = lean_ctor_get(v_endPos_701_, 0);
lean_inc(v_line_702_);
lean_dec_ref(v_endPos_701_);
v___x_703_ = lean_nat_dec_eq(v_line_699_, v_line_702_);
lean_dec(v_line_702_);
lean_dec(v_line_699_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_705_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_706_ = l_List_replicateTR___redArg(v_column_700_, v___x_705_);
v___x_707_ = lean_string_mk(v___x_706_);
v___x_708_ = lean_string_append(v___x_704_, v___x_707_);
lean_dec_ref(v___x_707_);
return v___x_708_;
}
else
{
lean_object* v___x_709_; 
lean_dec(v_column_700_);
v___x_709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_709_;
}
}
else
{
lean_object* v___x_710_; 
lean_dec(v___x_696_);
lean_dec(v_val_695_);
lean_dec_ref(v_fileMap_692_);
v___x_710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_710_;
}
}
else
{
lean_object* v___x_711_; 
lean_dec(v___x_694_);
lean_dec_ref(v_fileMap_692_);
v___x_711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_712_, lean_object* v_fileMap_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_712_, v_fileMap_713_);
lean_dec(v_tacticSeq_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_721_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
lean_inc(v_p_719_);
v___x_722_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v_p_719_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
lean_ctor_set(v___x_722_, 3, v_p_719_);
v___x_723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_720_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_start_727_; lean_object* v_stop_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
v___x_725_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_726_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
v_start_727_ = lean_ctor_get(v_range_724_, 0);
v_stop_728_ = lean_ctor_get(v_range_724_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_range_724_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v_range_724_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_stop_728_);
lean_inc(v_start_727_);
lean_dec(v_range_724_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_732_, 0, v___x_726_);
lean_ctor_set(v___x_732_, 1, v_start_727_);
lean_ctor_set(v___x_732_, 2, v___x_726_);
lean_ctor_set(v___x_732_, 3, v_stop_728_);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 2);
lean_ctor_set(v___x_730_, 1, v___x_725_);
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_725_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_737_, lean_object* v_nc_x3f_738_, lean_object* v_msg_739_, lean_object* v_acc_740_){
_start:
{
switch(lean_obj_tag(v_msg_739_))
{
case 3:
{
lean_object* v_a_741_; lean_object* v_a_742_; lean_object* v___x_743_; 
lean_dec(v_mc_x3f_737_);
v_a_741_ = lean_ctor_get(v_msg_739_, 0);
v_a_742_ = lean_ctor_get(v_msg_739_, 1);
lean_inc_ref(v_a_741_);
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v_a_741_);
v_mc_x3f_737_ = v___x_743_;
v_msg_739_ = v_a_742_;
goto _start;
}
case 4:
{
lean_object* v_a_745_; lean_object* v_a_746_; lean_object* v___x_747_; 
lean_dec(v_nc_x3f_738_);
v_a_745_ = lean_ctor_get(v_msg_739_, 0);
v_a_746_ = lean_ctor_get(v_msg_739_, 1);
lean_inc_ref(v_a_745_);
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v_a_745_);
v_nc_x3f_738_ = v___x_747_;
v_msg_739_ = v_a_746_;
goto _start;
}
case 5:
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v_msg_739_, 1);
v_msg_739_ = v_a_749_;
goto _start;
}
case 6:
{
lean_object* v_a_751_; 
v_a_751_ = lean_ctor_get(v_msg_739_, 0);
v_msg_739_ = v_a_751_;
goto _start;
}
case 8:
{
lean_object* v_a_753_; 
v_a_753_ = lean_ctor_get(v_msg_739_, 1);
v_msg_739_ = v_a_753_;
goto _start;
}
case 7:
{
lean_object* v_a_755_; lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_755_ = lean_ctor_get(v_msg_739_, 0);
v_a_756_ = lean_ctor_get(v_msg_739_, 1);
lean_inc(v_nc_x3f_738_);
lean_inc(v_mc_x3f_737_);
v___x_757_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_737_, v_nc_x3f_738_, v_a_755_, v_acc_740_);
v_msg_739_ = v_a_756_;
v_acc_740_ = v___x_757_;
goto _start;
}
case 2:
{
lean_object* v_a_759_; 
v_a_759_ = lean_ctor_get(v_msg_739_, 1);
v_msg_739_ = v_a_759_;
goto _start;
}
case 9:
{
lean_object* v_msg_761_; lean_object* v_children_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_msg_761_ = lean_ctor_get(v_msg_739_, 1);
v_children_762_ = lean_ctor_get(v_msg_739_, 2);
lean_inc(v_nc_x3f_738_);
lean_inc(v_mc_x3f_737_);
v___x_763_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_737_, v_nc_x3f_738_, v_msg_761_, v_acc_740_);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_array_get_size(v_children_762_);
v___x_766_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v_nc_x3f_738_);
lean_dec(v_mc_x3f_737_);
return v___x_763_;
}
else
{
size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((size_t)0ULL);
v___x_768_ = lean_usize_of_nat(v___x_765_);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_737_, v_nc_x3f_738_, v_children_762_, v___x_767_, v___x_768_, v___x_763_);
return v___x_769_;
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_737_) == 1)
{
if (lean_obj_tag(v_nc_x3f_738_) == 1)
{
lean_object* v_a_770_; lean_object* v_val_771_; lean_object* v_val_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_a_770_ = lean_ctor_get(v_msg_739_, 0);
v_val_771_ = lean_ctor_get(v_mc_x3f_737_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v_mc_x3f_737_, 1);
v_val_772_ = lean_ctor_get(v_nc_x3f_738_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v_nc_x3f_738_, 1);
lean_inc(v_a_770_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_val_772_);
lean_ctor_set(v___x_773_, 1, v_a_770_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_val_771_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_array_push(v_acc_740_, v___x_774_);
return v___x_775_;
}
else
{
lean_dec_ref_known(v_mc_x3f_737_, 1);
lean_dec(v_nc_x3f_738_);
return v_acc_740_;
}
}
else
{
lean_dec(v_nc_x3f_738_);
lean_dec(v_mc_x3f_737_);
return v_acc_740_;
}
}
default: 
{
lean_dec(v_nc_x3f_738_);
lean_dec(v_mc_x3f_737_);
return v_acc_740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_776_, lean_object* v_nc_x3f_777_, lean_object* v_as_778_, size_t v_i_779_, size_t v_stop_780_, lean_object* v_b_781_){
_start:
{
uint8_t v___x_782_; 
v___x_782_ = lean_usize_dec_eq(v_i_779_, v_stop_780_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; size_t v___x_785_; size_t v___x_786_; 
v___x_783_ = lean_array_uget_borrowed(v_as_778_, v_i_779_);
lean_inc(v_nc_x3f_777_);
lean_inc(v_mc_x3f_776_);
v___x_784_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_776_, v_nc_x3f_777_, v___x_783_, v_b_781_);
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_add(v_i_779_, v___x_785_);
v_i_779_ = v___x_786_;
v_b_781_ = v___x_784_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_777_);
lean_dec(v_mc_x3f_776_);
return v_b_781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_788_, lean_object* v_nc_x3f_789_, lean_object* v_as_790_, lean_object* v_i_791_, lean_object* v_stop_792_, lean_object* v_b_793_){
_start:
{
size_t v_i_boxed_794_; size_t v_stop_boxed_795_; lean_object* v_res_796_; 
v_i_boxed_794_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_stop_boxed_795_ = lean_unbox_usize(v_stop_792_);
lean_dec(v_stop_792_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_788_, v_nc_x3f_789_, v_as_790_, v_i_boxed_794_, v_stop_boxed_795_, v_b_793_);
lean_dec_ref(v_as_790_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_797_, lean_object* v_nc_x3f_798_, lean_object* v_msg_799_, lean_object* v_acc_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_797_, v_nc_x3f_798_, v_msg_799_, v_acc_800_);
lean_dec_ref(v_msg_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_box(0);
v___x_806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_807_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_805_, v___x_805_, v_msg_804_, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_808_);
lean_dec_ref(v_msg_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_812_, lean_object* v_stx_813_){
_start:
{
lean_object* v___x_814_; 
lean_inc(v_stx_813_);
v___x_814_ = l_Lean_Syntax_getKind(v_stx_813_);
if (lean_obj_tag(v___x_814_) == 1)
{
lean_object* v_pre_815_; 
v_pre_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_pre_815_);
if (lean_obj_tag(v_pre_815_) == 1)
{
lean_object* v_pre_816_; 
v_pre_816_ = lean_ctor_get(v_pre_815_, 0);
lean_inc(v_pre_816_);
if (lean_obj_tag(v_pre_816_) == 1)
{
lean_object* v_pre_817_; 
v_pre_817_ = lean_ctor_get(v_pre_816_, 0);
lean_inc(v_pre_817_);
if (lean_obj_tag(v_pre_817_) == 1)
{
lean_object* v_pre_818_; 
v_pre_818_ = lean_ctor_get(v_pre_817_, 0);
if (lean_obj_tag(v_pre_818_) == 0)
{
lean_object* v_str_819_; lean_object* v_str_820_; lean_object* v_str_821_; lean_object* v_str_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_str_819_ = lean_ctor_get(v___x_814_, 1);
lean_inc_ref(v_str_819_);
lean_dec_ref_known(v___x_814_, 2);
v_str_820_ = lean_ctor_get(v_pre_815_, 1);
lean_inc_ref(v_str_820_);
lean_dec_ref_known(v_pre_815_, 2);
v_str_821_ = lean_ctor_get(v_pre_816_, 1);
lean_inc_ref(v_str_821_);
lean_dec_ref_known(v_pre_816_, 2);
v_str_822_ = lean_ctor_get(v_pre_817_, 1);
lean_inc_ref(v_str_822_);
lean_dec_ref_known(v_pre_817_, 2);
v___x_823_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_824_ = lean_string_dec_eq(v_str_822_, v___x_823_);
lean_dec_ref(v_str_822_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec_ref(v_str_821_);
lean_dec_ref(v_str_820_);
lean_dec_ref(v_str_819_);
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_827_ = lean_string_dec_eq(v_str_821_, v___x_826_);
lean_dec_ref(v_str_821_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec_ref(v_str_820_);
lean_dec_ref(v_str_819_);
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_828_ = lean_box(0);
return v___x_828_;
}
else
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_830_ = lean_string_dec_eq(v_str_820_, v___x_829_);
lean_dec_ref(v_str_820_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_dec_ref(v_str_819_);
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
else
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_833_ = lean_string_dec_eq(v_str_819_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_835_ = lean_string_dec_eq(v_str_819_, v___x_834_);
lean_dec_ref(v_str_819_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_836_ = lean_box(0);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v_body_838_; lean_object* v___y_840_; lean_object* v___x_843_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v_body_838_ = l_Lean_Syntax_getArg(v_stx_813_, v___x_837_);
v___x_843_ = l_Lean_Syntax_getTailPos_x3f(v_body_838_, v___x_833_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_unsigned_to_nat(2u);
v___x_845_ = l_Lean_Syntax_getArg(v_stx_813_, v___x_844_);
lean_dec(v_stx_813_);
v___x_846_ = l_Lean_Syntax_getPos_x3f(v___x_845_, v___x_833_);
lean_dec(v___x_845_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_stop_847_; 
v_stop_847_ = lean_ctor_get(v_range_812_, 1);
lean_inc(v_stop_847_);
lean_dec_ref(v_range_812_);
v___y_840_ = v_stop_847_;
goto v___jp_839_;
}
else
{
lean_object* v_val_848_; 
lean_dec_ref(v_range_812_);
v_val_848_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v___x_846_, 1);
v___y_840_ = v_val_848_;
goto v___jp_839_;
}
}
else
{
lean_object* v_val_849_; 
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v_val_849_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v___x_843_, 1);
v___y_840_ = v_val_849_;
goto v___jp_839_;
}
v___jp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_body_838_);
lean_ctor_set(v___x_841_, 1, v___y_840_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
}
else
{
lean_object* v___x_850_; lean_object* v_body_851_; lean_object* v___y_853_; uint8_t v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v_str_819_);
v___x_850_ = lean_unsigned_to_nat(0u);
v_body_851_ = l_Lean_Syntax_getArg(v_stx_813_, v___x_850_);
lean_dec(v_stx_813_);
v___x_856_ = 0;
v___x_857_ = l_Lean_Syntax_getTailPos_x3f(v_body_851_, v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_stop_858_; 
v_stop_858_ = lean_ctor_get(v_range_812_, 1);
lean_inc(v_stop_858_);
lean_dec_ref(v_range_812_);
v___y_853_ = v_stop_858_;
goto v___jp_852_;
}
else
{
lean_object* v_val_859_; 
lean_dec_ref(v_range_812_);
v_val_859_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v___x_857_, 1);
v___y_853_ = v_val_859_;
goto v___jp_852_;
}
v___jp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v_body_851_);
lean_ctor_set(v___x_854_, 1, v___y_853_);
v___x_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
}
}
}
}
else
{
lean_object* v___x_860_; 
lean_dec_ref_known(v_pre_817_, 2);
lean_dec_ref_known(v_pre_816_, 2);
lean_dec_ref_known(v_pre_815_, 2);
lean_dec_ref_known(v___x_814_, 2);
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_860_ = lean_box(0);
return v___x_860_;
}
}
else
{
lean_object* v___x_861_; 
lean_dec(v_pre_817_);
lean_dec_ref_known(v_pre_816_, 2);
lean_dec_ref_known(v_pre_815_, 2);
lean_dec_ref_known(v___x_814_, 2);
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_861_ = lean_box(0);
return v___x_861_;
}
}
else
{
lean_object* v___x_862_; 
lean_dec_ref_known(v_pre_815_, 2);
lean_dec(v_pre_816_);
lean_dec_ref_known(v___x_814_, 2);
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_862_ = lean_box(0);
return v___x_862_;
}
}
else
{
lean_object* v___x_863_; 
lean_dec_ref_known(v___x_814_, 2);
lean_dec(v_pre_815_);
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_863_ = lean_box(0);
return v___x_863_;
}
}
else
{
lean_object* v___x_864_; 
lean_dec(v___x_814_);
lean_dec(v_stx_813_);
lean_dec_ref(v_range_812_);
v___x_864_ = lean_box(0);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_868_, lean_object* v_stx_869_){
_start:
{
lean_object* v___x_870_; 
lean_inc(v_stx_869_);
lean_inc_ref(v_range_868_);
v___x_870_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_868_, v_stx_869_);
if (lean_obj_tag(v___x_870_) == 1)
{
lean_dec(v_stx_869_);
lean_dec_ref(v_range_868_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; size_t v_sz_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v_fst_877_; 
lean_dec(v___x_870_);
v___x_871_ = l_Lean_Syntax_getArgs(v_stx_869_);
lean_dec(v_stx_869_);
v___x_872_ = lean_box(0);
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_874_ = lean_array_size(v___x_871_);
v___x_875_ = ((size_t)0ULL);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_868_, v___x_871_, v_sz_874_, v___x_875_, v___x_873_);
lean_dec_ref(v___x_871_);
v_fst_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_fst_877_);
lean_dec_ref(v___x_876_);
if (lean_obj_tag(v_fst_877_) == 0)
{
return v___x_872_;
}
else
{
lean_object* v_val_878_; 
v_val_878_ = lean_ctor_get(v_fst_877_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v_fst_877_, 1);
return v_val_878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_879_, lean_object* v_as_880_, size_t v_sz_881_, size_t v_i_882_, lean_object* v_b_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = lean_usize_dec_lt(v_i_882_, v_sz_881_);
if (v___x_884_ == 0)
{
lean_dec_ref(v_range_879_);
lean_inc_ref(v_b_883_);
return v_b_883_;
}
else
{
lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_887_; 
v___x_885_ = lean_box(0);
v_a_886_ = lean_array_uget_borrowed(v_as_880_, v_i_882_);
lean_inc(v_a_886_);
lean_inc_ref(v_range_879_);
v___x_887_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_879_, v_a_886_);
if (lean_obj_tag(v___x_887_) == 1)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec_ref(v_range_879_);
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_885_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; size_t v___x_891_; size_t v___x_892_; 
lean_dec(v___x_887_);
v___x_890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_i_882_, v___x_891_);
v_i_882_ = v___x_892_;
v_b_883_ = v___x_890_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_894_, lean_object* v_as_895_, lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_b_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_900_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_894_, v_as_895_, v_sz_boxed_899_, v_i_boxed_900_, v_b_898_);
lean_dec_ref(v_b_898_);
lean_dec_ref(v_as_895_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_902_, lean_object* v_stx_903_){
_start:
{
uint8_t v___x_904_; lean_object* v___x_905_; 
v___x_904_ = 0;
v___x_905_ = l_Lean_Syntax_getRange_x3f(v_stx_903_, v___x_904_);
if (lean_obj_tag(v___x_905_) == 1)
{
lean_object* v_val_906_; uint8_t v___x_907_; 
v_val_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v___x_905_, 1);
v___x_907_ = l_Lean_Syntax_Range_includes(v_val_906_, v_range_902_, v___x_904_, v___x_904_);
lean_dec(v_val_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec(v_stx_903_);
lean_dec_ref(v_range_902_);
v___x_908_ = lean_box(0);
return v___x_908_;
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; size_t v_sz_911_; size_t v___x_912_; lean_object* v___x_913_; lean_object* v_fst_914_; 
v___x_909_ = l_Lean_Syntax_getArgs(v_stx_903_);
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_911_ = lean_array_size(v___x_909_);
v___x_912_ = ((size_t)0ULL);
lean_inc_ref(v_range_902_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_902_, v___x_909_, v_sz_911_, v___x_912_, v___x_910_);
lean_dec_ref(v___x_909_);
v_fst_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_fst_914_);
lean_dec_ref(v___x_913_);
if (lean_obj_tag(v_fst_914_) == 0)
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_902_, v_stx_903_);
return v___x_915_;
}
else
{
lean_object* v_val_916_; 
lean_dec(v_stx_903_);
lean_dec_ref(v_range_902_);
v_val_916_ = lean_ctor_get(v_fst_914_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v_fst_914_, 1);
return v_val_916_;
}
}
}
else
{
lean_object* v___x_917_; 
lean_dec(v___x_905_);
lean_dec(v_stx_903_);
lean_dec_ref(v_range_902_);
v___x_917_ = lean_box(0);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_918_, lean_object* v_as_919_, size_t v_sz_920_, size_t v_i_921_, lean_object* v_b_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_lt(v_i_921_, v_sz_920_);
if (v___x_923_ == 0)
{
lean_dec_ref(v_range_918_);
lean_inc_ref(v_b_922_);
return v_b_922_;
}
else
{
lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_926_; 
v___x_924_ = lean_box(0);
v_a_925_ = lean_array_uget_borrowed(v_as_919_, v_i_921_);
lean_inc(v_a_925_);
lean_inc_ref(v_range_918_);
v___x_926_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_918_, v_a_925_);
if (lean_obj_tag(v___x_926_) == 1)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec_ref(v_range_918_);
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_924_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; size_t v___x_930_; size_t v___x_931_; 
lean_dec(v___x_926_);
v___x_929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_921_, v___x_930_);
v_i_921_ = v___x_931_;
v_b_922_ = v___x_929_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_933_, lean_object* v_as_934_, lean_object* v_sz_935_, lean_object* v_i_936_, lean_object* v_b_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_935_);
lean_dec(v_sz_935_);
v_i_boxed_939_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_933_, v_as_934_, v_sz_boxed_938_, v_i_boxed_939_, v_b_937_);
lean_dec_ref(v_b_937_);
lean_dec_ref(v_as_934_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_941_, lean_object* v_range_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_942_, v_cmd_941_);
return v___x_943_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_opts_944_, lean_object* v_opt_945_){
_start:
{
lean_object* v_name_946_; lean_object* v_defValue_947_; lean_object* v_map_948_; lean_object* v___x_949_; 
v_name_946_ = lean_ctor_get(v_opt_945_, 0);
v_defValue_947_ = lean_ctor_get(v_opt_945_, 1);
v_map_948_ = lean_ctor_get(v_opts_944_, 0);
v___x_949_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_948_, v_name_946_);
if (lean_obj_tag(v___x_949_) == 0)
{
uint8_t v___x_950_; 
v___x_950_ = lean_unbox(v_defValue_947_);
return v___x_950_;
}
else
{
lean_object* v_val_951_; 
v_val_951_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v___x_949_, 1);
if (lean_obj_tag(v_val_951_) == 1)
{
uint8_t v_v_952_; 
v_v_952_ = lean_ctor_get_uint8(v_val_951_, 0);
lean_dec_ref_known(v_val_951_, 0);
return v_v_952_;
}
else
{
uint8_t v___x_953_; 
lean_dec(v_val_951_);
v___x_953_ = lean_unbox(v_defValue_947_);
return v___x_953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_opts_954_, lean_object* v_opt_955_){
_start:
{
uint8_t v_res_956_; lean_object* v_r_957_; 
v_res_956_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_954_, v_opt_955_);
lean_dec_ref(v_opt_955_);
lean_dec_ref(v_opts_954_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_958_, lean_object* v_info_959_, lean_object* v_acc_960_){
_start:
{
if (lean_obj_tag(v_info_959_) == 0)
{
lean_object* v_i_961_; lean_object* v_toElabInfo_962_; lean_object* v_mctxBefore_963_; lean_object* v_goalsBefore_964_; lean_object* v_stx_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_983_; 
v_i_961_ = lean_ctor_get(v_info_959_, 0);
lean_inc_ref(v_i_961_);
lean_dec_ref_known(v_info_959_, 1);
v_toElabInfo_962_ = lean_ctor_get(v_i_961_, 0);
lean_inc_ref(v_toElabInfo_962_);
v_mctxBefore_963_ = lean_ctor_get(v_i_961_, 1);
lean_inc_ref(v_mctxBefore_963_);
v_goalsBefore_964_ = lean_ctor_get(v_i_961_, 2);
lean_inc(v_goalsBefore_964_);
lean_dec_ref(v_i_961_);
v_stx_965_ = lean_ctor_get(v_toElabInfo_962_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v_toElabInfo_962_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v_toElabInfo_962_, 0);
lean_dec(v_unused_984_);
v___x_967_ = v_toElabInfo_962_;
v_isShared_968_ = v_isSharedCheck_983_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_stx_965_);
lean_dec(v_toElabInfo_962_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_983_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
uint8_t v___x_969_; 
lean_inc(v_stx_965_);
v___x_969_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_965_);
if (v___x_969_ == 0)
{
lean_del_object(v___x_967_);
lean_dec(v_stx_965_);
lean_dec(v_goalsBefore_964_);
lean_dec_ref(v_mctxBefore_963_);
return v_acc_960_;
}
else
{
lean_object* v___x_970_; 
v___x_970_ = l_List_head_x3f___redArg(v_goalsBefore_964_);
lean_dec(v_goalsBefore_964_);
if (lean_obj_tag(v___x_970_) == 1)
{
lean_object* v_toCommandContextInfo_971_; lean_object* v_val_972_; lean_object* v_env_973_; lean_object* v_options_974_; lean_object* v_currNamespace_975_; lean_object* v_openDecls_976_; lean_object* v_namingCtx_978_; 
v_toCommandContextInfo_971_ = lean_ctor_get(v_ctx_958_, 0);
v_val_972_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_val_972_);
lean_dec_ref_known(v___x_970_, 1);
v_env_973_ = lean_ctor_get(v_toCommandContextInfo_971_, 0);
v_options_974_ = lean_ctor_get(v_toCommandContextInfo_971_, 4);
v_currNamespace_975_ = lean_ctor_get(v_toCommandContextInfo_971_, 5);
v_openDecls_976_ = lean_ctor_get(v_toCommandContextInfo_971_, 6);
lean_inc(v_openDecls_976_);
lean_inc(v_currNamespace_975_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v_openDecls_976_);
lean_ctor_set(v___x_967_, 0, v_currNamespace_975_);
v_namingCtx_978_ = v___x_967_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_currNamespace_975_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_openDecls_976_);
v_namingCtx_978_ = v_reuseFailAlloc_982_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_box(1);
lean_inc_ref(v_options_974_);
lean_inc_ref(v_env_973_);
v___x_980_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v_stx_965_);
lean_ctor_set(v___x_980_, 2, v_env_973_);
lean_ctor_set(v___x_980_, 3, v_mctxBefore_963_);
lean_ctor_set(v___x_980_, 4, v_options_974_);
lean_ctor_set(v___x_980_, 5, v_namingCtx_978_);
lean_ctor_set(v___x_980_, 6, v_val_972_);
v___x_981_ = lean_array_push(v_acc_960_, v___x_980_);
return v___x_981_;
}
}
else
{
lean_dec(v___x_970_);
lean_del_object(v___x_967_);
lean_dec(v_stx_965_);
lean_dec_ref(v_mctxBefore_963_);
return v_acc_960_;
}
}
}
}
else
{
lean_dec_ref(v_info_959_);
return v_acc_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_985_, lean_object* v_info_986_, lean_object* v_acc_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_985_, v_info_986_, v_acc_987_);
lean_dec_ref(v_ctx_985_);
return v_res_988_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(lean_object* v_x_993_){
_start:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1));
v___x_995_ = lean_name_eq(v_x_993_, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___boxed(lean_object* v_x_996_){
_start:
{
uint8_t v_res_997_; lean_object* v_r_998_; 
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(v_x_996_);
lean_dec(v_x_996_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(lean_object* v_a_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
uint8_t v___x_1001_; 
v___x_1001_ = 0;
return v___x_1001_;
}
else
{
lean_object* v_key_1002_; lean_object* v_tail_1003_; lean_object* v_fst_1004_; lean_object* v_snd_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; uint8_t v___x_1008_; 
v_key_1002_ = lean_ctor_get(v_x_1000_, 0);
v_tail_1003_ = lean_ctor_get(v_x_1000_, 2);
v_fst_1004_ = lean_ctor_get(v_key_1002_, 0);
v_snd_1005_ = lean_ctor_get(v_key_1002_, 1);
v_fst_1006_ = lean_ctor_get(v_a_999_, 0);
v_snd_1007_ = lean_ctor_get(v_a_999_, 1);
v___x_1008_ = l_Lean_Syntax_instBEqRange_beq(v_fst_1004_, v_fst_1006_);
if (v___x_1008_ == 0)
{
v_x_1000_ = v_tail_1003_;
goto _start;
}
else
{
uint8_t v___x_1010_; 
v___x_1010_ = l_Lean_instBEqMVarId_beq(v_snd_1005_, v_snd_1007_);
if (v___x_1010_ == 0)
{
v_x_1000_ = v_tail_1003_;
goto _start;
}
else
{
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg___boxed(lean_object* v_a_1012_, lean_object* v_x_1013_){
_start:
{
uint8_t v_res_1014_; lean_object* v_r_1015_; 
v_res_1014_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1012_, v_x_1013_);
lean_dec(v_x_1013_);
lean_dec_ref(v_a_1012_);
v_r_1015_ = lean_box(v_res_1014_);
return v_r_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
if (lean_obj_tag(v_x_1017_) == 0)
{
return v_x_1016_;
}
else
{
lean_object* v_key_1018_; lean_object* v_value_1019_; lean_object* v_tail_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1047_; 
v_key_1018_ = lean_ctor_get(v_x_1017_, 0);
v_value_1019_ = lean_ctor_get(v_x_1017_, 1);
v_tail_1020_ = lean_ctor_get(v_x_1017_, 2);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_x_1017_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1022_ = v_x_1017_;
v_isShared_1023_ = v_isSharedCheck_1047_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_tail_1020_);
lean_inc(v_value_1019_);
lean_inc(v_key_1018_);
lean_dec(v_x_1017_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1047_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1026_; uint64_t v___x_1027_; uint64_t v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v_fold_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v_fst_1024_ = lean_ctor_get(v_key_1018_, 0);
v_snd_1025_ = lean_ctor_get(v_key_1018_, 1);
v___x_1026_ = lean_array_get_size(v_x_1016_);
v___x_1027_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1024_);
v___x_1028_ = l_Lean_instHashableMVarId_hash(v_snd_1025_);
v___x_1029_ = lean_uint64_mix_hash(v___x_1027_, v___x_1028_);
v___x_1030_ = 32ULL;
v___x_1031_ = lean_uint64_shift_right(v___x_1029_, v___x_1030_);
v_fold_1032_ = lean_uint64_xor(v___x_1029_, v___x_1031_);
v___x_1033_ = 16ULL;
v___x_1034_ = lean_uint64_shift_right(v_fold_1032_, v___x_1033_);
v___x_1035_ = lean_uint64_xor(v_fold_1032_, v___x_1034_);
v___x_1036_ = lean_uint64_to_usize(v___x_1035_);
v___x_1037_ = lean_usize_of_nat(v___x_1026_);
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_sub(v___x_1037_, v___x_1038_);
v___x_1040_ = lean_usize_land(v___x_1036_, v___x_1039_);
v___x_1041_ = lean_array_uget_borrowed(v_x_1016_, v___x_1040_);
lean_inc(v___x_1041_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 2, v___x_1041_);
v___x_1043_ = v___x_1022_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_key_1018_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_value_1019_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_array_uset(v_x_1016_, v___x_1040_, v___x_1043_);
v_x_1016_ = v___x_1044_;
v_x_1017_ = v_tail_1020_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1048_, lean_object* v_source_1049_, lean_object* v_target_1050_){
_start:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = lean_array_get_size(v_source_1049_);
v___x_1052_ = lean_nat_dec_lt(v_i_1048_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_dec_ref(v_source_1049_);
lean_dec(v_i_1048_);
return v_target_1050_;
}
else
{
lean_object* v_es_1053_; lean_object* v___x_1054_; lean_object* v_source_1055_; lean_object* v_target_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_es_1053_ = lean_array_fget(v_source_1049_, v_i_1048_);
v___x_1054_ = lean_box(0);
v_source_1055_ = lean_array_fset(v_source_1049_, v_i_1048_, v___x_1054_);
v_target_1056_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1050_, v_es_1053_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_i_1048_, v___x_1057_);
lean_dec(v_i_1048_);
v_i_1048_ = v___x_1058_;
v_source_1049_ = v_source_1055_;
v_target_1050_ = v_target_1056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(lean_object* v_data_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v_nbuckets_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1061_ = lean_array_get_size(v_data_1060_);
v___x_1062_ = lean_unsigned_to_nat(2u);
v_nbuckets_1063_ = lean_nat_mul(v___x_1061_, v___x_1062_);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_mk_array(v_nbuckets_1063_, v___x_1065_);
v___x_1067_ = lean_array_propagate_mark(v_data_1060_, v___x_1066_);
v___x_1068_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v___x_1064_, v_data_1060_, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v_m_1069_, lean_object* v_a_1070_, lean_object* v_b_1071_){
_start:
{
lean_object* v_size_1072_; lean_object* v_buckets_1073_; lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v___x_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v_fold_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; lean_object* v_bkt_1091_; uint8_t v___x_1092_; 
v_size_1072_ = lean_ctor_get(v_m_1069_, 0);
v_buckets_1073_ = lean_ctor_get(v_m_1069_, 1);
v_fst_1074_ = lean_ctor_get(v_a_1070_, 0);
v_snd_1075_ = lean_ctor_get(v_a_1070_, 1);
v___x_1076_ = lean_array_get_size(v_buckets_1073_);
v___x_1077_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1074_);
v___x_1078_ = l_Lean_instHashableMVarId_hash(v_snd_1075_);
v___x_1079_ = lean_uint64_mix_hash(v___x_1077_, v___x_1078_);
v___x_1080_ = 32ULL;
v___x_1081_ = lean_uint64_shift_right(v___x_1079_, v___x_1080_);
v_fold_1082_ = lean_uint64_xor(v___x_1079_, v___x_1081_);
v___x_1083_ = 16ULL;
v___x_1084_ = lean_uint64_shift_right(v_fold_1082_, v___x_1083_);
v___x_1085_ = lean_uint64_xor(v_fold_1082_, v___x_1084_);
v___x_1086_ = lean_uint64_to_usize(v___x_1085_);
v___x_1087_ = lean_usize_of_nat(v___x_1076_);
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_sub(v___x_1087_, v___x_1088_);
v___x_1090_ = lean_usize_land(v___x_1086_, v___x_1089_);
v_bkt_1091_ = lean_array_uget_borrowed(v_buckets_1073_, v___x_1090_);
v___x_1092_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1070_, v_bkt_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1113_; 
lean_inc_ref(v_buckets_1073_);
lean_inc(v_size_1072_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_m_1069_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1114_ = lean_ctor_get(v_m_1069_, 1);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_m_1069_, 0);
lean_dec(v_unused_1115_);
v___x_1094_ = v_m_1069_;
v_isShared_1095_ = v_isSharedCheck_1113_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v_m_1069_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1113_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v_size_x27_1097_; lean_object* v___x_1098_; lean_object* v_buckets_x27_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1096_ = lean_unsigned_to_nat(1u);
v_size_x27_1097_ = lean_nat_add(v_size_1072_, v___x_1096_);
lean_dec(v_size_1072_);
lean_inc(v_bkt_1091_);
v___x_1098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1098_, 0, v_a_1070_);
lean_ctor_set(v___x_1098_, 1, v_b_1071_);
lean_ctor_set(v___x_1098_, 2, v_bkt_1091_);
v_buckets_x27_1099_ = lean_array_uset(v_buckets_1073_, v___x_1090_, v___x_1098_);
v___x_1100_ = lean_unsigned_to_nat(4u);
v___x_1101_ = lean_nat_mul(v_size_x27_1097_, v___x_1100_);
v___x_1102_ = lean_unsigned_to_nat(3u);
v___x_1103_ = lean_nat_div(v___x_1101_, v___x_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_array_get_size(v_buckets_x27_1099_);
v___x_1105_ = lean_nat_dec_le(v___x_1103_, v___x_1104_);
lean_dec(v___x_1103_);
if (v___x_1105_ == 0)
{
lean_object* v_val_1106_; lean_object* v___x_1108_; 
v_val_1106_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_buckets_x27_1099_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_val_1106_);
lean_ctor_set(v___x_1094_, 0, v_size_x27_1097_);
v___x_1108_ = v___x_1094_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_size_x27_1097_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_val_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
else
{
lean_object* v___x_1111_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_buckets_x27_1099_);
lean_ctor_set(v___x_1094_, 0, v_size_x27_1097_);
v___x_1111_ = v___x_1094_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_size_x27_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_buckets_x27_1099_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_dec(v_b_1071_);
lean_dec_ref(v_a_1070_);
return v_m_1069_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_buckets_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; uint64_t v___x_1124_; uint64_t v___x_1125_; uint64_t v___x_1126_; uint64_t v_fold_1127_; uint64_t v___x_1128_; uint64_t v___x_1129_; uint64_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_buckets_1118_ = lean_ctor_get(v_m_1116_, 1);
v_fst_1119_ = lean_ctor_get(v_a_1117_, 0);
v_snd_1120_ = lean_ctor_get(v_a_1117_, 1);
v___x_1121_ = lean_array_get_size(v_buckets_1118_);
v___x_1122_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1119_);
v___x_1123_ = l_Lean_instHashableMVarId_hash(v_snd_1120_);
v___x_1124_ = lean_uint64_mix_hash(v___x_1122_, v___x_1123_);
v___x_1125_ = 32ULL;
v___x_1126_ = lean_uint64_shift_right(v___x_1124_, v___x_1125_);
v_fold_1127_ = lean_uint64_xor(v___x_1124_, v___x_1126_);
v___x_1128_ = 16ULL;
v___x_1129_ = lean_uint64_shift_right(v_fold_1127_, v___x_1128_);
v___x_1130_ = lean_uint64_xor(v_fold_1127_, v___x_1129_);
v___x_1131_ = lean_uint64_to_usize(v___x_1130_);
v___x_1132_ = lean_usize_of_nat(v___x_1121_);
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_sub(v___x_1132_, v___x_1133_);
v___x_1135_ = lean_usize_land(v___x_1131_, v___x_1134_);
v___x_1136_ = lean_array_uget_borrowed(v_buckets_1118_, v___x_1135_);
v___x_1137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1117_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object* v_m_1138_, lean_object* v_a_1139_){
_start:
{
uint8_t v_res_1140_; lean_object* v_r_1141_; 
v_res_1140_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1138_, v_a_1139_);
lean_dec_ref(v_a_1139_);
lean_dec_ref(v_m_1138_);
v_r_1141_ = lean_box(v_res_1140_);
return v_r_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object* v___x_1142_, lean_object* v_fst_1143_, lean_object* v_snd_1144_, lean_object* v___x_1145_, lean_object* v_as_1146_, size_t v_sz_1147_, size_t v_i_1148_, lean_object* v_b_1149_){
_start:
{
lean_object* v_a_1152_; uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_lt(v_i_1148_, v_sz_1147_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v___x_1145_);
lean_dec(v_snd_1144_);
lean_dec(v_fst_1143_);
lean_dec_ref(v___x_1142_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_b_1149_);
return v___x_1157_;
}
else
{
lean_object* v_a_1158_; lean_object* v_snd_1159_; lean_object* v_fst_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1196_; 
v_a_1158_ = lean_array_uget(v_as_1146_, v_i_1148_);
v_snd_1159_ = lean_ctor_get(v_a_1158_, 1);
v_fst_1160_ = lean_ctor_get(v_a_1158_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_a_1158_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1162_ = v_a_1158_;
v_isShared_1163_ = v_isSharedCheck_1196_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_snd_1159_);
lean_inc(v_fst_1160_);
lean_dec(v_a_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1196_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_fst_1164_; lean_object* v_snd_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1195_; 
v_fst_1164_ = lean_ctor_get(v_snd_1159_, 0);
v_snd_1165_ = lean_ctor_get(v_snd_1159_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_snd_1159_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1167_ = v_snd_1159_;
v_isShared_1168_ = v_isSharedCheck_1195_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snd_1165_);
lean_inc(v_fst_1164_);
lean_dec(v_snd_1159_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1195_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_fst_1169_; lean_object* v_snd_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1194_; 
v_fst_1169_ = lean_ctor_get(v_b_1149_, 0);
v_snd_1170_ = lean_ctor_get(v_b_1149_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_b_1149_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1172_ = v_b_1149_;
v_isShared_1173_ = v_isSharedCheck_1194_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_snd_1170_);
lean_inc(v_fst_1169_);
lean_dec(v_b_1149_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1194_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
lean_inc(v_snd_1165_);
lean_inc_ref(v___x_1142_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_snd_1165_);
lean_ctor_set(v___x_1172_, 0, v___x_1142_);
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_snd_1165_);
v___x_1175_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
uint8_t v___x_1176_; 
v___x_1176_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1170_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v_env_1177_; lean_object* v_mctx_1178_; lean_object* v_opts_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v_env_1177_ = lean_ctor_get(v_fst_1160_, 0);
lean_inc_ref(v_env_1177_);
v_mctx_1178_ = lean_ctor_get(v_fst_1160_, 1);
lean_inc_ref(v_mctx_1178_);
v_opts_1179_ = lean_ctor_get(v_fst_1160_, 3);
lean_inc_ref(v_opts_1179_);
lean_dec(v_fst_1160_);
v___x_1180_ = lean_box(0);
v___x_1181_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1170_, v___x_1175_, v___x_1180_);
lean_inc(v_snd_1144_);
lean_inc(v_fst_1143_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v_snd_1144_);
lean_ctor_set(v___x_1162_, 0, v_fst_1143_);
v___x_1183_ = v___x_1162_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_fst_1143_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_snd_1144_);
v___x_1183_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
lean_inc(v___x_1145_);
v___x_1184_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1145_);
lean_ctor_set(v___x_1184_, 2, v_env_1177_);
lean_ctor_set(v___x_1184_, 3, v_mctx_1178_);
lean_ctor_set(v___x_1184_, 4, v_opts_1179_);
lean_ctor_set(v___x_1184_, 5, v_fst_1164_);
lean_ctor_set(v___x_1184_, 6, v_snd_1165_);
v___x_1185_ = lean_array_push(v_fst_1169_, v___x_1184_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1181_);
lean_ctor_set(v___x_1167_, 0, v___x_1185_);
v___x_1187_ = v___x_1167_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1181_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
v_a_1152_ = v___x_1187_;
goto v___jp_1151_;
}
}
}
else
{
lean_object* v___x_1191_; 
lean_dec_ref(v___x_1175_);
lean_dec(v_snd_1165_);
lean_dec(v_fst_1164_);
lean_del_object(v___x_1162_);
lean_dec(v_fst_1160_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v_snd_1170_);
lean_ctor_set(v___x_1167_, 0, v_fst_1169_);
v___x_1191_ = v___x_1167_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_fst_1169_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_snd_1170_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_a_1152_ = v___x_1191_;
goto v___jp_1151_;
}
}
}
}
}
}
}
v___jp_1151_:
{
size_t v___x_1153_; size_t v___x_1154_; 
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_add(v_i_1148_, v___x_1153_);
v_i_1148_ = v___x_1154_;
v_b_1149_ = v_a_1152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object* v___x_1197_, lean_object* v_fst_1198_, lean_object* v_snd_1199_, lean_object* v___x_1200_, lean_object* v_as_1201_, lean_object* v_sz_1202_, lean_object* v_i_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_){
_start:
{
size_t v_sz_boxed_1206_; size_t v_i_boxed_1207_; lean_object* v_res_1208_; 
v_sz_boxed_1206_ = lean_unbox_usize(v_sz_1202_);
lean_dec(v_sz_1202_);
v_i_boxed_1207_ = lean_unbox_usize(v_i_1203_);
lean_dec(v_i_1203_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1197_, v_fst_1198_, v_snd_1199_, v___x_1200_, v_as_1201_, v_sz_boxed_1206_, v_i_boxed_1207_, v_b_1204_);
lean_dec_ref(v_as_1201_);
return v_res_1208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0_spec__0___redArg___closed__0);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1212_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
lean_ctor_set(v___x_1214_, 2, v___x_1213_);
lean_ctor_set(v___x_1214_, 3, v___x_1213_);
lean_ctor_set(v___x_1214_, 4, v___x_1212_);
lean_ctor_set(v___x_1214_, 5, v___x_1212_);
lean_ctor_set(v___x_1214_, 6, v___x_1212_);
lean_ctor_set(v___x_1214_, 7, v___x_1212_);
lean_ctor_set(v___x_1214_, 8, v___x_1212_);
lean_ctor_set(v___x_1214_, 9, v___x_1212_);
lean_ctor_set(v___x_1214_, 10, v___x_1212_);
lean_ctor_set(v___x_1214_, 11, v___x_1211_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_unsigned_to_nat(32u);
v___x_1216_ = lean_mk_empty_array_with_capacity(v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1218_ = ((size_t)5ULL);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_unsigned_to_nat(32u);
v___x_1221_ = lean_mk_empty_array_with_capacity(v___x_1220_);
v___x_1222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2);
v___x_1223_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v___x_1221_);
lean_ctor_set(v___x_1223_, 2, v___x_1219_);
lean_ctor_set(v___x_1223_, 3, v___x_1219_);
lean_ctor_set_usize(v___x_1223_, 4, v___x_1218_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = lean_box(1);
v___x_1225_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3);
v___x_1226_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1225_);
lean_ctor_set(v___x_1227_, 2, v___x_1224_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(lean_object* v_msgData_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v_env_1232_; uint8_t v___x_1233_; lean_object* v_env_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_scopes_1237_; lean_object* v___x_1238_; lean_object* v_opts_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1231_ = lean_st_ref_get(v___y_1229_);
v_env_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc_ref(v_env_1232_);
lean_dec(v___x_1231_);
v___x_1233_ = 0;
v_env_1234_ = l_Lean_Environment_setRecordingDeps(v_env_1232_, v___x_1233_);
v___x_1235_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1236_ = lean_st_ref_get(v___y_1229_);
v_scopes_1237_ = lean_ctor_get(v___x_1236_, 2);
lean_inc(v_scopes_1237_);
lean_dec(v___x_1236_);
v___x_1238_ = l_List_head_x21___redArg(v___x_1235_, v_scopes_1237_);
lean_dec(v_scopes_1237_);
v_opts_1239_ = lean_ctor_get(v___x_1238_, 1);
lean_inc_ref(v_opts_1239_);
lean_dec(v___x_1238_);
v___x_1240_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1);
v___x_1241_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4);
v___x_1242_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1242_, 0, v_env_1234_);
lean_ctor_set(v___x_1242_, 1, v___x_1240_);
lean_ctor_set(v___x_1242_, 2, v___x_1241_);
lean_ctor_set(v___x_1242_, 3, v_opts_1239_);
v___x_1243_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_msgData_1228_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_1245_, v___y_1246_);
lean_dec(v___y_1246_);
return v_res_1248_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1249_; double v___x_1250_; 
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_float_of_nat(v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v_cls_1253_, lean_object* v_msg_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Elab_Command_getRef___redArg(v___y_1255_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1309_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msg_1254_, v___y_1256_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1309_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1309_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v_traceState_1266_; lean_object* v_env_1267_; lean_object* v_messages_1268_; lean_object* v_scopes_1269_; lean_object* v_usedQuotCtxts_1270_; lean_object* v_nextMacroScope_1271_; lean_object* v_maxRecDepth_1272_; lean_object* v_ngen_1273_; lean_object* v_auxDeclNGen_1274_; lean_object* v_infoState_1275_; lean_object* v_snapshotTasks_1276_; lean_object* v_prevLinterStates_1277_; lean_object* v_codeQualityEntryTasks_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1308_; 
v___x_1265_ = lean_st_ref_take(v___y_1256_);
v_traceState_1266_ = lean_ctor_get(v___x_1265_, 9);
v_env_1267_ = lean_ctor_get(v___x_1265_, 0);
v_messages_1268_ = lean_ctor_get(v___x_1265_, 1);
v_scopes_1269_ = lean_ctor_get(v___x_1265_, 2);
v_usedQuotCtxts_1270_ = lean_ctor_get(v___x_1265_, 3);
v_nextMacroScope_1271_ = lean_ctor_get(v___x_1265_, 4);
v_maxRecDepth_1272_ = lean_ctor_get(v___x_1265_, 5);
v_ngen_1273_ = lean_ctor_get(v___x_1265_, 6);
v_auxDeclNGen_1274_ = lean_ctor_get(v___x_1265_, 7);
v_infoState_1275_ = lean_ctor_get(v___x_1265_, 8);
v_snapshotTasks_1276_ = lean_ctor_get(v___x_1265_, 10);
v_prevLinterStates_1277_ = lean_ctor_get(v___x_1265_, 11);
v_codeQualityEntryTasks_1278_ = lean_ctor_get(v___x_1265_, 12);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1280_ = v___x_1265_;
v_isShared_1281_ = v_isSharedCheck_1308_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1278_);
lean_inc(v_prevLinterStates_1277_);
lean_inc(v_snapshotTasks_1276_);
lean_inc(v_traceState_1266_);
lean_inc(v_infoState_1275_);
lean_inc(v_auxDeclNGen_1274_);
lean_inc(v_ngen_1273_);
lean_inc(v_maxRecDepth_1272_);
lean_inc(v_nextMacroScope_1271_);
lean_inc(v_usedQuotCtxts_1270_);
lean_inc(v_scopes_1269_);
lean_inc(v_messages_1268_);
lean_inc(v_env_1267_);
lean_dec(v___x_1265_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1308_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
uint64_t v_tid_1282_; lean_object* v_traces_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1307_; 
v_tid_1282_ = lean_ctor_get_uint64(v_traceState_1266_, sizeof(void*)*1);
v_traces_1283_ = lean_ctor_get(v_traceState_1266_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_traceState_1266_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1285_ = v_traceState_1266_;
v_isShared_1286_ = v_isSharedCheck_1307_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_traces_1283_);
lean_dec(v_traceState_1266_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1307_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; double v___x_1289_; uint8_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_1290_ = 0;
v___x_1291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1292_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1292_, 0, v_cls_1253_);
lean_ctor_set(v___x_1292_, 1, v___x_1288_);
lean_ctor_set(v___x_1292_, 2, v___x_1291_);
lean_ctor_set_float(v___x_1292_, sizeof(void*)*3, v___x_1289_);
lean_ctor_set_float(v___x_1292_, sizeof(void*)*3 + 8, v___x_1289_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*3 + 16, v___x_1290_);
v___x_1293_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_1294_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v_a_1261_);
lean_ctor_set(v___x_1294_, 2, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_a_1259_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = l_Lean_PersistentArray_push___redArg(v_traces_1283_, v___x_1295_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1296_);
v___x_1298_ = v___x_1285_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1296_);
lean_ctor_set_uint64(v_reuseFailAlloc_1306_, sizeof(void*)*1, v_tid_1282_);
v___x_1298_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 9, v___x_1298_);
v___x_1300_ = v___x_1280_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_env_1267_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_messages_1268_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_scopes_1269_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_usedQuotCtxts_1270_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_nextMacroScope_1271_);
lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_maxRecDepth_1272_);
lean_ctor_set(v_reuseFailAlloc_1305_, 6, v_ngen_1273_);
lean_ctor_set(v_reuseFailAlloc_1305_, 7, v_auxDeclNGen_1274_);
lean_ctor_set(v_reuseFailAlloc_1305_, 8, v_infoState_1275_);
lean_ctor_set(v_reuseFailAlloc_1305_, 9, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1305_, 10, v_snapshotTasks_1276_);
lean_ctor_set(v_reuseFailAlloc_1305_, 11, v_prevLinterStates_1277_);
lean_ctor_set(v_reuseFailAlloc_1305_, 12, v_codeQualityEntryTasks_1278_);
v___x_1300_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_st_ref_put(v___y_1256_, v___x_1300_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1287_);
v___x_1303_ = v___x_1263_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1287_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_msg_1254_);
lean_dec(v_cls_1253_);
v_a_1310_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1258_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1258_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v_cls_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_cls_1318_, v_msg_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1323_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2));
v___x_1330_ = l_Lean_Name_append(v___x_1329_, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6));
v___x_1336_ = l_Lean_stringToMessageData(v___x_1335_);
return v___x_1336_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8));
v___x_1339_ = l_Lean_stringToMessageData(v___x_1338_);
return v___x_1339_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10));
v___x_1342_ = l_Lean_stringToMessageData(v___x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(lean_object* v___x_1343_, lean_object* v_val_1344_, lean_object* v_cmd_1345_, uint8_t v_onUnsolved_1346_, uint8_t v___y_1347_, lean_object* v_as_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_dec(v_cmd_1345_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_b_1351_);
return v___x_1356_;
}
else
{
lean_object* v_snd_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1505_; 
v_snd_1357_ = lean_ctor_get(v_b_1351_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_b_1351_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_b_1351_, 0);
lean_dec(v_unused_1506_);
v___x_1359_ = v_b_1351_;
v_isShared_1360_ = v_isSharedCheck_1505_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snd_1357_);
lean_dec(v_b_1351_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1505_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1504_; 
v_fst_1361_ = lean_ctor_get(v_snd_1357_, 0);
v_snd_1362_ = lean_ctor_get(v_snd_1357_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_snd_1357_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1364_ = v_snd_1357_;
v_isShared_1365_ = v_isSharedCheck_1504_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_snd_1362_);
lean_inc(v_fst_1361_);
lean_dec(v_snd_1357_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1504_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_a_1366_; lean_object* v_pos_1367_; lean_object* v_endPos_1368_; uint8_t v_severity_1369_; lean_object* v_data_1370_; lean_object* v___x_1371_; lean_object* v_a_1373_; 
v_a_1366_ = lean_array_uget_borrowed(v_as_1348_, v_i_1350_);
v_pos_1367_ = lean_ctor_get(v_a_1366_, 1);
v_endPos_1368_ = lean_ctor_get(v_a_1366_, 2);
lean_inc(v_endPos_1368_);
v_severity_1369_ = lean_ctor_get_uint8(v_a_1366_, sizeof(void*)*5 + 1);
v_data_1370_ = lean_ctor_get(v_a_1366_, 4);
v___x_1371_ = lean_box(0);
if (v_severity_1369_ == 2)
{
lean_object* v___f_1386_; uint8_t v___x_1387_; 
v___f_1386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1370_);
v___x_1387_ = l_Lean_MessageData_hasTag(v___f_1386_, v_data_1370_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_dec(v_endPos_1368_);
lean_del_object(v___x_1359_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_fst_1361_);
lean_ctor_set(v___x_1388_, 1, v_snd_1362_);
v_a_1373_ = v___x_1388_;
goto v___jp_1372_;
}
else
{
if (lean_obj_tag(v_endPos_1368_) == 1)
{
lean_object* v_val_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1501_; 
v_val_1389_ = lean_ctor_get(v_endPos_1368_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_endPos_1368_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1391_ = v_endPos_1368_;
v_isShared_1392_ = v_isSharedCheck_1501_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_val_1389_);
lean_dec(v_endPos_1368_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1501_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; uint8_t v___x_1397_; 
lean_inc_ref(v_pos_1367_);
v___x_1393_ = l_Lean_FileMap_ofPosition(v___x_1343_, v_pos_1367_);
v___x_1394_ = l_Lean_FileMap_ofPosition(v___x_1343_, v_val_1389_);
lean_inc(v___x_1394_);
lean_inc(v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = 0;
v___x_1397_ = l_Lean_Syntax_Range_includes(v_val_1344_, v___x_1395_, v___x_1396_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_dec_ref_known(v___x_1395_, 2);
lean_dec(v___x_1394_);
lean_dec(v___x_1393_);
lean_del_object(v___x_1391_);
lean_del_object(v___x_1359_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_fst_1361_);
lean_ctor_set(v___x_1398_, 1, v_snd_1362_);
v_a_1373_ = v___x_1398_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1399_; 
lean_inc(v_cmd_1345_);
lean_inc_ref(v___x_1395_);
v___x_1399_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1395_, v_cmd_1345_);
if (lean_obj_tag(v___x_1399_) == 1)
{
lean_object* v_val_1400_; lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v___x_1394_);
lean_dec(v___x_1393_);
lean_del_object(v___x_1391_);
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v_fst_1401_ = lean_ctor_get(v_val_1400_, 0);
v_snd_1402_ = lean_ctor_get(v_val_1400_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_val_1400_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1404_ = v_val_1400_;
v_isShared_1405_ = v_isSharedCheck_1465_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snd_1402_);
lean_inc(v_fst_1401_);
lean_dec(v_val_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1465_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; uint8_t v___y_1463_; lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Syntax_getPos_x3f(v_fst_1401_, v___x_1396_);
if (lean_obj_tag(v___x_1464_) == 0)
{
v___y_1463_ = v___x_1397_;
goto v___jp_1462_;
}
else
{
lean_dec_ref_known(v___x_1464_, 1);
v___y_1463_ = v___x_1396_;
goto v___jp_1462_;
}
v___jp_1406_:
{
lean_object* v___x_1412_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v_snd_1362_);
lean_ctor_set(v___x_1404_, 0, v_fst_1361_);
v___x_1412_ = v___x_1404_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_fst_1361_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_snd_1362_);
v___x_1412_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
size_t v_sz_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v_sz_1413_ = lean_array_size(v___y_1408_);
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1395_, v_fst_1401_, v_snd_1402_, v___y_1407_, v___y_1408_, v_sz_1413_, v___x_1414_, v___x_1412_);
lean_dec_ref(v___y_1408_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v_fst_1417_ = lean_ctor_get(v_a_1416_, 0);
v_snd_1418_ = lean_ctor_get(v_a_1416_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v_a_1416_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_snd_1418_);
lean_inc(v_fst_1417_);
lean_dec(v_a_1416_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_fst_1417_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_snd_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
v_a_1373_ = v___x_1423_;
goto v___jp_1372_;
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_del_object(v___x_1364_);
lean_dec(v_cmd_1345_);
v_a_1426_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1415_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1415_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
v___jp_1435_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
lean_inc_ref(v___x_1395_);
v___x_1436_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1395_);
v___x_1437_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1370_);
v___x_1438_ = lean_array_get_size(v___x_1437_);
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_nat_dec_eq(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
v___y_1407_ = v___x_1436_;
v___y_1408_ = v___x_1437_;
v___y_1409_ = v___y_1352_;
v___y_1410_ = v___y_1353_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v_scopes_1446_; lean_object* v___x_1447_; lean_object* v_opts_1448_; uint8_t v_hasTrace_1449_; 
v___x_1441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1442_ = l_Lean_inheritedTraceOptions;
v___x_1443_ = lean_st_ref_get(v___x_1442_);
v___x_1444_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1445_ = lean_st_ref_get(v___y_1353_);
v_scopes_1446_ = lean_ctor_get(v___x_1445_, 2);
lean_inc(v_scopes_1446_);
lean_dec(v___x_1445_);
v___x_1447_ = l_List_head_x21___redArg(v___x_1444_, v_scopes_1446_);
lean_dec(v_scopes_1446_);
v_opts_1448_ = lean_ctor_get(v___x_1447_, 1);
lean_inc_ref(v_opts_1448_);
lean_dec(v___x_1447_);
v_hasTrace_1449_ = lean_ctor_get_uint8(v_opts_1448_, sizeof(void*)*1);
if (v_hasTrace_1449_ == 0)
{
lean_dec_ref(v_opts_1448_);
lean_dec(v___x_1443_);
v___y_1407_ = v___x_1436_;
v___y_1408_ = v___x_1437_;
v___y_1409_ = v___y_1352_;
v___y_1410_ = v___y_1353_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1450_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1451_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1443_, v_opts_1448_, v___x_1450_);
lean_dec_ref(v_opts_1448_);
lean_dec(v___x_1443_);
if (v___x_1451_ == 0)
{
v___y_1407_ = v___x_1436_;
v___y_1408_ = v___x_1437_;
v___y_1409_ = v___y_1352_;
v___y_1410_ = v___y_1353_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1453_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1441_, v___x_1452_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_dec_ref_known(v___x_1453_, 1);
v___y_1407_ = v___x_1436_;
v___y_1408_ = v___x_1437_;
v___y_1409_ = v___y_1352_;
v___y_1410_ = v___y_1353_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v___x_1437_);
lean_dec(v___x_1436_);
lean_del_object(v___x_1404_);
lean_dec(v_snd_1402_);
lean_dec(v_fst_1401_);
lean_dec_ref_known(v___x_1395_, 2);
lean_del_object(v___x_1364_);
lean_dec(v_snd_1362_);
lean_dec(v_fst_1361_);
lean_dec(v_cmd_1345_);
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
v___jp_1462_:
{
if (v_onUnsolved_1346_ == 0)
{
if (v___y_1347_ == 0)
{
lean_del_object(v___x_1404_);
lean_dec(v_snd_1402_);
lean_dec(v_fst_1401_);
lean_dec_ref_known(v___x_1395_, 2);
goto v___jp_1380_;
}
else
{
if (v___y_1463_ == 0)
{
lean_del_object(v___x_1404_);
lean_dec(v_snd_1402_);
lean_dec(v_fst_1401_);
lean_dec_ref_known(v___x_1395_, 2);
goto v___jp_1380_;
}
else
{
lean_del_object(v___x_1359_);
goto v___jp_1435_;
}
}
}
else
{
lean_del_object(v___x_1359_);
goto v___jp_1435_;
}
}
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_scopes_1471_; lean_object* v___x_1472_; lean_object* v_opts_1473_; uint8_t v_hasTrace_1474_; 
lean_dec(v___x_1399_);
lean_dec_ref_known(v___x_1395_, 2);
lean_del_object(v___x_1359_);
v___x_1466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1467_ = l_Lean_inheritedTraceOptions;
v___x_1468_ = lean_st_ref_get(v___x_1467_);
v___x_1469_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1470_ = lean_st_ref_get(v___y_1353_);
v_scopes_1471_ = lean_ctor_get(v___x_1470_, 2);
lean_inc(v_scopes_1471_);
lean_dec(v___x_1470_);
v___x_1472_ = l_List_head_x21___redArg(v___x_1469_, v_scopes_1471_);
lean_dec(v_scopes_1471_);
v_opts_1473_ = lean_ctor_get(v___x_1472_, 1);
lean_inc_ref(v_opts_1473_);
lean_dec(v___x_1472_);
v_hasTrace_1474_ = lean_ctor_get_uint8(v_opts_1473_, sizeof(void*)*1);
if (v_hasTrace_1474_ == 0)
{
lean_dec_ref(v_opts_1473_);
lean_dec(v___x_1468_);
lean_dec(v___x_1394_);
lean_dec(v___x_1393_);
lean_del_object(v___x_1391_);
goto v___jp_1384_;
}
else
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1476_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1468_, v_opts_1473_, v___x_1475_);
lean_dec_ref(v_opts_1473_);
lean_dec(v___x_1468_);
if (v___x_1476_ == 0)
{
lean_dec(v___x_1394_);
lean_dec(v___x_1393_);
lean_del_object(v___x_1391_);
goto v___jp_1384_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1477_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1478_ = l_Nat_reprFast(v___x_1393_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 3);
lean_ctor_set(v___x_1391_, 0, v___x_1478_);
v___x_1480_ = v___x_1391_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1481_ = l_Lean_MessageData_ofFormat(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1477_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Nat_reprFast(v___x_1394_);
v___x_1486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
v___x_1487_ = l_Lean_MessageData_ofFormat(v___x_1486_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1484_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1466_, v___x_1490_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref_known(v___x_1491_, 1);
goto v___jp_1384_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_del_object(v___x_1364_);
lean_dec(v_snd_1362_);
lean_dec(v_fst_1361_);
lean_dec(v_cmd_1345_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
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
lean_object* v___x_1502_; 
lean_dec(v_endPos_1368_);
lean_del_object(v___x_1359_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_fst_1361_);
lean_ctor_set(v___x_1502_, 1, v_snd_1362_);
v_a_1373_ = v___x_1502_;
goto v___jp_1372_;
}
}
}
else
{
lean_object* v___x_1503_; 
lean_dec(v_endPos_1368_);
lean_del_object(v___x_1359_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_fst_1361_);
lean_ctor_set(v___x_1503_, 1, v_snd_1362_);
v_a_1373_ = v___x_1503_;
goto v___jp_1372_;
}
v___jp_1372_:
{
lean_object* v___x_1375_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_a_1373_);
lean_ctor_set(v___x_1364_, 0, v___x_1371_);
v___x_1375_ = v___x_1364_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_a_1373_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
size_t v___x_1376_; size_t v___x_1377_; 
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = lean_usize_add(v_i_1350_, v___x_1376_);
v_i_1350_ = v___x_1377_;
v_b_1351_ = v___x_1375_;
goto _start;
}
}
v___jp_1380_:
{
lean_object* v___x_1382_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v_snd_1362_);
lean_ctor_set(v___x_1359_, 0, v_fst_1361_);
v___x_1382_ = v___x_1359_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_fst_1361_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_snd_1362_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
v_a_1373_ = v___x_1382_;
goto v___jp_1372_;
}
}
v___jp_1384_:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_fst_1361_);
lean_ctor_set(v___x_1385_, 1, v_snd_1362_);
v_a_1373_ = v___x_1385_;
goto v___jp_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___boxed(lean_object* v___x_1507_, lean_object* v_val_1508_, lean_object* v_cmd_1509_, lean_object* v_onUnsolved_1510_, lean_object* v___y_1511_, lean_object* v_as_1512_, lean_object* v_sz_1513_, lean_object* v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v_onUnsolved_boxed_1519_; uint8_t v___y_12284__boxed_1520_; size_t v_sz_boxed_1521_; size_t v_i_boxed_1522_; lean_object* v_res_1523_; 
v_onUnsolved_boxed_1519_ = lean_unbox(v_onUnsolved_1510_);
v___y_12284__boxed_1520_ = lean_unbox(v___y_1511_);
v_sz_boxed_1521_ = lean_unbox_usize(v_sz_1513_);
lean_dec(v_sz_1513_);
v_i_boxed_1522_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1507_, v_val_1508_, v_cmd_1509_, v_onUnsolved_boxed_1519_, v___y_12284__boxed_1520_, v_as_1512_, v_sz_boxed_1521_, v_i_boxed_1522_, v_b_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_as_1512_);
lean_dec_ref(v_val_1508_);
lean_dec_ref(v___x_1507_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object* v___x_1524_, lean_object* v_val_1525_, lean_object* v_cmd_1526_, uint8_t v_onUnsolved_1527_, uint8_t v___y_1528_, lean_object* v_as_1529_, size_t v_sz_1530_, size_t v_i_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_usize_dec_lt(v_i_1531_, v_sz_1530_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_dec(v_cmd_1526_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_b_1532_);
return v___x_1537_;
}
else
{
lean_object* v_snd_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1686_; 
v_snd_1538_ = lean_ctor_get(v_b_1532_, 1);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_b_1532_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v_b_1532_, 0);
lean_dec(v_unused_1687_);
v___x_1540_ = v_b_1532_;
v_isShared_1541_ = v_isSharedCheck_1686_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_snd_1538_);
lean_dec(v_b_1532_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1686_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_fst_1542_; lean_object* v_snd_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1685_; 
v_fst_1542_ = lean_ctor_get(v_snd_1538_, 0);
v_snd_1543_ = lean_ctor_get(v_snd_1538_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_snd_1538_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1545_ = v_snd_1538_;
v_isShared_1546_ = v_isSharedCheck_1685_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_snd_1543_);
lean_inc(v_fst_1542_);
lean_dec(v_snd_1538_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1685_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_a_1547_; lean_object* v_pos_1548_; lean_object* v_endPos_1549_; uint8_t v_severity_1550_; lean_object* v_data_1551_; lean_object* v___x_1552_; lean_object* v_a_1554_; 
v_a_1547_ = lean_array_uget_borrowed(v_as_1529_, v_i_1531_);
v_pos_1548_ = lean_ctor_get(v_a_1547_, 1);
v_endPos_1549_ = lean_ctor_get(v_a_1547_, 2);
lean_inc(v_endPos_1549_);
v_severity_1550_ = lean_ctor_get_uint8(v_a_1547_, sizeof(void*)*5 + 1);
v_data_1551_ = lean_ctor_get(v_a_1547_, 4);
v___x_1552_ = lean_box(0);
if (v_severity_1550_ == 2)
{
lean_object* v___f_1567_; uint8_t v___x_1568_; 
v___f_1567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1551_);
v___x_1568_ = l_Lean_MessageData_hasTag(v___f_1567_, v_data_1551_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec(v_endPos_1549_);
lean_del_object(v___x_1540_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_fst_1542_);
lean_ctor_set(v___x_1569_, 1, v_snd_1543_);
v_a_1554_ = v___x_1569_;
goto v___jp_1553_;
}
else
{
if (lean_obj_tag(v_endPos_1549_) == 1)
{
lean_object* v_val_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1682_; 
v_val_1570_ = lean_ctor_get(v_endPos_1549_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_endPos_1549_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1572_ = v_endPos_1549_;
v_isShared_1573_ = v_isSharedCheck_1682_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_val_1570_);
lean_dec(v_endPos_1549_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1682_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; uint8_t v___x_1578_; 
lean_inc_ref(v_pos_1548_);
v___x_1574_ = l_Lean_FileMap_ofPosition(v___x_1524_, v_pos_1548_);
v___x_1575_ = l_Lean_FileMap_ofPosition(v___x_1524_, v_val_1570_);
lean_inc(v___x_1575_);
lean_inc(v___x_1574_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = 0;
v___x_1578_ = l_Lean_Syntax_Range_includes(v_val_1525_, v___x_1576_, v___x_1577_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref_known(v___x_1576_, 2);
lean_dec(v___x_1575_);
lean_dec(v___x_1574_);
lean_del_object(v___x_1572_);
lean_del_object(v___x_1540_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_fst_1542_);
lean_ctor_set(v___x_1579_, 1, v_snd_1543_);
v_a_1554_ = v___x_1579_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1580_; 
lean_inc(v_cmd_1526_);
lean_inc_ref(v___x_1576_);
v___x_1580_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1576_, v_cmd_1526_);
if (lean_obj_tag(v___x_1580_) == 1)
{
lean_object* v_val_1581_; lean_object* v_fst_1582_; lean_object* v_snd_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v___x_1575_);
lean_dec(v___x_1574_);
lean_del_object(v___x_1572_);
v_val_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v_fst_1582_ = lean_ctor_get(v_val_1581_, 0);
v_snd_1583_ = lean_ctor_get(v_val_1581_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_val_1581_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1585_ = v_val_1581_;
v_isShared_1586_ = v_isSharedCheck_1646_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snd_1583_);
lean_inc(v_fst_1582_);
lean_dec(v_val_1581_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1646_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; uint8_t v___y_1644_; lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Syntax_getPos_x3f(v_fst_1582_, v___x_1577_);
if (lean_obj_tag(v___x_1645_) == 0)
{
v___y_1644_ = v___x_1578_;
goto v___jp_1643_;
}
else
{
lean_dec_ref_known(v___x_1645_, 1);
v___y_1644_ = v___x_1577_;
goto v___jp_1643_;
}
v___jp_1587_:
{
lean_object* v___x_1593_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v_snd_1543_);
lean_ctor_set(v___x_1585_, 0, v_fst_1542_);
v___x_1593_ = v___x_1585_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_fst_1542_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_snd_1543_);
v___x_1593_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
size_t v_sz_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v_sz_1594_ = lean_array_size(v___y_1588_);
v___x_1595_ = ((size_t)0ULL);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1576_, v_fst_1582_, v_snd_1583_, v___y_1589_, v___y_1588_, v_sz_1594_, v___x_1595_, v___x_1593_);
lean_dec_ref(v___y_1588_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v_fst_1598_ = lean_ctor_get(v_a_1597_, 0);
v_snd_1599_ = lean_ctor_get(v_a_1597_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_a_1597_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v_a_1597_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_snd_1599_);
lean_inc(v_fst_1598_);
lean_dec(v_a_1597_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_fst_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_snd_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
v_a_1554_ = v___x_1604_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1545_);
lean_dec(v_cmd_1526_);
v_a_1607_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1596_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1596_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
v___jp_1616_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
lean_inc_ref(v___x_1576_);
v___x_1617_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1576_);
v___x_1618_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1551_);
v___x_1619_ = lean_array_get_size(v___x_1618_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_nat_dec_eq(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
v___y_1588_ = v___x_1618_;
v___y_1589_ = v___x_1617_;
v___y_1590_ = v___y_1533_;
v___y_1591_ = v___y_1534_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_scopes_1627_; lean_object* v___x_1628_; lean_object* v_opts_1629_; uint8_t v_hasTrace_1630_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1623_ = l_Lean_inheritedTraceOptions;
v___x_1624_ = lean_st_ref_get(v___x_1623_);
v___x_1625_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1626_ = lean_st_ref_get(v___y_1534_);
v_scopes_1627_ = lean_ctor_get(v___x_1626_, 2);
lean_inc(v_scopes_1627_);
lean_dec(v___x_1626_);
v___x_1628_ = l_List_head_x21___redArg(v___x_1625_, v_scopes_1627_);
lean_dec(v_scopes_1627_);
v_opts_1629_ = lean_ctor_get(v___x_1628_, 1);
lean_inc_ref(v_opts_1629_);
lean_dec(v___x_1628_);
v_hasTrace_1630_ = lean_ctor_get_uint8(v_opts_1629_, sizeof(void*)*1);
if (v_hasTrace_1630_ == 0)
{
lean_dec_ref(v_opts_1629_);
lean_dec(v___x_1624_);
v___y_1588_ = v___x_1618_;
v___y_1589_ = v___x_1617_;
v___y_1590_ = v___y_1533_;
v___y_1591_ = v___y_1534_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1632_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1624_, v_opts_1629_, v___x_1631_);
lean_dec_ref(v_opts_1629_);
lean_dec(v___x_1624_);
if (v___x_1632_ == 0)
{
v___y_1588_ = v___x_1618_;
v___y_1589_ = v___x_1617_;
v___y_1590_ = v___y_1533_;
v___y_1591_ = v___y_1534_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1634_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1622_, v___x_1633_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref_known(v___x_1634_, 1);
v___y_1588_ = v___x_1618_;
v___y_1589_ = v___x_1617_;
v___y_1590_ = v___y_1533_;
v___y_1591_ = v___y_1534_;
goto v___jp_1587_;
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v___x_1618_);
lean_dec(v___x_1617_);
lean_del_object(v___x_1585_);
lean_dec(v_snd_1583_);
lean_dec(v_fst_1582_);
lean_dec_ref_known(v___x_1576_, 2);
lean_del_object(v___x_1545_);
lean_dec(v_snd_1543_);
lean_dec(v_fst_1542_);
lean_dec(v_cmd_1526_);
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
v___jp_1643_:
{
if (v_onUnsolved_1527_ == 0)
{
if (v___y_1528_ == 0)
{
lean_del_object(v___x_1585_);
lean_dec(v_snd_1583_);
lean_dec(v_fst_1582_);
lean_dec_ref_known(v___x_1576_, 2);
goto v___jp_1561_;
}
else
{
if (v___y_1644_ == 0)
{
lean_del_object(v___x_1585_);
lean_dec(v_snd_1583_);
lean_dec(v_fst_1582_);
lean_dec_ref_known(v___x_1576_, 2);
goto v___jp_1561_;
}
else
{
lean_del_object(v___x_1540_);
goto v___jp_1616_;
}
}
}
else
{
lean_del_object(v___x_1540_);
goto v___jp_1616_;
}
}
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v_scopes_1652_; lean_object* v___x_1653_; lean_object* v_opts_1654_; uint8_t v_hasTrace_1655_; 
lean_dec(v___x_1580_);
lean_dec_ref_known(v___x_1576_, 2);
lean_del_object(v___x_1540_);
v___x_1647_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1648_ = l_Lean_inheritedTraceOptions;
v___x_1649_ = lean_st_ref_get(v___x_1648_);
v___x_1650_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1651_ = lean_st_ref_get(v___y_1534_);
v_scopes_1652_ = lean_ctor_get(v___x_1651_, 2);
lean_inc(v_scopes_1652_);
lean_dec(v___x_1651_);
v___x_1653_ = l_List_head_x21___redArg(v___x_1650_, v_scopes_1652_);
lean_dec(v_scopes_1652_);
v_opts_1654_ = lean_ctor_get(v___x_1653_, 1);
lean_inc_ref(v_opts_1654_);
lean_dec(v___x_1653_);
v_hasTrace_1655_ = lean_ctor_get_uint8(v_opts_1654_, sizeof(void*)*1);
if (v_hasTrace_1655_ == 0)
{
lean_dec_ref(v_opts_1654_);
lean_dec(v___x_1649_);
lean_dec(v___x_1575_);
lean_dec(v___x_1574_);
lean_del_object(v___x_1572_);
goto v___jp_1565_;
}
else
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1657_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1649_, v_opts_1654_, v___x_1656_);
lean_dec_ref(v_opts_1654_);
lean_dec(v___x_1649_);
if (v___x_1657_ == 0)
{
lean_dec(v___x_1575_);
lean_dec(v___x_1574_);
lean_del_object(v___x_1572_);
goto v___jp_1565_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1659_ = l_Nat_reprFast(v___x_1574_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 3);
lean_ctor_set(v___x_1572_, 0, v___x_1659_);
v___x_1661_ = v___x_1572_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1662_ = l_Lean_MessageData_ofFormat(v___x_1661_);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1658_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Nat_reprFast(v___x_1575_);
v___x_1667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
v___x_1668_ = l_Lean_MessageData_ofFormat(v___x_1667_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1665_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1647_, v___x_1671_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_dec_ref_known(v___x_1672_, 1);
goto v___jp_1565_;
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_del_object(v___x_1545_);
lean_dec(v_snd_1543_);
lean_dec(v_fst_1542_);
lean_dec(v_cmd_1526_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
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
lean_object* v___x_1683_; 
lean_dec(v_endPos_1549_);
lean_del_object(v___x_1540_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_fst_1542_);
lean_ctor_set(v___x_1683_, 1, v_snd_1543_);
v_a_1554_ = v___x_1683_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1684_; 
lean_dec(v_endPos_1549_);
lean_del_object(v___x_1540_);
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v_fst_1542_);
lean_ctor_set(v___x_1684_, 1, v_snd_1543_);
v_a_1554_ = v___x_1684_;
goto v___jp_1553_;
}
v___jp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v_a_1554_);
lean_ctor_set(v___x_1545_, 0, v___x_1552_);
v___x_1556_ = v___x_1545_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_a_1554_);
v___x_1556_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
size_t v___x_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = ((size_t)1ULL);
v___x_1558_ = lean_usize_add(v_i_1531_, v___x_1557_);
v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1524_, v_val_1525_, v_cmd_1526_, v_onUnsolved_1527_, v___y_1528_, v_as_1529_, v_sz_1530_, v___x_1558_, v___x_1556_, v___y_1533_, v___y_1534_);
return v___x_1559_;
}
}
v___jp_1561_:
{
lean_object* v___x_1563_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v_snd_1543_);
lean_ctor_set(v___x_1540_, 0, v_fst_1542_);
v___x_1563_ = v___x_1540_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_fst_1542_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_snd_1543_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
v_a_1554_ = v___x_1563_;
goto v___jp_1553_;
}
}
v___jp_1565_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v_fst_1542_);
lean_ctor_set(v___x_1566_, 1, v_snd_1543_);
v_a_1554_ = v___x_1566_;
goto v___jp_1553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object* v___x_1688_, lean_object* v_val_1689_, lean_object* v_cmd_1690_, lean_object* v_onUnsolved_1691_, lean_object* v___y_1692_, lean_object* v_as_1693_, lean_object* v_sz_1694_, lean_object* v_i_1695_, lean_object* v_b_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v_onUnsolved_boxed_1700_; uint8_t v___y_12625__boxed_1701_; size_t v_sz_boxed_1702_; size_t v_i_boxed_1703_; lean_object* v_res_1704_; 
v_onUnsolved_boxed_1700_ = lean_unbox(v_onUnsolved_1691_);
v___y_12625__boxed_1701_ = lean_unbox(v___y_1692_);
v_sz_boxed_1702_ = lean_unbox_usize(v_sz_1694_);
lean_dec(v_sz_1694_);
v_i_boxed_1703_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_1688_, v_val_1689_, v_cmd_1690_, v_onUnsolved_boxed_1700_, v___y_12625__boxed_1701_, v_as_1693_, v_sz_boxed_1702_, v_i_boxed_1703_, v_b_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec_ref(v_as_1693_);
lean_dec_ref(v_val_1689_);
lean_dec_ref(v___x_1688_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(lean_object* v___x_1705_, lean_object* v_val_1706_, lean_object* v_cmd_1707_, uint8_t v_onUnsolved_1708_, uint8_t v___y_1709_, lean_object* v_as_1710_, size_t v_sz_1711_, size_t v_i_1712_, lean_object* v_b_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_usize_dec_lt(v_i_1712_, v_sz_1711_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_cmd_1707_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_b_1713_);
return v___x_1718_;
}
else
{
lean_object* v_snd_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1867_; 
v_snd_1719_ = lean_ctor_get(v_b_1713_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_b_1713_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; 
v_unused_1868_ = lean_ctor_get(v_b_1713_, 0);
lean_dec(v_unused_1868_);
v___x_1721_ = v_b_1713_;
v_isShared_1722_ = v_isSharedCheck_1867_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_snd_1719_);
lean_dec(v_b_1713_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1867_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_fst_1723_; lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1866_; 
v_fst_1723_ = lean_ctor_get(v_snd_1719_, 0);
v_snd_1724_ = lean_ctor_get(v_snd_1719_, 1);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_snd_1719_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1726_ = v_snd_1719_;
v_isShared_1727_ = v_isSharedCheck_1866_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_inc(v_fst_1723_);
lean_dec(v_snd_1719_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1866_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_a_1728_; lean_object* v_pos_1729_; lean_object* v_endPos_1730_; uint8_t v_severity_1731_; lean_object* v_data_1732_; lean_object* v___x_1733_; lean_object* v_a_1735_; 
v_a_1728_ = lean_array_uget_borrowed(v_as_1710_, v_i_1712_);
v_pos_1729_ = lean_ctor_get(v_a_1728_, 1);
v_endPos_1730_ = lean_ctor_get(v_a_1728_, 2);
lean_inc(v_endPos_1730_);
v_severity_1731_ = lean_ctor_get_uint8(v_a_1728_, sizeof(void*)*5 + 1);
v_data_1732_ = lean_ctor_get(v_a_1728_, 4);
v___x_1733_ = lean_box(0);
if (v_severity_1731_ == 2)
{
lean_object* v___f_1748_; uint8_t v___x_1749_; 
v___f_1748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1732_);
v___x_1749_ = l_Lean_MessageData_hasTag(v___f_1748_, v_data_1732_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
lean_dec(v_endPos_1730_);
lean_del_object(v___x_1721_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_fst_1723_);
lean_ctor_set(v___x_1750_, 1, v_snd_1724_);
v_a_1735_ = v___x_1750_;
goto v___jp_1734_;
}
else
{
if (lean_obj_tag(v_endPos_1730_) == 1)
{
lean_object* v_val_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1863_; 
v_val_1751_ = lean_ctor_get(v_endPos_1730_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_endPos_1730_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1753_ = v_endPos_1730_;
v_isShared_1754_ = v_isSharedCheck_1863_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_val_1751_);
lean_dec(v_endPos_1730_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1863_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; 
lean_inc_ref(v_pos_1729_);
v___x_1755_ = l_Lean_FileMap_ofPosition(v___x_1705_, v_pos_1729_);
v___x_1756_ = l_Lean_FileMap_ofPosition(v___x_1705_, v_val_1751_);
lean_inc(v___x_1756_);
lean_inc(v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = 0;
v___x_1759_ = l_Lean_Syntax_Range_includes(v_val_1706_, v___x_1757_, v___x_1758_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_dec_ref_known(v___x_1757_, 2);
lean_dec(v___x_1756_);
lean_dec(v___x_1755_);
lean_del_object(v___x_1753_);
lean_del_object(v___x_1721_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_fst_1723_);
lean_ctor_set(v___x_1760_, 1, v_snd_1724_);
v_a_1735_ = v___x_1760_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1761_; 
lean_inc(v_cmd_1707_);
lean_inc_ref(v___x_1757_);
v___x_1761_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1757_, v_cmd_1707_);
if (lean_obj_tag(v___x_1761_) == 1)
{
lean_object* v_val_1762_; lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v___x_1756_);
lean_dec(v___x_1755_);
lean_del_object(v___x_1753_);
v_val_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v_fst_1763_ = lean_ctor_get(v_val_1762_, 0);
v_snd_1764_ = lean_ctor_get(v_val_1762_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_val_1762_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1766_ = v_val_1762_;
v_isShared_1767_ = v_isSharedCheck_1827_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snd_1764_);
lean_inc(v_fst_1763_);
lean_dec(v_val_1762_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1827_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; uint8_t v___y_1825_; lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Syntax_getPos_x3f(v_fst_1763_, v___x_1758_);
if (lean_obj_tag(v___x_1826_) == 0)
{
v___y_1825_ = v___x_1759_;
goto v___jp_1824_;
}
else
{
lean_dec_ref_known(v___x_1826_, 1);
v___y_1825_ = v___x_1758_;
goto v___jp_1824_;
}
v___jp_1768_:
{
lean_object* v___x_1774_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v_snd_1724_);
lean_ctor_set(v___x_1766_, 0, v_fst_1723_);
v___x_1774_ = v___x_1766_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_snd_1724_);
v___x_1774_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
size_t v_sz_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v_sz_1775_ = lean_array_size(v___y_1770_);
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1757_, v_fst_1763_, v_snd_1764_, v___y_1769_, v___y_1770_, v_sz_1775_, v___x_1776_, v___x_1774_);
lean_dec_ref(v___y_1770_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v_fst_1779_; lean_object* v_snd_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v_fst_1779_ = lean_ctor_get(v_a_1778_, 0);
v_snd_1780_ = lean_ctor_get(v_a_1778_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_a_1778_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v_a_1778_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snd_1780_);
lean_inc(v_fst_1779_);
lean_dec(v_a_1778_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_snd_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v_a_1735_ = v___x_1785_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_del_object(v___x_1726_);
lean_dec(v_cmd_1707_);
v_a_1788_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1777_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1777_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
v___jp_1797_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
lean_inc_ref(v___x_1757_);
v___x_1798_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1757_);
v___x_1799_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1732_);
v___x_1800_ = lean_array_get_size(v___x_1799_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_nat_dec_eq(v___x_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
v___y_1769_ = v___x_1798_;
v___y_1770_ = v___x_1799_;
v___y_1771_ = v___y_1714_;
v___y_1772_ = v___y_1715_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v_scopes_1808_; lean_object* v___x_1809_; lean_object* v_opts_1810_; uint8_t v_hasTrace_1811_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1804_ = l_Lean_inheritedTraceOptions;
v___x_1805_ = lean_st_ref_get(v___x_1804_);
v___x_1806_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1807_ = lean_st_ref_get(v___y_1715_);
v_scopes_1808_ = lean_ctor_get(v___x_1807_, 2);
lean_inc(v_scopes_1808_);
lean_dec(v___x_1807_);
v___x_1809_ = l_List_head_x21___redArg(v___x_1806_, v_scopes_1808_);
lean_dec(v_scopes_1808_);
v_opts_1810_ = lean_ctor_get(v___x_1809_, 1);
lean_inc_ref(v_opts_1810_);
lean_dec(v___x_1809_);
v_hasTrace_1811_ = lean_ctor_get_uint8(v_opts_1810_, sizeof(void*)*1);
if (v_hasTrace_1811_ == 0)
{
lean_dec_ref(v_opts_1810_);
lean_dec(v___x_1805_);
v___y_1769_ = v___x_1798_;
v___y_1770_ = v___x_1799_;
v___y_1771_ = v___y_1714_;
v___y_1772_ = v___y_1715_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1813_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1805_, v_opts_1810_, v___x_1812_);
lean_dec_ref(v_opts_1810_);
lean_dec(v___x_1805_);
if (v___x_1813_ == 0)
{
v___y_1769_ = v___x_1798_;
v___y_1770_ = v___x_1799_;
v___y_1771_ = v___y_1714_;
v___y_1772_ = v___y_1715_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1815_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1803_, v___x_1814_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_dec_ref_known(v___x_1815_, 1);
v___y_1769_ = v___x_1798_;
v___y_1770_ = v___x_1799_;
v___y_1771_ = v___y_1714_;
v___y_1772_ = v___y_1715_;
goto v___jp_1768_;
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec_ref(v___x_1799_);
lean_dec(v___x_1798_);
lean_del_object(v___x_1766_);
lean_dec(v_snd_1764_);
lean_dec(v_fst_1763_);
lean_dec_ref_known(v___x_1757_, 2);
lean_del_object(v___x_1726_);
lean_dec(v_snd_1724_);
lean_dec(v_fst_1723_);
lean_dec(v_cmd_1707_);
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
v___jp_1824_:
{
if (v_onUnsolved_1708_ == 0)
{
if (v___y_1709_ == 0)
{
lean_del_object(v___x_1766_);
lean_dec(v_snd_1764_);
lean_dec(v_fst_1763_);
lean_dec_ref_known(v___x_1757_, 2);
goto v___jp_1742_;
}
else
{
if (v___y_1825_ == 0)
{
lean_del_object(v___x_1766_);
lean_dec(v_snd_1764_);
lean_dec(v_fst_1763_);
lean_dec_ref_known(v___x_1757_, 2);
goto v___jp_1742_;
}
else
{
lean_del_object(v___x_1721_);
goto v___jp_1797_;
}
}
}
else
{
lean_del_object(v___x_1721_);
goto v___jp_1797_;
}
}
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_scopes_1833_; lean_object* v___x_1834_; lean_object* v_opts_1835_; uint8_t v_hasTrace_1836_; 
lean_dec(v___x_1761_);
lean_dec_ref_known(v___x_1757_, 2);
lean_del_object(v___x_1721_);
v___x_1828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1829_ = l_Lean_inheritedTraceOptions;
v___x_1830_ = lean_st_ref_get(v___x_1829_);
v___x_1831_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1832_ = lean_st_ref_get(v___y_1715_);
v_scopes_1833_ = lean_ctor_get(v___x_1832_, 2);
lean_inc(v_scopes_1833_);
lean_dec(v___x_1832_);
v___x_1834_ = l_List_head_x21___redArg(v___x_1831_, v_scopes_1833_);
lean_dec(v_scopes_1833_);
v_opts_1835_ = lean_ctor_get(v___x_1834_, 1);
lean_inc_ref(v_opts_1835_);
lean_dec(v___x_1834_);
v_hasTrace_1836_ = lean_ctor_get_uint8(v_opts_1835_, sizeof(void*)*1);
if (v_hasTrace_1836_ == 0)
{
lean_dec_ref(v_opts_1835_);
lean_dec(v___x_1830_);
lean_dec(v___x_1756_);
lean_dec(v___x_1755_);
lean_del_object(v___x_1753_);
goto v___jp_1746_;
}
else
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1838_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1830_, v_opts_1835_, v___x_1837_);
lean_dec_ref(v_opts_1835_);
lean_dec(v___x_1830_);
if (v___x_1838_ == 0)
{
lean_dec(v___x_1756_);
lean_dec(v___x_1755_);
lean_del_object(v___x_1753_);
goto v___jp_1746_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1840_ = l_Nat_reprFast(v___x_1755_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 3);
lean_ctor_set(v___x_1753_, 0, v___x_1840_);
v___x_1842_ = v___x_1753_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1843_ = l_Lean_MessageData_ofFormat(v___x_1842_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1839_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Nat_reprFast(v___x_1756_);
v___x_1848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
v___x_1849_ = l_Lean_MessageData_ofFormat(v___x_1848_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1846_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1828_, v___x_1852_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_dec_ref_known(v___x_1853_, 1);
goto v___jp_1746_;
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_del_object(v___x_1726_);
lean_dec(v_snd_1724_);
lean_dec(v_fst_1723_);
lean_dec(v_cmd_1707_);
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
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
lean_object* v___x_1864_; 
lean_dec(v_endPos_1730_);
lean_del_object(v___x_1721_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_fst_1723_);
lean_ctor_set(v___x_1864_, 1, v_snd_1724_);
v_a_1735_ = v___x_1864_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v___x_1865_; 
lean_dec(v_endPos_1730_);
lean_del_object(v___x_1721_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v_fst_1723_);
lean_ctor_set(v___x_1865_, 1, v_snd_1724_);
v_a_1735_ = v___x_1865_;
goto v___jp_1734_;
}
v___jp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_a_1735_);
lean_ctor_set(v___x_1726_, 0, v___x_1733_);
v___x_1737_ = v___x_1726_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_a_1735_);
v___x_1737_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
size_t v___x_1738_; size_t v___x_1739_; 
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_i_1712_, v___x_1738_);
v_i_1712_ = v___x_1739_;
v_b_1713_ = v___x_1737_;
goto _start;
}
}
v___jp_1742_:
{
lean_object* v___x_1744_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v_snd_1724_);
lean_ctor_set(v___x_1721_, 0, v_fst_1723_);
v___x_1744_ = v___x_1721_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_snd_1724_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v_a_1735_ = v___x_1744_;
goto v___jp_1734_;
}
}
v___jp_1746_:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_fst_1723_);
lean_ctor_set(v___x_1747_, 1, v_snd_1724_);
v_a_1735_ = v___x_1747_;
goto v___jp_1734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v___x_1869_, lean_object* v_val_1870_, lean_object* v_cmd_1871_, lean_object* v_onUnsolved_1872_, lean_object* v___y_1873_, lean_object* v_as_1874_, lean_object* v_sz_1875_, lean_object* v_i_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v_onUnsolved_boxed_1881_; uint8_t v___y_12957__boxed_1882_; size_t v_sz_boxed_1883_; size_t v_i_boxed_1884_; lean_object* v_res_1885_; 
v_onUnsolved_boxed_1881_ = lean_unbox(v_onUnsolved_1872_);
v___y_12957__boxed_1882_ = lean_unbox(v___y_1873_);
v_sz_boxed_1883_ = lean_unbox_usize(v_sz_1875_);
lean_dec(v_sz_1875_);
v_i_boxed_1884_ = lean_unbox_usize(v_i_1876_);
lean_dec(v_i_1876_);
v_res_1885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1869_, v_val_1870_, v_cmd_1871_, v_onUnsolved_boxed_1881_, v___y_12957__boxed_1882_, v_as_1874_, v_sz_boxed_1883_, v_i_boxed_1884_, v_b_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v_as_1874_);
lean_dec_ref(v_val_1870_);
lean_dec_ref(v___x_1869_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(lean_object* v___x_1886_, lean_object* v_val_1887_, lean_object* v_cmd_1888_, uint8_t v_onUnsolved_1889_, uint8_t v___y_1890_, lean_object* v_as_1891_, size_t v_sz_1892_, size_t v_i_1893_, lean_object* v_b_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_usize_dec_lt(v_i_1893_, v_sz_1892_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_dec(v_cmd_1888_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_b_1894_);
return v___x_1899_;
}
else
{
lean_object* v_snd_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_2048_; 
v_snd_1900_ = lean_ctor_get(v_b_1894_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_b_1894_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; 
v_unused_2049_ = lean_ctor_get(v_b_1894_, 0);
lean_dec(v_unused_2049_);
v___x_1902_ = v_b_1894_;
v_isShared_1903_ = v_isSharedCheck_2048_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_snd_1900_);
lean_dec(v_b_1894_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_2048_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_fst_1904_; lean_object* v_snd_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_2047_; 
v_fst_1904_ = lean_ctor_get(v_snd_1900_, 0);
v_snd_1905_ = lean_ctor_get(v_snd_1900_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_snd_1900_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_1907_ = v_snd_1900_;
v_isShared_1908_ = v_isSharedCheck_2047_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_snd_1905_);
lean_inc(v_fst_1904_);
lean_dec(v_snd_1900_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_2047_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_a_1909_; lean_object* v_pos_1910_; lean_object* v_endPos_1911_; uint8_t v_severity_1912_; lean_object* v_data_1913_; lean_object* v___x_1914_; lean_object* v_a_1916_; 
v_a_1909_ = lean_array_uget_borrowed(v_as_1891_, v_i_1893_);
v_pos_1910_ = lean_ctor_get(v_a_1909_, 1);
v_endPos_1911_ = lean_ctor_get(v_a_1909_, 2);
lean_inc(v_endPos_1911_);
v_severity_1912_ = lean_ctor_get_uint8(v_a_1909_, sizeof(void*)*5 + 1);
v_data_1913_ = lean_ctor_get(v_a_1909_, 4);
v___x_1914_ = lean_box(0);
if (v_severity_1912_ == 2)
{
lean_object* v___f_1929_; uint8_t v___x_1930_; 
v___f_1929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1913_);
v___x_1930_ = l_Lean_MessageData_hasTag(v___f_1929_, v_data_1913_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec(v_endPos_1911_);
lean_del_object(v___x_1902_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v_fst_1904_);
lean_ctor_set(v___x_1931_, 1, v_snd_1905_);
v_a_1916_ = v___x_1931_;
goto v___jp_1915_;
}
else
{
if (lean_obj_tag(v_endPos_1911_) == 1)
{
lean_object* v_val_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_2044_; 
v_val_1932_ = lean_ctor_get(v_endPos_1911_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_endPos_1911_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_1934_ = v_endPos_1911_;
v_isShared_1935_ = v_isSharedCheck_2044_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_val_1932_);
lean_dec(v_endPos_1911_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_2044_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; uint8_t v___x_1940_; 
lean_inc_ref(v_pos_1910_);
v___x_1936_ = l_Lean_FileMap_ofPosition(v___x_1886_, v_pos_1910_);
v___x_1937_ = l_Lean_FileMap_ofPosition(v___x_1886_, v_val_1932_);
lean_inc(v___x_1937_);
lean_inc(v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = 0;
v___x_1940_ = l_Lean_Syntax_Range_includes(v_val_1887_, v___x_1938_, v___x_1939_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec_ref_known(v___x_1938_, 2);
lean_dec(v___x_1937_);
lean_dec(v___x_1936_);
lean_del_object(v___x_1934_);
lean_del_object(v___x_1902_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_fst_1904_);
lean_ctor_set(v___x_1941_, 1, v_snd_1905_);
v_a_1916_ = v___x_1941_;
goto v___jp_1915_;
}
else
{
lean_object* v___x_1942_; 
lean_inc(v_cmd_1888_);
lean_inc_ref(v___x_1938_);
v___x_1942_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1938_, v_cmd_1888_);
if (lean_obj_tag(v___x_1942_) == 1)
{
lean_object* v_val_1943_; lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v___x_1937_);
lean_dec(v___x_1936_);
lean_del_object(v___x_1934_);
v_val_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_val_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v_fst_1944_ = lean_ctor_get(v_val_1943_, 0);
v_snd_1945_ = lean_ctor_get(v_val_1943_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_val_1943_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1947_ = v_val_1943_;
v_isShared_1948_ = v_isSharedCheck_2008_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_snd_1945_);
lean_inc(v_fst_1944_);
lean_dec(v_val_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_2008_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; uint8_t v___y_2006_; lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Syntax_getPos_x3f(v_fst_1944_, v___x_1939_);
if (lean_obj_tag(v___x_2007_) == 0)
{
v___y_2006_ = v___x_1940_;
goto v___jp_2005_;
}
else
{
lean_dec_ref_known(v___x_2007_, 1);
v___y_2006_ = v___x_1939_;
goto v___jp_2005_;
}
v___jp_1949_:
{
lean_object* v___x_1955_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 1, v_snd_1905_);
lean_ctor_set(v___x_1947_, 0, v_fst_1904_);
v___x_1955_ = v___x_1947_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_fst_1904_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_snd_1905_);
v___x_1955_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
size_t v_sz_1956_; size_t v___x_1957_; lean_object* v___x_1958_; 
v_sz_1956_ = lean_array_size(v___y_1950_);
v___x_1957_ = ((size_t)0ULL);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1938_, v_fst_1944_, v_snd_1945_, v___y_1951_, v___y_1950_, v_sz_1956_, v___x_1957_, v___x_1955_);
lean_dec_ref(v___y_1950_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v_fst_1960_; lean_object* v_snd_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v_fst_1960_ = lean_ctor_get(v_a_1959_, 0);
v_snd_1961_ = lean_ctor_get(v_a_1959_, 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_a_1959_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v_a_1959_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_snd_1961_);
lean_inc(v_fst_1960_);
lean_dec(v_a_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_fst_1960_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_snd_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
v_a_1916_ = v___x_1966_;
goto v___jp_1915_;
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_del_object(v___x_1907_);
lean_dec(v_cmd_1888_);
v_a_1969_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1958_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1958_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
v___jp_1978_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
lean_inc_ref(v___x_1938_);
v___x_1979_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1938_);
v___x_1980_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1913_);
v___x_1981_ = lean_array_get_size(v___x_1980_);
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = lean_nat_dec_eq(v___x_1981_, v___x_1982_);
if (v___x_1983_ == 0)
{
v___y_1950_ = v___x_1980_;
v___y_1951_ = v___x_1979_;
v___y_1952_ = v___y_1895_;
v___y_1953_ = v___y_1896_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v_scopes_1989_; lean_object* v___x_1990_; lean_object* v_opts_1991_; uint8_t v_hasTrace_1992_; 
v___x_1984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1985_ = l_Lean_inheritedTraceOptions;
v___x_1986_ = lean_st_ref_get(v___x_1985_);
v___x_1987_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1988_ = lean_st_ref_get(v___y_1896_);
v_scopes_1989_ = lean_ctor_get(v___x_1988_, 2);
lean_inc(v_scopes_1989_);
lean_dec(v___x_1988_);
v___x_1990_ = l_List_head_x21___redArg(v___x_1987_, v_scopes_1989_);
lean_dec(v_scopes_1989_);
v_opts_1991_ = lean_ctor_get(v___x_1990_, 1);
lean_inc_ref(v_opts_1991_);
lean_dec(v___x_1990_);
v_hasTrace_1992_ = lean_ctor_get_uint8(v_opts_1991_, sizeof(void*)*1);
if (v_hasTrace_1992_ == 0)
{
lean_dec_ref(v_opts_1991_);
lean_dec(v___x_1986_);
v___y_1950_ = v___x_1980_;
v___y_1951_ = v___x_1979_;
v___y_1952_ = v___y_1895_;
v___y_1953_ = v___y_1896_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1994_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1986_, v_opts_1991_, v___x_1993_);
lean_dec_ref(v_opts_1991_);
lean_dec(v___x_1986_);
if (v___x_1994_ == 0)
{
v___y_1950_ = v___x_1980_;
v___y_1951_ = v___x_1979_;
v___y_1952_ = v___y_1895_;
v___y_1953_ = v___y_1896_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1996_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1984_, v___x_1995_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_dec_ref_known(v___x_1996_, 1);
v___y_1950_ = v___x_1980_;
v___y_1951_ = v___x_1979_;
v___y_1952_ = v___y_1895_;
v___y_1953_ = v___y_1896_;
goto v___jp_1949_;
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v___x_1980_);
lean_dec(v___x_1979_);
lean_del_object(v___x_1947_);
lean_dec(v_snd_1945_);
lean_dec(v_fst_1944_);
lean_dec_ref_known(v___x_1938_, 2);
lean_del_object(v___x_1907_);
lean_dec(v_snd_1905_);
lean_dec(v_fst_1904_);
lean_dec(v_cmd_1888_);
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
v___jp_2005_:
{
if (v_onUnsolved_1889_ == 0)
{
if (v___y_1890_ == 0)
{
lean_del_object(v___x_1947_);
lean_dec(v_snd_1945_);
lean_dec(v_fst_1944_);
lean_dec_ref_known(v___x_1938_, 2);
goto v___jp_1923_;
}
else
{
if (v___y_2006_ == 0)
{
lean_del_object(v___x_1947_);
lean_dec(v_snd_1945_);
lean_dec(v_fst_1944_);
lean_dec_ref_known(v___x_1938_, 2);
goto v___jp_1923_;
}
else
{
lean_del_object(v___x_1902_);
goto v___jp_1978_;
}
}
}
else
{
lean_del_object(v___x_1902_);
goto v___jp_1978_;
}
}
}
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v_scopes_2014_; lean_object* v___x_2015_; lean_object* v_opts_2016_; uint8_t v_hasTrace_2017_; 
lean_dec(v___x_1942_);
lean_dec_ref_known(v___x_1938_, 2);
lean_del_object(v___x_1902_);
v___x_2009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2010_ = l_Lean_inheritedTraceOptions;
v___x_2011_ = lean_st_ref_get(v___x_2010_);
v___x_2012_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2013_ = lean_st_ref_get(v___y_1896_);
v_scopes_2014_ = lean_ctor_get(v___x_2013_, 2);
lean_inc(v_scopes_2014_);
lean_dec(v___x_2013_);
v___x_2015_ = l_List_head_x21___redArg(v___x_2012_, v_scopes_2014_);
lean_dec(v_scopes_2014_);
v_opts_2016_ = lean_ctor_get(v___x_2015_, 1);
lean_inc_ref(v_opts_2016_);
lean_dec(v___x_2015_);
v_hasTrace_2017_ = lean_ctor_get_uint8(v_opts_2016_, sizeof(void*)*1);
if (v_hasTrace_2017_ == 0)
{
lean_dec_ref(v_opts_2016_);
lean_dec(v___x_2011_);
lean_dec(v___x_1937_);
lean_dec(v___x_1936_);
lean_del_object(v___x_1934_);
goto v___jp_1927_;
}
else
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2019_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2011_, v_opts_2016_, v___x_2018_);
lean_dec_ref(v_opts_2016_);
lean_dec(v___x_2011_);
if (v___x_2019_ == 0)
{
lean_dec(v___x_1937_);
lean_dec(v___x_1936_);
lean_del_object(v___x_1934_);
goto v___jp_1927_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2020_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_2021_ = l_Nat_reprFast(v___x_1936_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 3);
lean_ctor_set(v___x_1934_, 0, v___x_2021_);
v___x_2023_ = v___x_1934_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2024_ = l_Lean_MessageData_ofFormat(v___x_2023_);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2020_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = l_Nat_reprFast(v___x_1937_);
v___x_2029_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
v___x_2030_ = l_Lean_MessageData_ofFormat(v___x_2029_);
v___x_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2027_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2009_, v___x_2033_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_dec_ref_known(v___x_2034_, 1);
goto v___jp_1927_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_del_object(v___x_1907_);
lean_dec(v_snd_1905_);
lean_dec(v_fst_1904_);
lean_dec(v_cmd_1888_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
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
lean_object* v___x_2045_; 
lean_dec(v_endPos_1911_);
lean_del_object(v___x_1902_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_fst_1904_);
lean_ctor_set(v___x_2045_, 1, v_snd_1905_);
v_a_1916_ = v___x_2045_;
goto v___jp_1915_;
}
}
}
else
{
lean_object* v___x_2046_; 
lean_dec(v_endPos_1911_);
lean_del_object(v___x_1902_);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_fst_1904_);
lean_ctor_set(v___x_2046_, 1, v_snd_1905_);
v_a_1916_ = v___x_2046_;
goto v___jp_1915_;
}
v___jp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v_a_1916_);
lean_ctor_set(v___x_1907_, 0, v___x_1914_);
v___x_1918_ = v___x_1907_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_a_1916_);
v___x_1918_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
size_t v___x_1919_; size_t v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = ((size_t)1ULL);
v___x_1920_ = lean_usize_add(v_i_1893_, v___x_1919_);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1886_, v_val_1887_, v_cmd_1888_, v_onUnsolved_1889_, v___y_1890_, v_as_1891_, v_sz_1892_, v___x_1920_, v___x_1918_, v___y_1895_, v___y_1896_);
return v___x_1921_;
}
}
v___jp_1923_:
{
lean_object* v___x_1925_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_snd_1905_);
lean_ctor_set(v___x_1902_, 0, v_fst_1904_);
v___x_1925_ = v___x_1902_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_fst_1904_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_snd_1905_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
v_a_1916_ = v___x_1925_;
goto v___jp_1915_;
}
}
v___jp_1927_:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_fst_1904_);
lean_ctor_set(v___x_1928_, 1, v_snd_1905_);
v_a_1916_ = v___x_1928_;
goto v___jp_1915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11___boxed(lean_object* v___x_2050_, lean_object* v_val_2051_, lean_object* v_cmd_2052_, lean_object* v_onUnsolved_2053_, lean_object* v___y_2054_, lean_object* v_as_2055_, lean_object* v_sz_2056_, lean_object* v_i_2057_, lean_object* v_b_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
uint8_t v_onUnsolved_boxed_2062_; uint8_t v___y_13289__boxed_2063_; size_t v_sz_boxed_2064_; size_t v_i_boxed_2065_; lean_object* v_res_2066_; 
v_onUnsolved_boxed_2062_ = lean_unbox(v_onUnsolved_2053_);
v___y_13289__boxed_2063_ = lean_unbox(v___y_2054_);
v_sz_boxed_2064_ = lean_unbox_usize(v_sz_2056_);
lean_dec(v_sz_2056_);
v_i_boxed_2065_ = lean_unbox_usize(v_i_2057_);
lean_dec(v_i_2057_);
v_res_2066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2050_, v_val_2051_, v_cmd_2052_, v_onUnsolved_boxed_2062_, v___y_13289__boxed_2063_, v_as_2055_, v_sz_boxed_2064_, v_i_boxed_2065_, v_b_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec_ref(v_as_2055_);
lean_dec_ref(v_val_2051_);
lean_dec_ref(v___x_2050_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(lean_object* v_init_2067_, lean_object* v___x_2068_, lean_object* v_val_2069_, lean_object* v_cmd_2070_, uint8_t v_onUnsolved_2071_, uint8_t v___y_2072_, lean_object* v_n_2073_, lean_object* v_b_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
if (lean_obj_tag(v_n_2073_) == 0)
{
lean_object* v_cs_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; size_t v_sz_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
v_cs_2078_ = lean_ctor_get(v_n_2073_, 0);
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_b_2074_);
v_sz_2081_ = lean_array_size(v_cs_2078_);
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2067_, v___x_2068_, v_val_2069_, v_cmd_2070_, v_onUnsolved_2071_, v___y_2072_, v_cs_2078_, v_sz_2081_, v___x_2082_, v___x_2080_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2098_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_fst_2088_; 
v_fst_2088_ = lean_ctor_get(v_a_2084_, 0);
if (lean_obj_tag(v_fst_2088_) == 0)
{
lean_object* v_snd_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v_snd_2089_ = lean_ctor_get(v_a_2084_, 1);
lean_inc(v_snd_2089_);
lean_dec(v_a_2084_);
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_snd_2089_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2090_);
v___x_2092_ = v___x_2086_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; 
lean_inc_ref(v_fst_2088_);
lean_dec(v_a_2084_);
v_val_2094_ = lean_ctor_get(v_fst_2088_, 0);
lean_inc(v_val_2094_);
lean_dec_ref_known(v_fst_2088_, 1);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v_val_2094_);
v___x_2096_ = v___x_2086_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_val_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2083_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2083_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_vs_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; size_t v_sz_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v_vs_2107_ = lean_ctor_get(v_n_2073_, 0);
v___x_2108_ = lean_box(0);
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v_b_2074_);
v_sz_2110_ = lean_array_size(v_vs_2107_);
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2068_, v_val_2069_, v_cmd_2070_, v_onUnsolved_2071_, v___y_2072_, v_vs_2107_, v_sz_2110_, v___x_2111_, v___x_2109_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2127_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2127_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2127_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_fst_2117_; 
v_fst_2117_ = lean_ctor_get(v_a_2113_, 0);
if (lean_obj_tag(v_fst_2117_) == 0)
{
lean_object* v_snd_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v_snd_2118_ = lean_ctor_get(v_a_2113_, 1);
lean_inc(v_snd_2118_);
lean_dec(v_a_2113_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v_snd_2118_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2119_);
v___x_2121_ = v___x_2115_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
else
{
lean_object* v_val_2123_; lean_object* v___x_2125_; 
lean_inc_ref(v_fst_2117_);
lean_dec(v_a_2113_);
v_val_2123_ = lean_ctor_get(v_fst_2117_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v_fst_2117_, 1);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_val_2123_);
v___x_2125_ = v___x_2115_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_val_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
v_a_2128_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2112_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2112_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(lean_object* v_init_2136_, lean_object* v___x_2137_, lean_object* v_val_2138_, lean_object* v_cmd_2139_, uint8_t v_onUnsolved_2140_, uint8_t v___y_2141_, lean_object* v_as_2142_, size_t v_sz_2143_, size_t v_i_2144_, lean_object* v_b_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_usize_dec_lt(v_i_2144_, v_sz_2143_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_dec(v_cmd_2139_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_b_2145_);
return v___x_2150_;
}
else
{
lean_object* v_snd_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2185_; 
v_snd_2151_ = lean_ctor_get(v_b_2145_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_b_2145_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v_b_2145_, 0);
lean_dec(v_unused_2186_);
v___x_2153_ = v_b_2145_;
v_isShared_2154_ = v_isSharedCheck_2185_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_snd_2151_);
lean_dec(v_b_2145_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2185_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v_a_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(0);
v_a_2156_ = lean_array_uget_borrowed(v_as_2142_, v_i_2144_);
lean_inc(v_snd_2151_);
lean_inc(v_cmd_2139_);
v___x_2157_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2136_, v___x_2137_, v_val_2138_, v_cmd_2139_, v_onUnsolved_2140_, v___y_2141_, v_a_2156_, v_snd_2151_, v___y_2146_, v___y_2147_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2176_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2176_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2176_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
if (lean_obj_tag(v_a_2158_) == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec(v_cmd_2139_);
v___x_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2162_, 0, v_a_2158_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2162_);
v___x_2164_ = v___x_2153_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_snd_2151_);
v___x_2164_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2166_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2164_);
v___x_2166_ = v___x_2160_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; 
lean_del_object(v___x_2160_);
lean_dec(v_snd_2151_);
v_a_2169_ = lean_ctor_get(v_a_2158_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v_a_2158_, 1);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v_a_2169_);
lean_ctor_set(v___x_2153_, 0, v___x_2155_);
v___x_2171_ = v___x_2153_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_a_2169_);
v___x_2171_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
size_t v___x_2172_; size_t v___x_2173_; 
v___x_2172_ = ((size_t)1ULL);
v___x_2173_ = lean_usize_add(v_i_2144_, v___x_2172_);
v_i_2144_ = v___x_2173_;
v_b_2145_ = v___x_2171_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_del_object(v___x_2153_);
lean_dec(v_snd_2151_);
lean_dec(v_cmd_2139_);
v_a_2177_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2157_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2157_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10___boxed(lean_object* v_init_2187_, lean_object* v___x_2188_, lean_object* v_val_2189_, lean_object* v_cmd_2190_, lean_object* v_onUnsolved_2191_, lean_object* v___y_2192_, lean_object* v_as_2193_, lean_object* v_sz_2194_, lean_object* v_i_2195_, lean_object* v_b_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v_onUnsolved_boxed_2200_; uint8_t v___y_13590__boxed_2201_; size_t v_sz_boxed_2202_; size_t v_i_boxed_2203_; lean_object* v_res_2204_; 
v_onUnsolved_boxed_2200_ = lean_unbox(v_onUnsolved_2191_);
v___y_13590__boxed_2201_ = lean_unbox(v___y_2192_);
v_sz_boxed_2202_ = lean_unbox_usize(v_sz_2194_);
lean_dec(v_sz_2194_);
v_i_boxed_2203_ = lean_unbox_usize(v_i_2195_);
lean_dec(v_i_2195_);
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2187_, v___x_2188_, v_val_2189_, v_cmd_2190_, v_onUnsolved_boxed_2200_, v___y_13590__boxed_2201_, v_as_2193_, v_sz_boxed_2202_, v_i_boxed_2203_, v_b_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec_ref(v_as_2193_);
lean_dec_ref(v_val_2189_);
lean_dec_ref(v___x_2188_);
lean_dec_ref(v_init_2187_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8___boxed(lean_object* v_init_2205_, lean_object* v___x_2206_, lean_object* v_val_2207_, lean_object* v_cmd_2208_, lean_object* v_onUnsolved_2209_, lean_object* v___y_2210_, lean_object* v_n_2211_, lean_object* v_b_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
uint8_t v_onUnsolved_boxed_2216_; uint8_t v___y_13612__boxed_2217_; lean_object* v_res_2218_; 
v_onUnsolved_boxed_2216_ = lean_unbox(v_onUnsolved_2209_);
v___y_13612__boxed_2217_ = lean_unbox(v___y_2210_);
v_res_2218_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2205_, v___x_2206_, v_val_2207_, v_cmd_2208_, v_onUnsolved_boxed_2216_, v___y_13612__boxed_2217_, v_n_2211_, v_b_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec_ref(v_n_2211_);
lean_dec_ref(v_val_2207_);
lean_dec_ref(v___x_2206_);
lean_dec_ref(v_init_2205_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object* v___x_2219_, lean_object* v_val_2220_, lean_object* v_cmd_2221_, uint8_t v_onUnsolved_2222_, uint8_t v___y_2223_, lean_object* v_t_2224_, lean_object* v_init_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_root_2229_; lean_object* v_tail_2230_; lean_object* v___x_2231_; 
v_root_2229_ = lean_ctor_get(v_t_2224_, 0);
v_tail_2230_ = lean_ctor_get(v_t_2224_, 1);
lean_inc(v_cmd_2221_);
lean_inc_ref(v_init_2225_);
v___x_2231_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2225_, v___x_2219_, v_val_2220_, v_cmd_2221_, v_onUnsolved_2222_, v___y_2223_, v_root_2229_, v_init_2225_, v___y_2226_, v___y_2227_);
lean_dec_ref(v_init_2225_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2268_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2268_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2268_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
if (lean_obj_tag(v_a_2232_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; 
lean_dec(v_cmd_2221_);
v_a_2236_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v_a_2232_, 1);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v_a_2236_);
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
lean_del_object(v___x_2234_);
v_a_2240_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v_a_2232_, 1);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v_a_2240_);
v_sz_2243_ = lean_array_size(v_tail_2230_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_2219_, v_val_2220_, v_cmd_2221_, v_onUnsolved_2222_, v___y_2223_, v_tail_2230_, v_sz_2243_, v___x_2244_, v___x_2242_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2259_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_fst_2250_; 
v_fst_2250_ = lean_ctor_get(v_a_2246_, 0);
if (lean_obj_tag(v_fst_2250_) == 0)
{
lean_object* v_snd_2251_; lean_object* v___x_2253_; 
v_snd_2251_ = lean_ctor_get(v_a_2246_, 1);
lean_inc(v_snd_2251_);
lean_dec(v_a_2246_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v_snd_2251_);
v___x_2253_ = v___x_2248_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_snd_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
else
{
lean_object* v_val_2255_; lean_object* v___x_2257_; 
lean_inc_ref(v_fst_2250_);
lean_dec(v_a_2246_);
v_val_2255_ = lean_ctor_get(v_fst_2250_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v_fst_2250_, 1);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v_val_2255_);
v___x_2257_ = v___x_2248_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_val_2255_);
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
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_a_2260_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2245_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2245_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_cmd_2221_);
v_a_2269_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2231_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2231_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object* v___x_2277_, lean_object* v_val_2278_, lean_object* v_cmd_2279_, lean_object* v_onUnsolved_2280_, lean_object* v___y_2281_, lean_object* v_t_2282_, lean_object* v_init_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
uint8_t v_onUnsolved_boxed_2287_; uint8_t v___y_13803__boxed_2288_; lean_object* v_res_2289_; 
v_onUnsolved_boxed_2287_ = lean_unbox(v_onUnsolved_2280_);
v___y_13803__boxed_2288_ = lean_unbox(v___y_2281_);
v_res_2289_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2277_, v_val_2278_, v_cmd_2279_, v_onUnsolved_boxed_2287_, v___y_13803__boxed_2288_, v_t_2282_, v_init_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec_ref(v_t_2282_);
lean_dec_ref(v_val_2278_);
lean_dec_ref(v___x_2277_);
return v_res_2289_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_box(0);
v___x_2291_ = lean_unsigned_to_nat(16u);
v___x_2292_ = lean_mk_array(v___x_2291_, v___x_2290_);
return v___x_2292_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v___x_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2299_, lean_object* v_opts_2300_, lean_object* v_tree_2301_, lean_object* v_msgs_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
uint8_t v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; uint8_t v___y_2310_; lean_object* v___y_2311_; uint8_t v___y_2338_; uint8_t v___y_2339_; lean_object* v_acc_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___f_2344_; uint8_t v___y_2346_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___f_2344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2353_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2354_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2300_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2356_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2300_, v___x_2355_);
v___y_2346_ = v___x_2356_;
goto v___jp_2345_;
}
else
{
v___y_2346_ = v___x_2354_;
goto v___jp_2345_;
}
v___jp_2306_:
{
uint8_t v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = 1;
v___x_2313_ = l_Lean_Syntax_getRange_x3f(v_cmd_2299_, v___x_2312_);
if (lean_obj_tag(v___x_2313_) == 1)
{
lean_object* v_val_2314_; lean_object* v_fileMap_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_val_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v_fileMap_2315_ = lean_ctor_get(v___y_2308_, 1);
v___x_2316_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___y_2311_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v_fileMap_2315_, v_val_2314_, v_cmd_2299_, v___y_2307_, v___y_2310_, v_msgs_2302_, v___x_2317_, v___y_2308_, v___y_2309_);
lean_dec(v_val_2314_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2327_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2327_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2327_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_fst_2323_; lean_object* v___x_2325_; 
v_fst_2323_ = lean_ctor_get(v_a_2319_, 0);
lean_inc(v_fst_2323_);
lean_dec(v_a_2319_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v_fst_2323_);
v___x_2325_ = v___x_2321_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_fst_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
v_a_2328_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2318_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2318_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v___x_2336_; 
lean_dec(v___x_2313_);
lean_dec(v_cmd_2299_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___y_2311_);
return v___x_2336_;
}
}
v___jp_2337_:
{
if (v___y_2338_ == 0)
{
if (v___y_2339_ == 0)
{
lean_object* v___x_2343_; 
lean_dec(v_cmd_2299_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_acc_2340_);
return v___x_2343_;
}
else
{
v___y_2307_ = v___y_2338_;
v___y_2308_ = v___y_2341_;
v___y_2309_ = v___y_2342_;
v___y_2310_ = v___y_2339_;
v___y_2311_ = v_acc_2340_;
goto v___jp_2306_;
}
}
else
{
v___y_2307_ = v___y_2338_;
v___y_2308_ = v___y_2341_;
v___y_2309_ = v___y_2342_;
v___y_2310_ = v___y_2339_;
v___y_2311_ = v_acc_2340_;
goto v___jp_2306_;
}
}
v___jp_2345_:
{
lean_object* v___x_2347_; uint8_t v_onUnsolved_2348_; lean_object* v___x_2349_; uint8_t v_onSorry_2350_; lean_object* v_acc_2351_; 
v___x_2347_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2348_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2300_, v___x_2347_);
v___x_2349_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2350_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2300_, v___x_2349_);
v_acc_2351_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2350_ == 0)
{
lean_dec_ref(v_tree_2301_);
v___y_2338_ = v_onUnsolved_2348_;
v___y_2339_ = v___y_2346_;
v_acc_2340_ = v_acc_2351_;
v___y_2341_ = v_a_2303_;
v___y_2342_ = v_a_2304_;
goto v___jp_2337_;
}
else
{
lean_object* v_acc_2352_; 
v_acc_2352_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2344_, v_acc_2351_, v_tree_2301_);
v___y_2338_ = v_onUnsolved_2348_;
v___y_2339_ = v___y_2346_;
v_acc_2340_ = v_acc_2352_;
v___y_2341_ = v_a_2303_;
v___y_2342_ = v_a_2304_;
goto v___jp_2337_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2357_, lean_object* v_opts_2358_, lean_object* v_tree_2359_, lean_object* v_msgs_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2357_, v_opts_2358_, v_tree_2359_, v_msgs_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec_ref(v_msgs_2360_);
lean_dec_ref(v_opts_2358_);
return v_res_2364_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2365_, lean_object* v_m_2366_, lean_object* v_a_2367_){
_start:
{
uint8_t v___x_2368_; 
v___x_2368_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2366_, v_a_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object* v_00_u03b2_2369_, lean_object* v_m_2370_, lean_object* v_a_2371_){
_start:
{
uint8_t v_res_2372_; lean_object* v_r_2373_; 
v_res_2372_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(v_00_u03b2_2369_, v_m_2370_, v_a_2371_);
lean_dec_ref(v_a_2371_);
lean_dec_ref(v_m_2370_);
v_r_2373_ = lean_box(v_res_2372_);
return v_r_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v_00_u03b2_2374_, lean_object* v_m_2375_, lean_object* v_a_2376_, lean_object* v_b_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_2375_, v_a_2376_, v_b_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v___x_2379_, lean_object* v_fst_2380_, lean_object* v_snd_2381_, lean_object* v___x_2382_, lean_object* v_as_2383_, size_t v_sz_2384_, size_t v_i_2385_, lean_object* v_b_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_2379_, v_fst_2380_, v_snd_2381_, v___x_2382_, v_as_2383_, v_sz_2384_, v_i_2385_, v_b_2386_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v___x_2391_, lean_object* v_fst_2392_, lean_object* v_snd_2393_, lean_object* v___x_2394_, lean_object* v_as_2395_, lean_object* v_sz_2396_, lean_object* v_i_2397_, lean_object* v_b_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
size_t v_sz_boxed_2402_; size_t v_i_boxed_2403_; lean_object* v_res_2404_; 
v_sz_boxed_2402_ = lean_unbox_usize(v_sz_2396_);
lean_dec(v_sz_2396_);
v_i_boxed_2403_ = lean_unbox_usize(v_i_2397_);
lean_dec(v_i_2397_);
v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2391_, v_fst_2392_, v_snd_2393_, v___x_2394_, v_as_2395_, v_sz_boxed_2402_, v_i_boxed_2403_, v_b_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec_ref(v_as_2395_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(lean_object* v_msgData_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_2405_, v___y_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___boxed(lean_object* v_msgData_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(v_msgData_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2414_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_object* v_00_u03b2_2415_, lean_object* v_a_2416_, lean_object* v_x_2417_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_2416_, v_x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2419_, lean_object* v_a_2420_, lean_object* v_x_2421_){
_start:
{
uint8_t v_res_2422_; lean_object* v_r_2423_; 
v_res_2422_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(v_00_u03b2_2419_, v_a_2420_, v_x_2421_);
lean_dec(v_x_2421_);
lean_dec_ref(v_a_2420_);
v_r_2423_ = lean_box(v_res_2422_);
return v_r_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3(lean_object* v_00_u03b2_2424_, lean_object* v_data_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_data_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2427_, lean_object* v_i_2428_, lean_object* v_source_2429_, lean_object* v_target_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v_i_2428_, v_source_2429_, v_target_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_x_2433_, v_x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
v___x_2444_ = lean_apply_7(v_x_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, lean_box(0));
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2454_, lean_object* v_x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___f_2463_; lean_object* v___x_2464_; 
lean_inc(v___y_2457_);
lean_inc_ref(v___y_2456_);
v___f_2463_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2463_, 0, v_x_2455_);
lean_closure_set(v___f_2463_, 1, v___y_2456_);
lean_closure_set(v___f_2463_, 2, v___y_2457_);
v___x_2464_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2454_, v___f_2463_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2464_) == 0)
{
return v___x_2464_;
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2473_, lean_object* v_x_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2473_, v_x_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2483_, lean_object* v_mvarId_2484_, lean_object* v_x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2484_, v_x_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_mvarId_2495_, lean_object* v_x_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2494_, v_mvarId_2495_, v_x_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2546_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2547_, lean_object* v_x_2548_){
_start:
{
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2549_, lean_object* v_x_2550_){
_start:
{
uint8_t v___x_10973__boxed_2551_; uint8_t v_res_2552_; lean_object* v_r_2553_; 
v___x_10973__boxed_2551_ = lean_unbox(v___x_2549_);
v_res_2552_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_10973__boxed_2551_, v_x_2550_);
lean_dec(v_x_2550_);
v_r_2553_ = lean_box(v_res_2552_);
return v_r_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v_env_2561_; uint8_t v___x_2562_; lean_object* v_env_2563_; lean_object* v___x_2564_; lean_object* v_toCold_2565_; lean_object* v_mctx_2566_; lean_object* v_lctx_2567_; lean_object* v_options_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2560_ = lean_st_ref_get(v___y_2558_);
v_env_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc_ref(v_env_2561_);
lean_dec(v___x_2560_);
v___x_2562_ = 0;
v_env_2563_ = l_Lean_Environment_setRecordingDeps(v_env_2561_, v___x_2562_);
v___x_2564_ = lean_st_ref_get(v___y_2556_);
v_toCold_2565_ = lean_ctor_get(v___y_2557_, 0);
v_mctx_2566_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_ref(v_mctx_2566_);
lean_dec(v___x_2564_);
v_lctx_2567_ = lean_ctor_get(v___y_2555_, 2);
v_options_2568_ = lean_ctor_get(v_toCold_2565_, 2);
lean_inc_ref(v_options_2568_);
lean_inc_ref(v_lctx_2567_);
v___x_2569_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2569_, 0, v_env_2563_);
lean_ctor_set(v___x_2569_, 1, v_mctx_2566_);
lean_ctor_set(v___x_2569_, 2, v_lctx_2567_);
lean_ctor_set(v___x_2569_, 3, v_options_2568_);
v___x_2570_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v_msgData_2554_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2579_, lean_object* v_msg_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_ref_2586_; lean_object* v___x_2587_; lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2633_; 
v_ref_2586_ = lean_ctor_get(v___y_2583_, 2);
v___x_2587_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2633_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2633_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v_traceState_2593_; lean_object* v_env_2594_; lean_object* v_nextMacroScope_2595_; lean_object* v_ngen_2596_; lean_object* v_auxDeclNGen_2597_; lean_object* v_cache_2598_; lean_object* v_recordedDeps_2599_; lean_object* v_messages_2600_; lean_object* v_infoState_2601_; lean_object* v_snapshotTasks_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2632_; 
v___x_2592_ = lean_st_ref_take(v___y_2584_);
v_traceState_2593_ = lean_ctor_get(v___x_2592_, 4);
v_env_2594_ = lean_ctor_get(v___x_2592_, 0);
v_nextMacroScope_2595_ = lean_ctor_get(v___x_2592_, 1);
v_ngen_2596_ = lean_ctor_get(v___x_2592_, 2);
v_auxDeclNGen_2597_ = lean_ctor_get(v___x_2592_, 3);
v_cache_2598_ = lean_ctor_get(v___x_2592_, 5);
v_recordedDeps_2599_ = lean_ctor_get(v___x_2592_, 6);
v_messages_2600_ = lean_ctor_get(v___x_2592_, 7);
v_infoState_2601_ = lean_ctor_get(v___x_2592_, 8);
v_snapshotTasks_2602_ = lean_ctor_get(v___x_2592_, 9);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2604_ = v___x_2592_;
v_isShared_2605_ = v_isSharedCheck_2632_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_snapshotTasks_2602_);
lean_inc(v_infoState_2601_);
lean_inc(v_messages_2600_);
lean_inc(v_recordedDeps_2599_);
lean_inc(v_cache_2598_);
lean_inc(v_traceState_2593_);
lean_inc(v_auxDeclNGen_2597_);
lean_inc(v_ngen_2596_);
lean_inc(v_nextMacroScope_2595_);
lean_inc(v_env_2594_);
lean_dec(v___x_2592_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2632_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
uint64_t v_tid_2606_; lean_object* v_traces_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2631_; 
v_tid_2606_ = lean_ctor_get_uint64(v_traceState_2593_, sizeof(void*)*1);
v_traces_2607_ = lean_ctor_get(v_traceState_2593_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_traceState_2593_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2609_ = v_traceState_2593_;
v_isShared_2610_ = v_isSharedCheck_2631_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_traces_2607_);
lean_dec(v_traceState_2593_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2631_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; double v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2614_ = 0;
v___x_2615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2616_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2616_, 0, v_cls_2579_);
lean_ctor_set(v___x_2616_, 1, v___x_2612_);
lean_ctor_set(v___x_2616_, 2, v___x_2615_);
lean_ctor_set_float(v___x_2616_, sizeof(void*)*3, v___x_2613_);
lean_ctor_set_float(v___x_2616_, sizeof(void*)*3 + 8, v___x_2613_);
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*3 + 16, v___x_2614_);
v___x_2617_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2618_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2616_);
lean_ctor_set(v___x_2618_, 1, v_a_2588_);
lean_ctor_set(v___x_2618_, 2, v___x_2617_);
lean_inc(v_ref_2586_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_ref_2586_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Lean_PersistentArray_push___redArg(v_traces_2607_, v___x_2619_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2620_);
v___x_2622_ = v___x_2609_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2620_);
lean_ctor_set_uint64(v_reuseFailAlloc_2630_, sizeof(void*)*1, v_tid_2606_);
v___x_2622_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 4, v___x_2622_);
v___x_2624_ = v___x_2604_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_env_2594_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_nextMacroScope_2595_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_ngen_2596_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v_auxDeclNGen_2597_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2629_, 5, v_cache_2598_);
lean_ctor_set(v_reuseFailAlloc_2629_, 6, v_recordedDeps_2599_);
lean_ctor_set(v_reuseFailAlloc_2629_, 7, v_messages_2600_);
lean_ctor_set(v_reuseFailAlloc_2629_, 8, v_infoState_2601_);
lean_ctor_set(v_reuseFailAlloc_2629_, 9, v_snapshotTasks_2602_);
v___x_2624_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = lean_st_ref_put(v___y_2584_, v___x_2624_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2611_);
v___x_2627_ = v___x_2590_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2611_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2634_, lean_object* v_msg_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2634_, v_msg_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
return v_res_2641_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2644_ = l_Lean_stringToMessageData(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2645_, lean_object* v___f_2646_, lean_object* v___x_2647_, lean_object* v___x_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; lean_object* v_a_2658_; lean_object* v___y_2662_; lean_object* v___x_2676_; 
v___x_2656_ = lean_st_mk_ref(v___x_2645_);
v___x_2676_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2656_, v___y_2650_, v___y_2652_, v___y_2654_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2648_, v___x_2647_, v___x_2656_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; 
lean_dec(v_a_2677_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2647_);
lean_dec_ref(v___f_2646_);
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v_a_2658_ = v_a_2679_;
goto v___jp_2657_;
}
else
{
lean_object* v_a_2680_; uint8_t v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2678_, 0);
v___x_2681_ = l_Lean_Exception_isInterrupt(v_a_2680_);
if (v___x_2681_ == 0)
{
uint8_t v___x_2682_; 
lean_inc(v_a_2680_);
v___x_2682_ = l_Lean_Exception_isRuntime(v_a_2680_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2683_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2677_, v___x_2682_, v___x_2656_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2712_; 
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; 
v_unused_2713_ = lean_ctor_get(v___x_2683_, 0);
lean_dec(v_unused_2713_);
v___x_2685_ = v___x_2683_;
v_isShared_2686_ = v_isSharedCheck_2712_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v___x_2683_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2712_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
uint8_t v___x_2687_; 
lean_inc(v_a_2680_);
v___x_2687_ = l_Lean_Exception_isMaxRecDepth(v_a_2680_);
if (v___x_2687_ == 0)
{
lean_object* v_toCold_2688_; lean_object* v_options_2689_; uint8_t v_hasTrace_2690_; 
lean_del_object(v___x_2685_);
v_toCold_2688_ = lean_ctor_get(v___y_2653_, 0);
v_options_2689_ = lean_ctor_get(v_toCold_2688_, 2);
v_hasTrace_2690_ = lean_ctor_get_uint8(v_options_2689_, sizeof(void*)*1);
if (v_hasTrace_2690_ == 0)
{
lean_dec(v_a_2680_);
goto v___jp_2673_;
}
else
{
lean_object* v_inheritedTraceOptions_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v_inheritedTraceOptions_2691_ = lean_ctor_get(v_toCold_2688_, 11);
v___x_2692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2693_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2694_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2691_, v_options_2689_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_dec(v_a_2680_);
goto v___jp_2673_;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2695_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2696_ = l_Lean_Exception_toMessageData(v_a_2680_);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2692_, v___x_2697_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2700_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
lean_inc(v___x_2656_);
v___x_2700_ = lean_apply_10(v___f_2646_, v_a_2699_, v___x_2647_, v___x_2656_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, lean_box(0));
v___y_2662_ = v___x_2700_;
goto v___jp_2661_;
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v___x_2656_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2647_);
lean_dec_ref(v___f_2646_);
v_a_2701_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2698_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2698_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
else
{
lean_object* v___x_2710_; 
lean_dec(v___x_2656_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2647_);
lean_dec_ref(v___f_2646_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set_tag(v___x_2685_, 1);
lean_ctor_set(v___x_2685_, 0, v_a_2680_);
v___x_2710_ = v___x_2685_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2680_);
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
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2680_);
lean_dec(v___x_2656_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2647_);
lean_dec_ref(v___f_2646_);
v_a_2714_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2683_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2683_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_dec(v_a_2677_);
lean_dec(v___x_2656_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2647_);
lean_dec_ref(v___f_2646_);
return v___x_2678_;
}
}
else
{
lean_dec(v_a_2677_);
lean_dec(v___x_2656_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2647_);
lean_dec_ref(v___f_2646_);
return v___x_2678_;
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___x_2656_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2648_);
lean_dec_ref(v___x_2647_);
lean_dec_ref(v___f_2646_);
v_a_2722_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2676_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2676_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
v___jp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = lean_st_ref_get(v___x_2656_);
lean_dec(v___x_2656_);
lean_dec(v___x_2659_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_a_2658_);
return v___x_2660_;
}
v___jp_2661_:
{
if (lean_obj_tag(v___y_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v_a_2664_; 
v_a_2663_ = lean_ctor_get(v___y_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___y_2662_, 1);
v_a_2664_ = lean_ctor_get(v_a_2663_, 0);
lean_inc(v_a_2664_);
lean_dec(v_a_2663_);
v_a_2658_ = v_a_2664_;
goto v___jp_2657_;
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v___x_2656_);
v_a_2665_ = lean_ctor_get(v___y_2662_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___y_2662_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___y_2662_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___y_2662_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
v___jp_2673_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_box(0);
lean_inc(v___x_2656_);
v___x_2675_ = lean_apply_10(v___f_2646_, v___x_2674_, v___x_2647_, v___x_2656_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, lean_box(0));
v___y_2662_ = v___x_2675_;
goto v___jp_2661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2730_, lean_object* v___f_2731_, lean_object* v___x_2732_, lean_object* v___x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2730_, v___f_2731_, v___x_2732_, v___x_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2742_, uint8_t v___x_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2742_, v___x_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2752_, lean_object* v___x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
uint8_t v___x_11292__boxed_2761_; lean_object* v_res_2762_; 
v___x_11292__boxed_2761_ = lean_unbox(v___x_2753_);
v_res_2762_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2752_, v___x_11292__boxed_2761_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2763_, lean_object* v_msg_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_ref_2770_; lean_object* v___x_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2817_; 
v_ref_2770_ = lean_ctor_get(v___y_2767_, 2);
v___x_2771_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2817_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2817_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v_traceState_2777_; lean_object* v_env_2778_; lean_object* v_nextMacroScope_2779_; lean_object* v_ngen_2780_; lean_object* v_auxDeclNGen_2781_; lean_object* v_cache_2782_; lean_object* v_recordedDeps_2783_; lean_object* v_messages_2784_; lean_object* v_infoState_2785_; lean_object* v_snapshotTasks_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2816_; 
v___x_2776_ = lean_st_ref_take(v___y_2768_);
v_traceState_2777_ = lean_ctor_get(v___x_2776_, 4);
v_env_2778_ = lean_ctor_get(v___x_2776_, 0);
v_nextMacroScope_2779_ = lean_ctor_get(v___x_2776_, 1);
v_ngen_2780_ = lean_ctor_get(v___x_2776_, 2);
v_auxDeclNGen_2781_ = lean_ctor_get(v___x_2776_, 3);
v_cache_2782_ = lean_ctor_get(v___x_2776_, 5);
v_recordedDeps_2783_ = lean_ctor_get(v___x_2776_, 6);
v_messages_2784_ = lean_ctor_get(v___x_2776_, 7);
v_infoState_2785_ = lean_ctor_get(v___x_2776_, 8);
v_snapshotTasks_2786_ = lean_ctor_get(v___x_2776_, 9);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2788_ = v___x_2776_;
v_isShared_2789_ = v_isSharedCheck_2816_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_snapshotTasks_2786_);
lean_inc(v_infoState_2785_);
lean_inc(v_messages_2784_);
lean_inc(v_recordedDeps_2783_);
lean_inc(v_cache_2782_);
lean_inc(v_traceState_2777_);
lean_inc(v_auxDeclNGen_2781_);
lean_inc(v_ngen_2780_);
lean_inc(v_nextMacroScope_2779_);
lean_inc(v_env_2778_);
lean_dec(v___x_2776_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2816_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
uint64_t v_tid_2790_; lean_object* v_traces_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2815_; 
v_tid_2790_ = lean_ctor_get_uint64(v_traceState_2777_, sizeof(void*)*1);
v_traces_2791_ = lean_ctor_get(v_traceState_2777_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_traceState_2777_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2793_ = v_traceState_2777_;
v_isShared_2794_ = v_isSharedCheck_2815_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_traces_2791_);
lean_dec(v_traceState_2777_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2815_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; double v___x_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2798_ = 0;
v___x_2799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2800_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2800_, 0, v_cls_2763_);
lean_ctor_set(v___x_2800_, 1, v___x_2796_);
lean_ctor_set(v___x_2800_, 2, v___x_2799_);
lean_ctor_set_float(v___x_2800_, sizeof(void*)*3, v___x_2797_);
lean_ctor_set_float(v___x_2800_, sizeof(void*)*3 + 8, v___x_2797_);
lean_ctor_set_uint8(v___x_2800_, sizeof(void*)*3 + 16, v___x_2798_);
v___x_2801_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2802_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v_a_2772_);
lean_ctor_set(v___x_2802_, 2, v___x_2801_);
lean_inc(v_ref_2770_);
v___x_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2803_, 0, v_ref_2770_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = l_Lean_PersistentArray_push___redArg(v_traces_2791_, v___x_2803_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2804_);
v___x_2806_ = v___x_2793_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2804_);
lean_ctor_set_uint64(v_reuseFailAlloc_2814_, sizeof(void*)*1, v_tid_2790_);
v___x_2806_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2808_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 4, v___x_2806_);
v___x_2808_ = v___x_2788_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_env_2778_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_nextMacroScope_2779_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_ngen_2780_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_auxDeclNGen_2781_);
lean_ctor_set(v_reuseFailAlloc_2813_, 4, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2813_, 5, v_cache_2782_);
lean_ctor_set(v_reuseFailAlloc_2813_, 6, v_recordedDeps_2783_);
lean_ctor_set(v_reuseFailAlloc_2813_, 7, v_messages_2784_);
lean_ctor_set(v_reuseFailAlloc_2813_, 8, v_infoState_2785_);
lean_ctor_set(v_reuseFailAlloc_2813_, 9, v_snapshotTasks_2786_);
v___x_2808_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = lean_st_ref_put(v___y_2768_, v___x_2808_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2795_);
v___x_2811_ = v___x_2774_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2795_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2818_, lean_object* v_msg_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2818_, v_msg_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2825_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2828_ = l_Lean_stringToMessageData(v___x_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v___f_2829_, lean_object* v_term_2830_, lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___y_2839_; lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2830_, v___x_2831_, v___x_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v___f_2829_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v_fst_2865_; lean_object* v___x_2867_; 
v_fst_2865_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_fst_2865_);
lean_dec(v_a_2861_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v_fst_2865_);
v___x_2867_ = v___x_2863_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_fst_2865_);
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
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2907_; 
v_a_2870_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2872_ = v___x_2860_;
v_isShared_2873_ = v_isSharedCheck_2907_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2860_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2907_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
uint8_t v___x_2874_; 
v___x_2874_ = l_Lean_Exception_isInterrupt(v_a_2870_);
if (v___x_2874_ == 0)
{
uint8_t v___x_2875_; 
lean_inc(v_a_2870_);
v___x_2875_ = l_Lean_Exception_isRuntime(v_a_2870_);
if (v___x_2875_ == 0)
{
uint8_t v___x_2876_; 
lean_inc(v_a_2870_);
v___x_2876_ = l_Lean_Exception_isMaxRecDepth(v_a_2870_);
if (v___x_2876_ == 0)
{
lean_object* v_toCold_2877_; lean_object* v_options_2878_; uint8_t v_hasTrace_2879_; 
lean_del_object(v___x_2872_);
v_toCold_2877_ = lean_ctor_get(v___y_2835_, 0);
v_options_2878_ = lean_ctor_get(v_toCold_2877_, 2);
v_hasTrace_2879_ = lean_ctor_get_uint8(v_options_2878_, sizeof(void*)*1);
if (v_hasTrace_2879_ == 0)
{
lean_dec(v_a_2870_);
goto v___jp_2857_;
}
else
{
lean_object* v_inheritedTraceOptions_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v_inheritedTraceOptions_2880_ = lean_ctor_get(v_toCold_2877_, 11);
v___x_2881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2882_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2883_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2880_, v_options_2878_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_dec(v_a_2870_);
goto v___jp_2857_;
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2884_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2885_ = l_Lean_Exception_toMessageData(v_a_2870_);
v___x_2886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2884_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2881_, v___x_2886_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = lean_apply_6(v___f_2829_, v_a_2888_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, lean_box(0));
v___y_2839_ = v___x_2889_;
goto v___jp_2838_;
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v___f_2829_);
v_a_2890_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2887_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2887_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
}
else
{
lean_object* v___x_2899_; 
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v___f_2829_);
if (v_isShared_2873_ == 0)
{
v___x_2899_ = v___x_2872_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2870_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
else
{
lean_object* v___x_2902_; 
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v___f_2829_);
if (v_isShared_2873_ == 0)
{
v___x_2902_ = v___x_2872_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2870_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
lean_object* v___x_2905_; 
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec_ref(v___f_2829_);
if (v_isShared_2873_ == 0)
{
v___x_2905_ = v___x_2872_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2870_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
v___jp_2838_:
{
if (lean_obj_tag(v___y_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2848_; 
v_a_2840_ = lean_ctor_get(v___y_2839_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___y_2839_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2842_ = v___y_2839_;
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___y_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_a_2844_; lean_object* v___x_2846_; 
v_a_2844_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_a_2844_);
lean_dec(v_a_2840_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v_a_2844_);
v___x_2846_ = v___x_2842_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
v_a_2849_ = lean_ctor_get(v___y_2839_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___y_2839_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___y_2839_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___y_2839_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
v___jp_2857_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_apply_6(v___f_2829_, v___x_2858_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, lean_box(0));
v___y_2839_ = v___x_2859_;
goto v___jp_2838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v___f_2908_, lean_object* v_term_2909_, lean_object* v___x_2910_, lean_object* v___x_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v___f_2908_, v_term_2909_, v___x_2910_, v___x_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2918_, lean_object* v_vals_2919_, lean_object* v_i_2920_, lean_object* v_k_2921_){
_start:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = lean_array_get_size(v_keys_2918_);
v___x_2923_ = lean_nat_dec_lt(v_i_2920_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
lean_dec(v_i_2920_);
v___x_2924_ = lean_box(0);
return v___x_2924_;
}
else
{
lean_object* v_k_x27_2925_; uint8_t v___x_2926_; 
v_k_x27_2925_ = lean_array_fget_borrowed(v_keys_2918_, v_i_2920_);
v___x_2926_ = l_Lean_instBEqMVarId_beq(v_k_2921_, v_k_x27_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_unsigned_to_nat(1u);
v___x_2928_ = lean_nat_add(v_i_2920_, v___x_2927_);
lean_dec(v_i_2920_);
v_i_2920_ = v___x_2928_;
goto _start;
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_array_fget_borrowed(v_vals_2919_, v_i_2920_);
lean_dec(v_i_2920_);
lean_inc(v___x_2930_);
v___x_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2932_, lean_object* v_vals_2933_, lean_object* v_i_2934_, lean_object* v_k_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2932_, v_vals_2933_, v_i_2934_, v_k_2935_);
lean_dec(v_k_2935_);
lean_dec_ref(v_vals_2933_);
lean_dec_ref(v_keys_2932_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2937_, size_t v_x_2938_, lean_object* v_x_2939_){
_start:
{
if (lean_obj_tag(v_x_2937_) == 0)
{
lean_object* v_es_2940_; lean_object* v___x_2941_; size_t v___x_2942_; size_t v___x_2943_; lean_object* v_j_2944_; lean_object* v___x_2945_; 
v_es_2940_ = lean_ctor_get(v_x_2937_, 0);
v___x_2941_ = lean_box(2);
v___x_2942_ = ((size_t)31ULL);
v___x_2943_ = lean_usize_land(v_x_2938_, v___x_2942_);
v_j_2944_ = lean_usize_to_nat(v___x_2943_);
v___x_2945_ = lean_array_get_borrowed(v___x_2941_, v_es_2940_, v_j_2944_);
lean_dec(v_j_2944_);
switch(lean_obj_tag(v___x_2945_))
{
case 0:
{
lean_object* v_key_2946_; lean_object* v_val_2947_; uint8_t v___x_2948_; 
v_key_2946_ = lean_ctor_get(v___x_2945_, 0);
v_val_2947_ = lean_ctor_get(v___x_2945_, 1);
v___x_2948_ = l_Lean_instBEqMVarId_beq(v_x_2939_, v_key_2946_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_box(0);
return v___x_2949_;
}
else
{
lean_object* v___x_2950_; 
lean_inc(v_val_2947_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_val_2947_);
return v___x_2950_;
}
}
case 1:
{
lean_object* v_node_2951_; size_t v___x_2952_; size_t v___x_2953_; 
v_node_2951_ = lean_ctor_get(v___x_2945_, 0);
v___x_2952_ = ((size_t)5ULL);
v___x_2953_ = lean_usize_shift_right(v_x_2938_, v___x_2952_);
v_x_2937_ = v_node_2951_;
v_x_2938_ = v___x_2953_;
goto _start;
}
default: 
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_box(0);
return v___x_2955_;
}
}
}
else
{
lean_object* v_ks_2956_; lean_object* v_vs_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_ks_2956_ = lean_ctor_get(v_x_2937_, 0);
v_vs_2957_ = lean_ctor_get(v_x_2937_, 1);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2956_, v_vs_2957_, v___x_2958_, v_x_2939_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2960_, lean_object* v_x_2961_, lean_object* v_x_2962_){
_start:
{
size_t v_x_11605__boxed_2963_; lean_object* v_res_2964_; 
v_x_11605__boxed_2963_ = lean_unbox_usize(v_x_2961_);
lean_dec(v_x_2961_);
v_res_2964_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2960_, v_x_11605__boxed_2963_, v_x_2962_);
lean_dec(v_x_2962_);
lean_dec_ref(v_x_2960_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2965_, lean_object* v_x_2966_){
_start:
{
uint64_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = l_Lean_instHashableMVarId_hash(v_x_2966_);
v___x_2968_ = lean_uint64_to_usize(v___x_2967_);
v___x_2969_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2965_, v___x_2968_, v_x_2966_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2970_, lean_object* v_x_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2970_, v_x_2971_);
lean_dec(v_x_2971_);
lean_dec_ref(v_x_2970_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v_mctx_3002_; lean_object* v_env_3003_; lean_object* v_opts_3004_; lean_object* v_namingCtx_3005_; lean_object* v_goal_3006_; lean_object* v_decls_3007_; lean_object* v___x_3008_; 
v_mctx_3002_ = lean_ctor_get(v_c_2998_, 3);
lean_inc_ref(v_mctx_3002_);
v_env_3003_ = lean_ctor_get(v_c_2998_, 2);
lean_inc_ref(v_env_3003_);
v_opts_3004_ = lean_ctor_get(v_c_2998_, 4);
lean_inc_ref(v_opts_3004_);
v_namingCtx_3005_ = lean_ctor_get(v_c_2998_, 5);
lean_inc_ref(v_namingCtx_3005_);
v_goal_3006_ = lean_ctor_get(v_c_2998_, 6);
lean_inc(v_goal_3006_);
lean_dec_ref(v_c_2998_);
v_decls_3007_ = lean_ctor_get(v_mctx_3002_, 5);
v___x_3008_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3007_, v_goal_3006_);
if (lean_obj_tag(v___x_3008_) == 1)
{
lean_object* v_val_3009_; lean_object* v_lctx_3010_; lean_object* v___f_3011_; lean_object* v___f_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___f_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; lean_object* v___x_3020_; lean_object* v_term_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___f_3024_; lean_object* v___x_3025_; 
v_val_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_val_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v_lctx_3010_ = lean_ctor_get(v_val_3009_, 1);
lean_inc_ref(v_lctx_3010_);
lean_dec(v_val_3009_);
v___f_3011_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_3012_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_3013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_3014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_3015_ = lean_box(0);
lean_inc(v_goal_3006_);
v___x_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_goal_3006_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___f_3017_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3017_, 0, v___x_3016_);
lean_closure_set(v___f_3017_, 1, v___f_3011_);
lean_closure_set(v___f_3017_, 2, v___x_3014_);
lean_closure_set(v___f_3017_, 3, v___x_3013_);
v___x_3018_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_3018_, 0, lean_box(0));
lean_closure_set(v___x_3018_, 1, v_goal_3006_);
lean_closure_set(v___x_3018_, 2, v___f_3017_);
v___x_3019_ = 1;
v___x_3020_ = lean_box(v___x_3019_);
v_term_3021_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3021_, 0, v___x_3018_);
lean_closure_set(v_term_3021_, 1, v___x_3020_);
v___x_3022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3024_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3024_, 0, v___f_3012_);
lean_closure_set(v___f_3024_, 1, v_term_3021_);
lean_closure_set(v___f_3024_, 2, v___x_3022_);
lean_closure_set(v___f_3024_, 3, v___x_3023_);
v___x_3025_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3003_, v_mctx_3002_, v_lctx_3010_, v_opts_3004_, v_namingCtx_3005_, v___f_3024_, v_a_2999_, v_a_3000_);
return v___x_3025_;
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_dec(v___x_3008_);
lean_dec(v_goal_3006_);
lean_dec_ref(v_namingCtx_3005_);
lean_dec_ref(v_opts_3004_);
lean_dec_ref(v_env_3003_);
lean_dec_ref(v_mctx_3002_);
v___x_3026_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
return v___x_3027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3028_, v_a_3029_, v_a_3030_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3033_, lean_object* v_x_3034_, lean_object* v_x_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3034_, v_x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3037_, v_x_3038_, v_x_3039_);
lean_dec(v_x_3039_);
lean_dec_ref(v_x_3038_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3041_, lean_object* v_msg_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3041_, v_msg_3042_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3053_, lean_object* v_msg_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3053_, v_msg_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3065_, lean_object* v_x_3066_, size_t v_x_3067_, lean_object* v_x_3068_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3066_, v_x_3067_, v_x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3070_, lean_object* v_x_3071_, lean_object* v_x_3072_, lean_object* v_x_3073_){
_start:
{
size_t v_x_11862__boxed_3074_; lean_object* v_res_3075_; 
v_x_11862__boxed_3074_ = lean_unbox_usize(v_x_3072_);
lean_dec(v_x_3072_);
v_res_3075_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3070_, v_x_3071_, v_x_11862__boxed_3074_, v_x_3073_);
lean_dec(v_x_3073_);
lean_dec_ref(v_x_3071_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3076_, lean_object* v_keys_3077_, lean_object* v_vals_3078_, lean_object* v_heq_3079_, lean_object* v_i_3080_, lean_object* v_k_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3077_, v_vals_3078_, v_i_3080_, v_k_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3083_, lean_object* v_keys_3084_, lean_object* v_vals_3085_, lean_object* v_heq_3086_, lean_object* v_i_3087_, lean_object* v_k_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3083_, v_keys_3084_, v_vals_3085_, v_heq_3086_, v_i_3087_, v_k_3088_);
lean_dec(v_k_3088_);
lean_dec_ref(v_vals_3085_);
lean_dec_ref(v_keys_3084_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3092_, lean_object* v___x_3093_, lean_object* v_ref_3094_, lean_object* v_a_3095_, lean_object* v___x_3096_, lean_object* v___x_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
if (v___x_3092_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3093_);
v___x_3102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3103_ = lean_box(0);
v___x_3104_ = 4;
v___x_3105_ = l_Lean_MessageData_nil;
v___x_3106_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3094_, v_a_3095_, v___x_3101_, v___x_3102_, v___x_3103_, v___x_3104_, v___x_3105_, v___y_3098_, v___y_3099_);
return v___x_3106_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3107_ = lean_array_get(v___x_3096_, v_a_3095_, v___x_3097_);
lean_dec_ref(v_a_3095_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3093_);
v___x_3109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3110_ = lean_box(0);
v___x_3111_ = 4;
v___x_3112_ = l_Lean_MessageData_nil;
v___x_3113_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3094_, v___x_3107_, v___x_3108_, v___x_3109_, v___x_3110_, v___x_3111_, v___x_3112_, v___y_3098_, v___y_3099_);
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3114_, lean_object* v___x_3115_, lean_object* v_ref_3116_, lean_object* v_a_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
uint8_t v___x_3507__boxed_3123_; lean_object* v_res_3124_; 
v___x_3507__boxed_3123_ = lean_unbox(v___x_3114_);
v_res_3124_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3507__boxed_3123_, v___x_3115_, v_ref_3116_, v_a_3117_, v___x_3118_, v___x_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___x_3119_);
lean_dec_ref(v___x_3118_);
return v_res_3124_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3125_, lean_object* v_x_3126_){
_start:
{
if (lean_obj_tag(v_x_3126_) == 1)
{
lean_object* v_pre_3127_; 
v_pre_3127_ = lean_ctor_get(v_x_3126_, 0);
if (lean_obj_tag(v_pre_3127_) == 0)
{
lean_object* v_str_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v_str_3128_ = lean_ctor_get(v_x_3126_, 1);
v___x_3129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1));
v___x_3130_ = lean_string_dec_eq(v_str_3128_, v___x_3129_);
if (v___x_3130_ == 0)
{
return v___x_3130_;
}
else
{
return v_suppressElabErrors_3125_;
}
}
else
{
uint8_t v___x_3131_; 
v___x_3131_ = 0;
return v___x_3131_;
}
}
else
{
uint8_t v___x_3132_; 
v___x_3132_ = 0;
return v___x_3132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3133_, lean_object* v_x_3134_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3135_; uint8_t v_res_3136_; lean_object* v_r_3137_; 
v_suppressElabErrors_boxed_3135_ = lean_unbox(v_suppressElabErrors_3133_);
v_res_3136_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3135_, v_x_3134_);
lean_dec(v_x_3134_);
v_r_3137_ = lean_box(v_res_3136_);
return v_r_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3138_, lean_object* v_msgData_3139_, uint8_t v_severity_3140_, uint8_t v_isSilent_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
uint8_t v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; uint8_t v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3211_; uint8_t v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; uint8_t v___y_3237_; uint8_t v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; uint8_t v___y_3244_; uint8_t v___y_3245_; uint8_t v___x_3260_; uint8_t v___y_3262_; uint8_t v___x_3272_; 
v___x_3260_ = 2;
v___x_3272_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3140_, v___x_3260_);
if (v___x_3272_ == 0)
{
v___y_3262_ = v___x_3272_;
goto v___jp_3261_;
}
else
{
uint8_t v___x_3273_; 
lean_inc_ref(v_msgData_3139_);
v___x_3273_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3139_);
if (v___x_3273_ == 0)
{
v___y_3262_ = v___x_3273_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec_ref(v_msgData_3139_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
return v___x_3275_;
}
}
v___jp_3145_:
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lean_Elab_Command_getScope___redArg(v___y_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v_currNamespace_3156_; lean_object* v___x_3157_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v_currNamespace_3156_ = lean_ctor_get(v_a_3155_, 2);
lean_inc(v_currNamespace_3156_);
lean_dec(v_a_3155_);
v___x_3157_ = l_Lean_Elab_Command_getScope___redArg(v___y_3153_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3193_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3193_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3193_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_openDecls_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v_env_3167_; lean_object* v_messages_3168_; lean_object* v_scopes_3169_; lean_object* v_usedQuotCtxts_3170_; lean_object* v_nextMacroScope_3171_; lean_object* v_maxRecDepth_3172_; lean_object* v_ngen_3173_; lean_object* v_auxDeclNGen_3174_; lean_object* v_infoState_3175_; lean_object* v_traceState_3176_; lean_object* v_snapshotTasks_3177_; lean_object* v_prevLinterStates_3178_; lean_object* v_codeQualityEntryTasks_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3192_; 
v_openDecls_3162_ = lean_ctor_get(v_a_3158_, 3);
lean_inc(v_openDecls_3162_);
lean_dec(v_a_3158_);
v___x_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3163_, 0, v_currNamespace_3156_);
lean_ctor_set(v___x_3163_, 1, v_openDecls_3162_);
v___x_3164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___y_3150_);
lean_inc_ref(v___y_3152_);
lean_inc_ref(v___y_3148_);
v___x_3165_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3165_, 0, v___y_3148_);
lean_ctor_set(v___x_3165_, 1, v___y_3151_);
lean_ctor_set(v___x_3165_, 2, v___y_3147_);
lean_ctor_set(v___x_3165_, 3, v___y_3152_);
lean_ctor_set(v___x_3165_, 4, v___x_3164_);
lean_ctor_set_uint8(v___x_3165_, sizeof(void*)*5, v___y_3146_);
lean_ctor_set_uint8(v___x_3165_, sizeof(void*)*5 + 1, v___y_3149_);
lean_ctor_set_uint8(v___x_3165_, sizeof(void*)*5 + 2, v_isSilent_3141_);
v___x_3166_ = lean_st_ref_take(v___y_3153_);
v_env_3167_ = lean_ctor_get(v___x_3166_, 0);
v_messages_3168_ = lean_ctor_get(v___x_3166_, 1);
v_scopes_3169_ = lean_ctor_get(v___x_3166_, 2);
v_usedQuotCtxts_3170_ = lean_ctor_get(v___x_3166_, 3);
v_nextMacroScope_3171_ = lean_ctor_get(v___x_3166_, 4);
v_maxRecDepth_3172_ = lean_ctor_get(v___x_3166_, 5);
v_ngen_3173_ = lean_ctor_get(v___x_3166_, 6);
v_auxDeclNGen_3174_ = lean_ctor_get(v___x_3166_, 7);
v_infoState_3175_ = lean_ctor_get(v___x_3166_, 8);
v_traceState_3176_ = lean_ctor_get(v___x_3166_, 9);
v_snapshotTasks_3177_ = lean_ctor_get(v___x_3166_, 10);
v_prevLinterStates_3178_ = lean_ctor_get(v___x_3166_, 11);
v_codeQualityEntryTasks_3179_ = lean_ctor_get(v___x_3166_, 12);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3181_ = v___x_3166_;
v_isShared_3182_ = v_isSharedCheck_3192_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3179_);
lean_inc(v_prevLinterStates_3178_);
lean_inc(v_snapshotTasks_3177_);
lean_inc(v_traceState_3176_);
lean_inc(v_infoState_3175_);
lean_inc(v_auxDeclNGen_3174_);
lean_inc(v_ngen_3173_);
lean_inc(v_maxRecDepth_3172_);
lean_inc(v_nextMacroScope_3171_);
lean_inc(v_usedQuotCtxts_3170_);
lean_inc(v_scopes_3169_);
lean_inc(v_messages_3168_);
lean_inc(v_env_3167_);
lean_dec(v___x_3166_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3192_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3183_ = lean_box(0);
v___x_3184_ = l_Lean_MessageLog_add(v___x_3165_, v_messages_3168_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___x_3184_);
v___x_3186_ = v___x_3181_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_env_3167_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_scopes_3169_);
lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_usedQuotCtxts_3170_);
lean_ctor_set(v_reuseFailAlloc_3191_, 4, v_nextMacroScope_3171_);
lean_ctor_set(v_reuseFailAlloc_3191_, 5, v_maxRecDepth_3172_);
lean_ctor_set(v_reuseFailAlloc_3191_, 6, v_ngen_3173_);
lean_ctor_set(v_reuseFailAlloc_3191_, 7, v_auxDeclNGen_3174_);
lean_ctor_set(v_reuseFailAlloc_3191_, 8, v_infoState_3175_);
lean_ctor_set(v_reuseFailAlloc_3191_, 9, v_traceState_3176_);
lean_ctor_set(v_reuseFailAlloc_3191_, 10, v_snapshotTasks_3177_);
lean_ctor_set(v_reuseFailAlloc_3191_, 11, v_prevLinterStates_3178_);
lean_ctor_set(v_reuseFailAlloc_3191_, 12, v_codeQualityEntryTasks_3179_);
v___x_3186_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3187_ = lean_st_ref_put(v___y_3153_, v___x_3186_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3183_);
v___x_3189_ = v___x_3160_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3183_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v_currNamespace_3156_);
lean_dec_ref(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3147_);
v_a_3194_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3157_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3157_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3147_);
v_a_3202_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3154_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3154_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
v___jp_3210_:
{
lean_object* v_fileName_3215_; lean_object* v_fileMap_3216_; uint8_t v_suppressElabErrors_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3235_; 
v_fileName_3215_ = lean_ctor_get(v___y_3142_, 0);
v_fileMap_3216_ = lean_ctor_get(v___y_3142_, 1);
v_suppressElabErrors_3217_ = lean_ctor_get_uint8(v___y_3142_, sizeof(void*)*10);
v___x_3218_ = lean_box(v_suppressElabErrors_3217_);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3219_, 0, v___x_3218_);
v___x_3220_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3139_);
v___x_3221_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v___x_3220_, v___y_3143_);
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3235_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3235_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_inc_ref_n(v_fileMap_3216_, 2);
v___x_3226_ = l_Lean_FileMap_toPosition(v_fileMap_3216_, v___y_3213_);
lean_dec(v___y_3213_);
v___x_3227_ = l_Lean_FileMap_toPosition(v_fileMap_3216_, v___y_3214_);
lean_dec(v___y_3214_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
v___x_3229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3217_ == 0)
{
lean_del_object(v___x_3224_);
lean_dec_ref(v___f_3219_);
v___y_3146_ = v___y_3211_;
v___y_3147_ = v___x_3228_;
v___y_3148_ = v_fileName_3215_;
v___y_3149_ = v___y_3212_;
v___y_3150_ = v_a_3222_;
v___y_3151_ = v___x_3226_;
v___y_3152_ = v___x_3229_;
v___y_3153_ = v___y_3143_;
goto v___jp_3145_;
}
else
{
uint8_t v___x_3230_; 
lean_inc(v_a_3222_);
v___x_3230_ = l_Lean_MessageData_hasTag(v___f_3219_, v_a_3222_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
lean_dec_ref_known(v___x_3228_, 1);
lean_dec_ref(v___x_3226_);
lean_dec(v_a_3222_);
v___x_3231_ = lean_box(0);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3231_);
v___x_3233_ = v___x_3224_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
else
{
lean_del_object(v___x_3224_);
v___y_3146_ = v___y_3211_;
v___y_3147_ = v___x_3228_;
v___y_3148_ = v_fileName_3215_;
v___y_3149_ = v___y_3212_;
v___y_3150_ = v_a_3222_;
v___y_3151_ = v___x_3226_;
v___y_3152_ = v___x_3229_;
v___y_3153_ = v___y_3143_;
goto v___jp_3145_;
}
}
}
}
v___jp_3236_:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Syntax_getTailPos_x3f(v___y_3239_, v___y_3237_);
lean_dec(v___y_3239_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_inc(v___y_3240_);
v___y_3211_ = v___y_3237_;
v___y_3212_ = v___y_3238_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3240_;
goto v___jp_3210_;
}
else
{
lean_object* v_val_3242_; 
v_val_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_val_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v___y_3211_ = v___y_3237_;
v___y_3212_ = v___y_3238_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v_val_3242_;
goto v___jp_3210_;
}
}
v___jp_3243_:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Elab_Command_getRef___redArg(v___y_3142_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v_ref_3248_; lean_object* v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v_ref_3248_ = l_Lean_replaceRef(v_ref_3138_, v_a_3247_);
lean_dec(v_a_3247_);
v___x_3249_ = l_Lean_Syntax_getPos_x3f(v_ref_3248_, v___y_3244_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_unsigned_to_nat(0u);
v___y_3237_ = v___y_3244_;
v___y_3238_ = v___y_3245_;
v___y_3239_ = v_ref_3248_;
v___y_3240_ = v___x_3250_;
goto v___jp_3236_;
}
else
{
lean_object* v_val_3251_; 
v_val_3251_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_val_3251_);
lean_dec_ref_known(v___x_3249_, 1);
v___y_3237_ = v___y_3244_;
v___y_3238_ = v___y_3245_;
v___y_3239_ = v_ref_3248_;
v___y_3240_ = v_val_3251_;
goto v___jp_3236_;
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v_msgData_3139_);
v_a_3252_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3246_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3246_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
v___jp_3261_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v_scopes_3265_; lean_object* v___x_3266_; lean_object* v_opts_3267_; uint8_t v___x_3268_; uint8_t v___x_3269_; 
v___x_3263_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3264_ = lean_st_ref_get(v___y_3143_);
v_scopes_3265_ = lean_ctor_get(v___x_3264_, 2);
lean_inc(v_scopes_3265_);
lean_dec(v___x_3264_);
v___x_3266_ = l_List_head_x21___redArg(v___x_3263_, v_scopes_3265_);
lean_dec(v_scopes_3265_);
v_opts_3267_ = lean_ctor_get(v___x_3266_, 1);
lean_inc_ref(v_opts_3267_);
lean_dec(v___x_3266_);
v___x_3268_ = 1;
v___x_3269_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3140_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_dec_ref(v_opts_3267_);
v___y_3244_ = v___y_3262_;
v___y_3245_ = v_severity_3140_;
goto v___jp_3243_;
}
else
{
lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = l_Lean_warningAsError;
v___x_3271_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3267_, v___x_3270_);
lean_dec_ref(v_opts_3267_);
if (v___x_3271_ == 0)
{
v___y_3244_ = v___y_3262_;
v___y_3245_ = v_severity_3140_;
goto v___jp_3243_;
}
else
{
v___y_3244_ = v___y_3262_;
v___y_3245_ = v___x_3260_;
goto v___jp_3243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3276_, lean_object* v_msgData_3277_, lean_object* v_severity_3278_, lean_object* v_isSilent_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
uint8_t v_severity_boxed_3283_; uint8_t v_isSilent_boxed_3284_; lean_object* v_res_3285_; 
v_severity_boxed_3283_ = lean_unbox(v_severity_3278_);
v_isSilent_boxed_3284_ = lean_unbox(v_isSilent_3279_);
v_res_3285_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3276_, v_msgData_3277_, v_severity_boxed_3283_, v_isSilent_boxed_3284_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v_ref_3276_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3286_, lean_object* v_msgData_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
uint8_t v___x_3291_; uint8_t v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = 0;
v___x_3292_ = 0;
v___x_3293_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3286_, v_msgData_3287_, v___x_3291_, v___x_3292_, v___y_3288_, v___y_3289_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3294_, lean_object* v_msgData_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3294_, v_msgData_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v_ref_3294_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3304_ = lean_string_append(v___x_3303_, v___x_3301_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3305_, v_x_3306_);
lean_dec_ref(v_x_3306_);
lean_dec_ref(v___x_3305_);
return v_res_3307_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3317_, uint8_t v___x_3318_, lean_object* v___x_3319_, lean_object* v_insertPos_3320_, lean_object* v_cmdLine_3321_, lean_object* v_ref_3322_, size_t v_sz_3323_, size_t v_i_3324_, lean_object* v_bs_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_usize_dec_lt(v_i_3324_, v_sz_3323_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3317_);
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_bs_3325_);
return v___x_3330_;
}
else
{
lean_object* v_v_3331_; lean_object* v___x_3332_; lean_object* v_bs_x27_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_v_3331_ = lean_array_uget(v_bs_3325_, v_i_3324_);
v___x_3332_ = lean_unsigned_to_nat(0u);
v_bs_x27_3333_ = lean_array_uset(v_bs_3325_, v_i_3324_, v___x_3332_);
lean_inc(v_v_3331_);
v___x_3334_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3334_, 0, v_v_3331_);
v___x_3335_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3334_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___f_3339_; lean_object* v___x_3340_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = l_Std_Format_defWidth;
v___x_3338_ = l_Std_Format_pretty(v_a_3336_, v___x_3337_, v___x_3332_, v___x_3332_);
lean_inc_ref(v___x_3338_);
v___f_3339_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3339_, 0, v___x_3338_);
lean_inc_ref(v___x_3317_);
v___x_3340_ = lean_string_append(v___x_3317_, v___x_3338_);
lean_dec_ref(v___x_3338_);
if (v___x_3318_ == 0)
{
goto v___jp_3341_;
}
else
{
lean_object* v___x_3352_; lean_object* v_line_3353_; lean_object* v_column_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3389_; 
lean_inc_ref(v___x_3319_);
v___x_3352_ = l_Lean_FileMap_toPosition(v___x_3319_, v_insertPos_3320_);
v_line_3353_ = lean_ctor_get(v___x_3352_, 0);
v_column_3354_ = lean_ctor_get(v___x_3352_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3356_ = v___x_3352_;
v_isShared_3357_ = v_isSharedCheck_3389_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_column_3354_);
lean_inc(v_line_3353_);
lean_dec(v___x_3352_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3389_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3358_ = lean_nat_sub(v_line_3353_, v_cmdLine_3321_);
lean_dec(v_line_3353_);
v___x_3359_ = lean_unsigned_to_nat(1u);
v___x_3360_ = lean_nat_add(v___x_3358_, v___x_3359_);
lean_dec(v___x_3358_);
v___x_3361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3340_);
v___x_3362_ = l_String_quote(v___x_3340_);
v___x_3363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
v___x_3364_ = l_Lean_MessageData_ofFormat(v___x_3363_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set_tag(v___x_3356_, 7);
lean_ctor_set(v___x_3356_, 1, v___x_3364_);
lean_ctor_set(v___x_3356_, 0, v___x_3361_);
v___x_3366_ = v___x_3356_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3366_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = l_Nat_reprFast(v___x_3360_);
v___x_3370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
v___x_3371_ = l_Lean_MessageData_ofFormat(v___x_3370_);
v___x_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3368_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Nat_reprFast(v_column_3354_);
v___x_3376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
v___x_3377_ = l_Lean_MessageData_ofFormat(v___x_3376_);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3374_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3322_, v___x_3378_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_dec_ref_known(v___x_3379_, 1);
goto v___jp_3341_;
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref(v___x_3340_);
lean_dec_ref(v___f_3339_);
lean_dec_ref(v_bs_x27_3333_);
lean_dec(v_v_3331_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3317_);
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
}
v___jp_3341_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; size_t v___x_3348_; size_t v___x_3349_; lean_object* v___x_3350_; 
v___x_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
v___x_3343_ = lean_box(0);
v___x_3344_ = l_Lean_MessageData_ofSyntax(v_v_3331_);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
v___x_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3346_, 0, v___f_3339_);
v___x_3347_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3342_);
lean_ctor_set(v___x_3347_, 1, v___x_3343_);
lean_ctor_set(v___x_3347_, 2, v___x_3343_);
lean_ctor_set(v___x_3347_, 3, v___x_3343_);
lean_ctor_set(v___x_3347_, 4, v___x_3345_);
lean_ctor_set(v___x_3347_, 5, v___x_3346_);
v___x_3348_ = ((size_t)1ULL);
v___x_3349_ = lean_usize_add(v_i_3324_, v___x_3348_);
v___x_3350_ = lean_array_uset(v_bs_x27_3333_, v_i_3324_, v___x_3347_);
v_i_3324_ = v___x_3349_;
v_bs_3325_ = v___x_3350_;
goto _start;
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec_ref(v_bs_x27_3333_);
lean_dec(v_v_3331_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3317_);
v_a_3390_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3335_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3335_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3398_, lean_object* v___x_3399_, lean_object* v___x_3400_, lean_object* v_insertPos_3401_, lean_object* v_cmdLine_3402_, lean_object* v_ref_3403_, lean_object* v_sz_3404_, lean_object* v_i_3405_, lean_object* v_bs_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
uint8_t v___x_3853__boxed_3410_; size_t v_sz_boxed_3411_; size_t v_i_boxed_3412_; lean_object* v_res_3413_; 
v___x_3853__boxed_3410_ = lean_unbox(v___x_3399_);
v_sz_boxed_3411_ = lean_unbox_usize(v_sz_3404_);
lean_dec(v_sz_3404_);
v_i_boxed_3412_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_res_3413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3398_, v___x_3853__boxed_3410_, v___x_3400_, v_insertPos_3401_, v_cmdLine_3402_, v_ref_3403_, v_sz_boxed_3411_, v_i_boxed_3412_, v_bs_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v_ref_3403_);
lean_dec(v_cmdLine_3402_);
lean_dec(v_insertPos_3401_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3414_, lean_object* v_ref_3415_, lean_object* v_insertPos_3416_, lean_object* v_suggs_3417_, lean_object* v_cmdLine_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3422_ = lean_array_get_size(v_suggs_3417_);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_nat_dec_eq(v___x_3422_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v_fileMap_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v_scopes_3431_; lean_object* v___x_3432_; lean_object* v_opts_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; size_t v_sz_3436_; size_t v___x_3437_; lean_object* v___x_3438_; 
v_fileMap_3425_ = lean_ctor_get(v_a_3419_, 1);
v___x_3426_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_inc_ref_n(v_fileMap_3425_, 2);
v___x_3427_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3414_, v_fileMap_3425_);
lean_inc(v_insertPos_3416_);
v___x_3428_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3416_);
v___x_3429_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3430_ = lean_st_ref_get(v_a_3420_);
v_scopes_3431_ = lean_ctor_get(v___x_3430_, 2);
lean_inc(v_scopes_3431_);
lean_dec(v___x_3430_);
v___x_3432_ = l_List_head_x21___redArg(v___x_3429_, v_scopes_3431_);
lean_dec(v_scopes_3431_);
v_opts_3433_ = lean_ctor_get(v___x_3432_, 1);
lean_inc_ref(v_opts_3433_);
lean_dec(v___x_3432_);
v___x_3434_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3435_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3433_, v___x_3434_);
lean_dec_ref(v_opts_3433_);
v_sz_3436_ = lean_array_size(v_suggs_3417_);
v___x_3437_ = ((size_t)0ULL);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3427_, v___x_3435_, v_fileMap_3425_, v_insertPos_3416_, v_cmdLine_3418_, v_ref_3415_, v_sz_3436_, v___x_3437_, v_suggs_3417_, v_a_3419_, v_a_3420_);
lean_dec(v_insertPos_3416_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___y_3444_; lean_object* v___x_3445_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v___x_3440_ = lean_array_get_size(v_a_3439_);
v___x_3441_ = lean_unsigned_to_nat(1u);
v___x_3442_ = lean_nat_dec_eq(v___x_3440_, v___x_3441_);
v___x_3443_ = lean_box(v___x_3442_);
v___y_3444_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3444_, 0, v___x_3443_);
lean_closure_set(v___y_3444_, 1, v___x_3428_);
lean_closure_set(v___y_3444_, 2, v_ref_3415_);
lean_closure_set(v___y_3444_, 3, v_a_3439_);
lean_closure_set(v___y_3444_, 4, v___x_3426_);
lean_closure_set(v___y_3444_, 5, v___x_3423_);
v___x_3445_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3444_, v_a_3419_, v_a_3420_);
return v___x_3445_;
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v___x_3428_);
lean_dec(v_ref_3415_);
v_a_3446_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3438_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3438_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec_ref(v_suggs_3417_);
lean_dec(v_insertPos_3416_);
lean_dec(v_ref_3415_);
v___x_3454_ = lean_box(0);
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
return v___x_3455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3456_, lean_object* v_ref_3457_, lean_object* v_insertPos_3458_, lean_object* v_suggs_3459_, lean_object* v_cmdLine_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3456_, v_ref_3457_, v_insertPos_3458_, v_suggs_3459_, v_cmdLine_3460_, v_a_3461_, v_a_3462_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_cmdLine_3460_);
lean_dec(v_tacticSeq_3456_);
return v_res_3464_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3465_){
_start:
{
uint8_t v___x_3466_; 
v___x_3466_ = 0;
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3467_){
_start:
{
uint8_t v_res_3468_; lean_object* v_r_3469_; 
v_res_3468_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3467_);
lean_dec(v_x_3467_);
v_r_3469_ = lean_box(v_res_3468_);
return v_r_3469_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Array_mkArray0___redArg();
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3490_, lean_object* v_ref_3491_, lean_object* v_goal_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_toCold_3501_; lean_object* v_currRecDepth_3502_; lean_object* v_ref_3503_; uint16_t v_optionFlags_3504_; uint8_t v_suppressElabErrors_3505_; uint8_t v_checkDeprecated_3506_; uint8_t v_isRecordingDeps_3507_; uint8_t v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_ref_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v_toCold_3501_ = lean_ctor_get(v___y_3495_, 0);
v_currRecDepth_3502_ = lean_ctor_get(v___y_3495_, 1);
v_ref_3503_ = lean_ctor_get(v___y_3495_, 2);
v_optionFlags_3504_ = lean_ctor_get_uint16(v___y_3495_, sizeof(void*)*3);
v_suppressElabErrors_3505_ = lean_ctor_get_uint8(v___y_3495_, sizeof(void*)*3 + 2);
v_checkDeprecated_3506_ = lean_ctor_get_uint8(v___y_3495_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3507_ = lean_ctor_get_uint8(v___y_3495_, sizeof(void*)*3 + 4);
v___x_3508_ = 0;
v___x_3509_ = l_Lean_SourceInfo_fromRef(v_ref_3503_, v___x_3508_);
v___x_3510_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0));
lean_inc_n(v___x_3509_, 3);
v___x_3511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3509_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
v___x_3513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3514_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5);
v___x_3515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3509_);
lean_ctor_set(v___x_3515_, 1, v___x_3513_);
lean_ctor_set(v___x_3515_, 2, v___x_3514_);
v___x_3516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7));
v___x_3517_ = l_Lean_Syntax_node1(v___x_3509_, v___x_3516_, v___x_3515_);
v___x_3518_ = l_Lean_Syntax_node2(v___x_3509_, v___x_3512_, v___x_3511_, v___x_3517_);
v___x_3519_ = lean_box(0);
v___x_3520_ = lean_box(0);
v___x_3521_ = 1;
v___x_3522_ = lean_box(1);
v___x_3523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3524_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_3524_, 0, v___x_3519_);
lean_ctor_set(v___x_3524_, 1, v___x_3520_);
lean_ctor_set(v___x_3524_, 2, v___x_3519_);
lean_ctor_set(v___x_3524_, 3, v___f_3490_);
lean_ctor_set(v___x_3524_, 4, v___x_3522_);
lean_ctor_set(v___x_3524_, 5, v___x_3522_);
lean_ctor_set(v___x_3524_, 6, v___x_3519_);
lean_ctor_set(v___x_3524_, 7, v___x_3523_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8, v___x_3521_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 1, v___x_3521_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 2, v___x_3521_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 3, v___x_3521_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 4, v___x_3508_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 5, v___x_3508_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 6, v___x_3508_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 7, v___x_3508_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 8, v___x_3521_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*8 + 9, v___x_3508_);
v___x_3525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v___x_3526_ = lean_box(0);
v_ref_3527_ = l_Lean_replaceRef(v_ref_3491_, v_ref_3503_);
lean_inc(v_currRecDepth_3502_);
lean_inc_ref(v_toCold_3501_);
v___x_3528_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3528_, 0, v_toCold_3501_);
lean_ctor_set(v___x_3528_, 1, v_currRecDepth_3502_);
lean_ctor_set(v___x_3528_, 2, v_ref_3527_);
lean_ctor_set_uint16(v___x_3528_, sizeof(void*)*3, v_optionFlags_3504_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*3 + 2, v_suppressElabErrors_3505_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*3 + 3, v_checkDeprecated_3506_);
lean_ctor_set_uint8(v___x_3528_, sizeof(void*)*3 + 4, v_isRecordingDeps_3507_);
v___x_3529_ = l_Lean_Elab_runTactic(v_goal_3492_, v___x_3518_, v___x_3524_, v___x_3525_, v___y_3493_, v___y_3494_, v___x_3528_, v___y_3496_);
lean_dec_ref_known(v___x_3528_, 3);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; 
v_unused_3537_ = lean_ctor_get(v___x_3529_, 0);
lean_dec(v_unused_3537_);
v___x_3531_ = v___x_3529_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_dec(v___x_3529_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3526_);
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3526_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3558_; 
v_a_3538_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3540_ = v___x_3529_;
v_isShared_3541_ = v_isSharedCheck_3558_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3529_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3558_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
lean_inc(v_a_3538_);
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
uint8_t v___x_3544_; 
v___x_3544_ = l_Lean_Exception_isInterrupt(v_a_3538_);
if (v___x_3544_ == 0)
{
uint8_t v___x_3545_; 
lean_inc(v_a_3538_);
v___x_3545_ = l_Lean_Exception_isRuntime(v_a_3538_);
if (v___x_3545_ == 0)
{
uint8_t v___x_3546_; 
lean_inc(v_a_3538_);
v___x_3546_ = l_Lean_Exception_isMaxRecDepth(v_a_3538_);
if (v___x_3546_ == 0)
{
lean_object* v_options_3547_; uint8_t v_hasTrace_3548_; 
lean_dec_ref(v___x_3543_);
v_options_3547_ = lean_ctor_get(v_toCold_3501_, 2);
v_hasTrace_3548_ = lean_ctor_get_uint8(v_options_3547_, sizeof(void*)*1);
if (v_hasTrace_3548_ == 0)
{
lean_dec(v_a_3538_);
goto v___jp_3498_;
}
else
{
lean_object* v_inheritedTraceOptions_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v_inheritedTraceOptions_3549_ = lean_ctor_get(v_toCold_3501_, 11);
v___x_3550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3551_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3552_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3549_, v_options_3547_, v___x_3551_);
if (v___x_3552_ == 0)
{
lean_dec(v_a_3538_);
goto v___jp_3498_;
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3553_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3554_ = l_Lean_Exception_toMessageData(v_a_3538_);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3553_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3550_, v___x_3555_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
return v___x_3556_;
}
}
}
else
{
lean_dec(v_a_3538_);
return v___x_3543_;
}
}
else
{
lean_dec(v_a_3538_);
return v___x_3543_;
}
}
else
{
lean_dec(v_a_3538_);
return v___x_3543_;
}
}
}
}
v___jp_3498_:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_box(0);
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
return v___x_3500_;
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
uint8_t v___x_3602_; 
v___x_3602_ = lean_usize_dec_eq(v_i_3596_, v_stop_3597_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; lean_object* v_pos_3604_; uint8_t v_severity_3605_; lean_object* v_data_3606_; lean_object* v___f_3607_; uint8_t v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; uint8_t v___y_3612_; 
v___x_3603_ = lean_array_uget_borrowed(v_as_3595_, v_i_3596_);
v_pos_3604_ = lean_ctor_get(v___x_3603_, 1);
v_severity_3605_ = lean_ctor_get_uint8(v___x_3603_, sizeof(void*)*5 + 1);
v_data_3606_ = lean_ctor_get(v___x_3603_, 4);
v___f_3607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
v___x_3608_ = 1;
lean_inc_ref(v_pos_3604_);
v___x_3609_ = l_Lean_FileMap_ofPosition(v___x_3593_, v_pos_3604_);
v___x_3610_ = l_Lean_Syntax_Range_contains(v_val_3594_, v___x_3609_, v___x_3608_);
lean_dec(v___x_3609_);
if (v_severity_3605_ == 2)
{
v___y_3612_ = v___x_3608_;
goto v___jp_3611_;
}
else
{
v___y_3612_ = v___x_3602_;
goto v___jp_3611_;
}
v___jp_3611_:
{
if (v___x_3610_ == 0)
{
goto v___jp_3598_;
}
else
{
if (v___y_3612_ == 0)
{
goto v___jp_3598_;
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
goto v___jp_3598_;
}
}
}
}
}
else
{
uint8_t v___x_3614_; 
v___x_3614_ = 0;
return v___x_3614_;
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
size_t v___x_3631_; size_t v___x_3632_; uint8_t v___x_3633_; 
v___x_3631_ = ((size_t)0ULL);
v___x_3632_ = lean_usize_of_nat(v___x_3629_);
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3624_, v_val_3625_, v_cs_3627_, v___x_3631_, v___x_3632_);
return v___x_3633_;
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
size_t v___x_3638_; size_t v___x_3639_; uint8_t v___x_3640_; 
v___x_3638_ = ((size_t)0ULL);
v___x_3639_ = lean_usize_of_nat(v___x_3636_);
v___x_3640_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3624_, v_val_3625_, v_vs_3634_, v___x_3638_, v___x_3639_);
return v___x_3640_;
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
size_t v___x_3676_; size_t v___x_3677_; uint8_t v___x_3678_; 
v___x_3676_ = ((size_t)0ULL);
v___x_3677_ = lean_usize_of_nat(v___x_3674_);
v___x_3678_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3667_, v_val_3668_, v_tail_3671_, v___x_3676_, v___x_3677_);
return v___x_3678_;
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
lean_object* v_fileMap_3694_; lean_object* v___x_3695_; lean_object* v_messages_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
v_fileMap_3694_ = lean_ctor_get(v_a_3685_, 1);
v___x_3695_ = lean_st_ref_get(v_a_3686_);
v_messages_3696_ = lean_ctor_get(v___x_3695_, 1);
lean_inc_ref(v_messages_3696_);
lean_dec(v___x_3695_);
v___x_3697_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3696_);
v___x_3698_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3694_, v_val_3690_, v___x_3697_);
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
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v_scopes_3793_; lean_object* v___x_3794_; lean_object* v_opts_3795_; uint8_t v_hasTrace_3796_; 
v___x_3788_ = l_Lean_inheritedTraceOptions;
v___x_3789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3790_ = lean_st_ref_get(v___x_3788_);
v___x_3791_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3792_ = lean_st_ref_get(v___y_3776_);
v_scopes_3793_ = lean_ctor_get(v___x_3792_, 2);
lean_inc(v_scopes_3793_);
lean_dec(v___x_3792_);
v___x_3794_ = l_List_head_x21___redArg(v___x_3791_, v_scopes_3793_);
lean_dec(v_scopes_3793_);
v_opts_3795_ = lean_ctor_get(v___x_3794_, 1);
lean_inc_ref(v_opts_3795_);
lean_dec(v___x_3794_);
v_hasTrace_3796_ = lean_ctor_get_uint8(v_opts_3795_, sizeof(void*)*1);
if (v_hasTrace_3796_ == 0)
{
lean_dec_ref(v_opts_3795_);
lean_dec(v___x_3790_);
v_a_3779_ = v___x_3785_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3797_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3790_, v_opts_3795_, v___x_3797_);
lean_dec_ref(v_opts_3795_);
lean_dec(v___x_3790_);
if (v___x_3798_ == 0)
{
v_a_3779_ = v___x_3785_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3800_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3789_, v___x_3799_, v___y_3775_, v___y_3776_);
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
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v_a_3853_; lean_object* v___x_3854_; 
lean_dec_ref(v_b_3844_);
v___x_3850_ = lean_box(0);
v___x_3851_ = l_Lean_inheritedTraceOptions;
v___x_3852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3853_ = lean_array_uget_borrowed(v_as_3841_, v_i_3843_);
lean_inc(v_a_3853_);
lean_inc(v_stx_3836_);
v___x_3854_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3836_, v___x_3837_, v_a_3853_, v___x_3838_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v_scopes_3877_; lean_object* v___x_3878_; lean_object* v_opts_3879_; uint8_t v_hasTrace_3880_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3874_ = lean_st_ref_get(v___x_3851_);
v___x_3875_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3876_ = lean_st_ref_get(v___y_3846_);
v_scopes_3877_ = lean_ctor_get(v___x_3876_, 2);
lean_inc(v_scopes_3877_);
lean_dec(v___x_3876_);
v___x_3878_ = l_List_head_x21___redArg(v___x_3875_, v_scopes_3877_);
lean_dec(v_scopes_3877_);
v_opts_3879_ = lean_ctor_get(v___x_3878_, 1);
lean_inc_ref(v_opts_3879_);
lean_dec(v___x_3878_);
v_hasTrace_3880_ = lean_ctor_get_uint8(v_opts_3879_, sizeof(void*)*1);
if (v_hasTrace_3880_ == 0)
{
lean_dec_ref(v_opts_3879_);
lean_dec(v___x_3874_);
v___y_3857_ = v___y_3845_;
v___y_3858_ = v___y_3846_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3882_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3874_, v_opts_3879_, v___x_3881_);
lean_dec_ref(v_opts_3879_);
lean_dec(v___x_3874_);
if (v___x_3882_ == 0)
{
v___y_3857_ = v___y_3845_;
v___y_3858_ = v___y_3846_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3884_ = lean_array_get_size(v_a_3855_);
v___x_3885_ = l_Nat_reprFast(v___x_3884_);
v___x_3886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
v___x_3887_ = l_Lean_MessageData_ofFormat(v___x_3886_);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3883_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3852_, v___x_3888_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_dec_ref_known(v___x_3889_, 1);
v___y_3857_ = v___y_3845_;
v___y_3858_ = v___y_3846_;
goto v___jp_3856_;
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec(v_a_3855_);
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
v___jp_3856_:
{
size_t v_sz_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
v_sz_3859_ = lean_array_size(v_a_3855_);
v___x_3860_ = ((size_t)0ULL);
lean_inc_ref(v___x_3839_);
lean_inc(v_a_3853_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3853_, v___x_3839_, v___x_3840_, v_a_3855_, v_sz_3859_, v___x_3860_, v___x_3850_, v___y_3857_, v___y_3858_);
lean_dec(v_a_3855_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v___x_3862_; size_t v___x_3863_; size_t v___x_3864_; 
lean_dec_ref_known(v___x_3861_, 1);
v___x_3862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3863_ = ((size_t)1ULL);
v___x_3864_ = lean_usize_add(v_i_3843_, v___x_3863_);
v_i_3843_ = v___x_3864_;
v_b_3844_ = v___x_3862_;
goto _start;
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec_ref(v___x_3839_);
lean_dec(v_stx_3836_);
v_a_3866_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3861_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3861_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
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
v_a_3898_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3854_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3854_);
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
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v_a_3938_; lean_object* v___x_3939_; 
lean_dec_ref(v_b_3929_);
v___x_3935_ = lean_box(0);
v___x_3936_ = l_Lean_inheritedTraceOptions;
v___x_3937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3938_ = lean_array_uget_borrowed(v_as_3926_, v_i_3928_);
lean_inc(v_a_3938_);
lean_inc(v_stx_3921_);
v___x_3939_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3921_, v___x_3922_, v_a_3938_, v___x_3923_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v_scopes_3962_; lean_object* v___x_3963_; lean_object* v_opts_3964_; uint8_t v_hasTrace_3965_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v___x_3959_ = lean_st_ref_get(v___x_3936_);
v___x_3960_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3961_ = lean_st_ref_get(v___y_3931_);
v_scopes_3962_ = lean_ctor_get(v___x_3961_, 2);
lean_inc(v_scopes_3962_);
lean_dec(v___x_3961_);
v___x_3963_ = l_List_head_x21___redArg(v___x_3960_, v_scopes_3962_);
lean_dec(v_scopes_3962_);
v_opts_3964_ = lean_ctor_get(v___x_3963_, 1);
lean_inc_ref(v_opts_3964_);
lean_dec(v___x_3963_);
v_hasTrace_3965_ = lean_ctor_get_uint8(v_opts_3964_, sizeof(void*)*1);
if (v_hasTrace_3965_ == 0)
{
lean_dec_ref(v_opts_3964_);
lean_dec(v___x_3959_);
v___y_3942_ = v___y_3930_;
v___y_3943_ = v___y_3931_;
goto v___jp_3941_;
}
else
{
lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3967_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3959_, v_opts_3964_, v___x_3966_);
lean_dec_ref(v_opts_3964_);
lean_dec(v___x_3959_);
if (v___x_3967_ == 0)
{
v___y_3942_ = v___y_3930_;
v___y_3943_ = v___y_3931_;
goto v___jp_3941_;
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3968_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3969_ = lean_array_get_size(v_a_3940_);
v___x_3970_ = l_Nat_reprFast(v___x_3969_);
v___x_3971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v___x_3972_ = l_Lean_MessageData_ofFormat(v___x_3971_);
v___x_3973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3968_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3937_, v___x_3973_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_dec_ref_known(v___x_3974_, 1);
v___y_3942_ = v___y_3930_;
v___y_3943_ = v___y_3931_;
goto v___jp_3941_;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v_a_3940_);
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
v___jp_3941_:
{
size_t v_sz_3944_; size_t v___x_3945_; lean_object* v___x_3946_; 
v_sz_3944_ = lean_array_size(v_a_3940_);
v___x_3945_ = ((size_t)0ULL);
lean_inc_ref(v___x_3924_);
lean_inc(v_a_3938_);
v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3938_, v___x_3924_, v___x_3925_, v_a_3940_, v_sz_3944_, v___x_3945_, v___x_3935_, v___y_3942_, v___y_3943_);
lean_dec(v_a_3940_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v___x_3947_; size_t v___x_3948_; size_t v___x_3949_; lean_object* v___x_3950_; 
lean_dec_ref_known(v___x_3946_, 1);
v___x_3947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3948_ = ((size_t)1ULL);
v___x_3949_ = lean_usize_add(v_i_3928_, v___x_3948_);
v___x_3950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3921_, v___x_3922_, v___x_3923_, v___x_3924_, v___x_3925_, v_as_3926_, v_sz_3927_, v___x_3949_, v___x_3947_, v___y_3930_, v___y_3931_);
return v___x_3950_;
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec_ref(v___x_3924_);
lean_dec(v_stx_3921_);
v_a_3951_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3946_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3946_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
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
v_a_3983_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3939_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3939_);
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
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v_a_4026_; lean_object* v___x_4027_; 
lean_dec_ref(v_b_4017_);
v___x_4023_ = lean_box(0);
v___x_4024_ = l_Lean_inheritedTraceOptions;
v___x_4025_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4026_ = lean_array_uget_borrowed(v_as_4014_, v_i_4016_);
lean_inc(v_a_4026_);
lean_inc(v_stx_4009_);
v___x_4027_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4009_, v___x_4010_, v_a_4026_, v___x_4011_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v_scopes_4050_; lean_object* v___x_4051_; lean_object* v_opts_4052_; uint8_t v_hasTrace_4053_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4047_ = lean_st_ref_get(v___x_4024_);
v___x_4048_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4049_ = lean_st_ref_get(v___y_4019_);
v_scopes_4050_ = lean_ctor_get(v___x_4049_, 2);
lean_inc(v_scopes_4050_);
lean_dec(v___x_4049_);
v___x_4051_ = l_List_head_x21___redArg(v___x_4048_, v_scopes_4050_);
lean_dec(v_scopes_4050_);
v_opts_4052_ = lean_ctor_get(v___x_4051_, 1);
lean_inc_ref(v_opts_4052_);
lean_dec(v___x_4051_);
v_hasTrace_4053_ = lean_ctor_get_uint8(v_opts_4052_, sizeof(void*)*1);
if (v_hasTrace_4053_ == 0)
{
lean_dec_ref(v_opts_4052_);
lean_dec(v___x_4047_);
v___y_4030_ = v___y_4018_;
v___y_4031_ = v___y_4019_;
goto v___jp_4029_;
}
else
{
lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4047_, v_opts_4052_, v___x_4054_);
lean_dec_ref(v_opts_4052_);
lean_dec(v___x_4047_);
if (v___x_4055_ == 0)
{
v___y_4030_ = v___y_4018_;
v___y_4031_ = v___y_4019_;
goto v___jp_4029_;
}
else
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4056_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4057_ = lean_array_get_size(v_a_4028_);
v___x_4058_ = l_Nat_reprFast(v___x_4057_);
v___x_4059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
v___x_4060_ = l_Lean_MessageData_ofFormat(v___x_4059_);
v___x_4061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4056_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4025_, v___x_4061_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_dec_ref_known(v___x_4062_, 1);
v___y_4030_ = v___y_4018_;
v___y_4031_ = v___y_4019_;
goto v___jp_4029_;
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v_a_4028_);
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
v___jp_4029_:
{
size_t v_sz_4032_; size_t v___x_4033_; lean_object* v___x_4034_; 
v_sz_4032_ = lean_array_size(v_a_4028_);
v___x_4033_ = ((size_t)0ULL);
lean_inc_ref(v___x_4012_);
lean_inc(v_a_4026_);
v___x_4034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4026_, v___x_4012_, v___x_4013_, v_a_4028_, v_sz_4032_, v___x_4033_, v___x_4023_, v___y_4030_, v___y_4031_);
lean_dec(v_a_4028_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v___x_4035_; size_t v___x_4036_; size_t v___x_4037_; 
lean_dec_ref_known(v___x_4034_, 1);
v___x_4035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4036_ = ((size_t)1ULL);
v___x_4037_ = lean_usize_add(v_i_4016_, v___x_4036_);
v_i_4016_ = v___x_4037_;
v_b_4017_ = v___x_4035_;
goto _start;
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec_ref(v___x_4012_);
lean_dec(v_stx_4009_);
v_a_4039_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4034_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4034_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
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
v_a_4071_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4027_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4027_);
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
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v_a_4111_; lean_object* v___x_4112_; 
lean_dec_ref(v_b_4102_);
v___x_4108_ = lean_box(0);
v___x_4109_ = l_Lean_inheritedTraceOptions;
v___x_4110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4111_ = lean_array_uget_borrowed(v_as_4099_, v_i_4101_);
lean_inc(v_a_4111_);
lean_inc(v_stx_4094_);
v___x_4112_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4094_, v___x_4095_, v_a_4111_, v___x_4096_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v_scopes_4135_; lean_object* v___x_4136_; lean_object* v_opts_4137_; uint8_t v_hasTrace_4138_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v___x_4132_ = lean_st_ref_get(v___x_4109_);
v___x_4133_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4134_ = lean_st_ref_get(v___y_4104_);
v_scopes_4135_ = lean_ctor_get(v___x_4134_, 2);
lean_inc(v_scopes_4135_);
lean_dec(v___x_4134_);
v___x_4136_ = l_List_head_x21___redArg(v___x_4133_, v_scopes_4135_);
lean_dec(v_scopes_4135_);
v_opts_4137_ = lean_ctor_get(v___x_4136_, 1);
lean_inc_ref(v_opts_4137_);
lean_dec(v___x_4136_);
v_hasTrace_4138_ = lean_ctor_get_uint8(v_opts_4137_, sizeof(void*)*1);
if (v_hasTrace_4138_ == 0)
{
lean_dec_ref(v_opts_4137_);
lean_dec(v___x_4132_);
v___y_4115_ = v___y_4103_;
v___y_4116_ = v___y_4104_;
goto v___jp_4114_;
}
else
{
lean_object* v___x_4139_; uint8_t v___x_4140_; 
v___x_4139_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4132_, v_opts_4137_, v___x_4139_);
lean_dec_ref(v_opts_4137_);
lean_dec(v___x_4132_);
if (v___x_4140_ == 0)
{
v___y_4115_ = v___y_4103_;
v___y_4116_ = v___y_4104_;
goto v___jp_4114_;
}
else
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4142_ = lean_array_get_size(v_a_4113_);
v___x_4143_ = l_Nat_reprFast(v___x_4142_);
v___x_4144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
v___x_4145_ = l_Lean_MessageData_ofFormat(v___x_4144_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4141_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4110_, v___x_4146_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_dec_ref_known(v___x_4147_, 1);
v___y_4115_ = v___y_4103_;
v___y_4116_ = v___y_4104_;
goto v___jp_4114_;
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec(v_a_4113_);
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
v___jp_4114_:
{
size_t v_sz_4117_; size_t v___x_4118_; lean_object* v___x_4119_; 
v_sz_4117_ = lean_array_size(v_a_4113_);
v___x_4118_ = ((size_t)0ULL);
lean_inc_ref(v___x_4097_);
lean_inc(v_a_4111_);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4111_, v___x_4097_, v___x_4098_, v_a_4113_, v_sz_4117_, v___x_4118_, v___x_4108_, v___y_4115_, v___y_4116_);
lean_dec(v_a_4113_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v___x_4120_; size_t v___x_4121_; size_t v___x_4122_; lean_object* v___x_4123_; 
lean_dec_ref_known(v___x_4119_, 1);
v___x_4120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4121_ = ((size_t)1ULL);
v___x_4122_ = lean_usize_add(v_i_4101_, v___x_4121_);
v___x_4123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4094_, v___x_4095_, v___x_4096_, v___x_4097_, v___x_4098_, v_as_4099_, v_sz_4100_, v___x_4122_, v___x_4120_, v___y_4103_, v___y_4104_);
return v___x_4123_;
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec_ref(v___x_4097_);
lean_dec(v_stx_4094_);
v_a_4124_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4119_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4119_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
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
v_a_4156_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4112_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4112_);
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
lean_object* v___x_4267_; lean_object* v_a_4268_; lean_object* v___x_4269_; 
v___x_4267_ = lean_box(0);
v_a_4268_ = lean_array_uget_borrowed(v_as_4254_, v_i_4256_);
lean_inc(v_snd_4263_);
lean_inc_ref(v___x_4252_);
lean_inc(v_stx_4249_);
v___x_4269_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4248_, v_stx_4249_, v___x_4250_, v___x_4251_, v___x_4252_, v___x_4253_, v_a_4268_, v_snd_4263_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4288_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4288_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4288_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
if (lean_obj_tag(v_a_4270_) == 0)
{
lean_object* v___x_4274_; lean_object* v___x_4276_; 
lean_dec_ref(v___x_4252_);
lean_dec(v_stx_4249_);
v___x_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4274_, 0, v_a_4270_);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v___x_4274_);
v___x_4276_ = v___x_4265_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4274_);
lean_ctor_set(v_reuseFailAlloc_4280_, 1, v_snd_4263_);
v___x_4276_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
lean_object* v___x_4278_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4276_);
v___x_4278_ = v___x_4272_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; 
lean_del_object(v___x_4272_);
lean_dec(v_snd_4263_);
v_a_4281_ = lean_ctor_get(v_a_4270_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v_a_4270_, 1);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 1, v_a_4281_);
lean_ctor_set(v___x_4265_, 0, v___x_4267_);
v___x_4283_ = v___x_4265_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4267_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_a_4281_);
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
v_a_4289_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4269_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4269_);
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
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v_scopes_4419_; lean_object* v___x_4420_; lean_object* v_opts_4421_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; uint8_t v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; uint8_t v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; uint8_t v___y_4462_; uint8_t v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; uint8_t v___y_4475_; uint8_t v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; uint8_t v___y_4479_; lean_object* v___y_4480_; uint8_t v___y_4489_; uint8_t v___y_4490_; uint8_t v___y_4491_; uint8_t v___y_4525_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v___x_4417_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4418_ = lean_st_ref_get(v___y_4412_);
v_scopes_4419_ = lean_ctor_get(v___x_4418_, 2);
lean_inc(v_scopes_4419_);
lean_dec(v___x_4418_);
v___x_4420_ = l_List_head_x21___redArg(v___x_4417_, v_scopes_4419_);
lean_dec(v_scopes_4419_);
v_opts_4421_ = lean_ctor_get(v___x_4420_, 1);
lean_inc_ref(v_opts_4421_);
lean_dec(v___x_4420_);
v___x_4532_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4533_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4421_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4534_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4535_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4421_, v___x_4534_);
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
lean_object* v___x_4427_; lean_object* v_line_4428_; lean_object* v___x_4429_; lean_object* v_messages_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v_a_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
lean_inc_ref_n(v___y_4425_, 2);
v___x_4427_ = l_Lean_FileMap_toPosition(v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
v_line_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_line_4428_);
lean_dec_ref(v___x_4427_);
v___x_4429_ = lean_st_ref_get(v___y_4423_);
v_messages_4430_ = lean_ctor_get(v___x_4429_, 1);
lean_inc_ref(v_messages_4430_);
lean_dec(v___x_4429_);
v___x_4431_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4430_);
v___x_4432_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4423_);
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref(v___x_4432_);
v___x_4434_ = lean_box(0);
v___x_4435_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4425_, v_line_4428_, v_stx_4410_, v_opts_4421_, v___x_4431_, v_a_4433_, v___x_4434_, v___y_4424_, v___y_4423_);
lean_dec(v_a_4433_);
lean_dec_ref(v___x_4431_);
lean_dec_ref(v_opts_4421_);
lean_dec(v_line_4428_);
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
v___y_4424_ = v___y_4446_;
v___y_4425_ = v_fileMap_4448_;
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
v___y_4424_ = v___y_4446_;
v___y_4425_ = v_fileMap_4448_;
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
lean_ctor_set(v___x_4459_, 0, v___y_4454_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
lean_inc(v___y_4455_);
v___x_4460_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___y_4455_, v___x_4459_, v___y_4411_, v___y_4412_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_dec_ref_known(v___x_4460_, 1);
v___y_4445_ = v___y_4453_;
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
lean_ctor_set(v___x_4469_, 0, v___y_4464_);
lean_ctor_set(v___x_4469_, 1, v___x_4468_);
v___x_4470_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4469_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
if (v___y_4462_ == 0)
{
lean_object* v___x_4472_; 
v___x_4472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4453_ = v___y_4463_;
v___y_4454_ = v___x_4471_;
v___y_4455_ = v___y_4465_;
v___y_4456_ = v___x_4472_;
goto v___jp_4452_;
}
else
{
lean_object* v___x_4473_; 
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4453_ = v___y_4463_;
v___y_4454_ = v___x_4471_;
v___y_4455_ = v___y_4465_;
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
lean_inc_ref(v___y_4478_);
v___x_4483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4483_, 0, v___y_4478_);
lean_ctor_set(v___x_4483_, 1, v___x_4482_);
v___x_4484_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4483_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
if (v___y_4479_ == 0)
{
lean_object* v___x_4486_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4462_ = v___y_4476_;
v___y_4463_ = v___y_4475_;
v___y_4464_ = v___x_4485_;
v___y_4465_ = v___y_4477_;
v___y_4466_ = v___x_4486_;
goto v___jp_4461_;
}
else
{
lean_object* v___x_4487_; 
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4462_ = v___y_4476_;
v___y_4463_ = v___y_4475_;
v___y_4464_ = v___x_4485_;
v___y_4465_ = v___y_4477_;
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
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v_scopes_4499_; lean_object* v___x_4500_; lean_object* v_opts_4501_; uint8_t v_hasTrace_4502_; 
v___x_4495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4496_ = l_Lean_inheritedTraceOptions;
v___x_4497_ = lean_st_ref_get(v___x_4496_);
v___x_4498_ = lean_st_ref_get(v___y_4412_);
v_scopes_4499_ = lean_ctor_get(v___x_4498_, 2);
lean_inc(v_scopes_4499_);
lean_dec(v___x_4498_);
v___x_4500_ = l_List_head_x21___redArg(v___x_4417_, v_scopes_4499_);
lean_dec(v_scopes_4499_);
v_opts_4501_ = lean_ctor_get(v___x_4500_, 1);
lean_inc_ref(v_opts_4501_);
lean_dec(v___x_4500_);
v_hasTrace_4502_ = lean_ctor_get_uint8(v_opts_4501_, sizeof(void*)*1);
if (v_hasTrace_4502_ == 0)
{
uint8_t v___x_4503_; 
lean_dec_ref(v_opts_4501_);
lean_dec(v___x_4497_);
v___x_4503_ = lean_unbox(v_a_4493_);
lean_dec(v_a_4493_);
v___y_4445_ = v___x_4503_;
v___y_4446_ = v___y_4411_;
v___y_4447_ = v___y_4412_;
goto v___jp_4444_;
}
else
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4505_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4497_, v_opts_4501_, v___x_4504_);
lean_dec_ref(v_opts_4501_);
lean_dec(v___x_4497_);
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
v___y_4475_ = v___x_4509_;
v___y_4476_ = v___y_4489_;
v___y_4477_ = v___x_4495_;
v___y_4478_ = v___x_4507_;
v___y_4479_ = v___y_4491_;
v___y_4480_ = v___x_4508_;
goto v___jp_4474_;
}
else
{
lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4510_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4511_ = lean_unbox(v_a_4493_);
lean_dec(v_a_4493_);
v___y_4475_ = v___x_4511_;
v___y_4476_ = v___y_4489_;
v___y_4477_ = v___x_4495_;
v___y_4478_ = v___x_4507_;
v___y_4479_ = v___y_4491_;
v___y_4480_ = v___x_4510_;
goto v___jp_4474_;
}
}
}
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v_scopes_4516_; lean_object* v___x_4517_; lean_object* v_opts_4518_; uint8_t v_hasTrace_4519_; 
lean_dec(v_a_4493_);
lean_dec_ref(v_opts_4421_);
lean_dec(v_stx_4410_);
v___x_4512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4513_ = l_Lean_inheritedTraceOptions;
v___x_4514_ = lean_st_ref_get(v___x_4513_);
v___x_4515_ = lean_st_ref_get(v___y_4412_);
v_scopes_4516_ = lean_ctor_get(v___x_4515_, 2);
lean_inc(v_scopes_4516_);
lean_dec(v___x_4515_);
v___x_4517_ = l_List_head_x21___redArg(v___x_4417_, v_scopes_4516_);
lean_dec(v_scopes_4516_);
v_opts_4518_ = lean_ctor_get(v___x_4517_, 1);
lean_inc_ref(v_opts_4518_);
lean_dec(v___x_4517_);
v_hasTrace_4519_ = lean_ctor_get_uint8(v_opts_4518_, sizeof(void*)*1);
if (v_hasTrace_4519_ == 0)
{
lean_dec_ref(v_opts_4518_);
lean_dec(v___x_4514_);
goto v___jp_4414_;
}
else
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4521_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4514_, v_opts_4518_, v___x_4520_);
lean_dec_ref(v_opts_4518_);
lean_dec(v___x_4514_);
if (v___x_4521_ == 0)
{
goto v___jp_4414_;
}
else
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4523_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4512_, v___x_4522_, v___y_4411_, v___y_4412_);
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
v___x_4527_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4421_, v___x_4526_);
v___x_4528_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4529_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4421_, v___x_4528_);
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
v___y_4489_ = v___x_4529_;
v___y_4490_ = v___y_4525_;
v___y_4491_ = v___x_4527_;
goto v___jp_4488_;
}
}
else
{
v___y_4489_ = v___x_4529_;
v___y_4490_ = v___y_4525_;
v___y_4491_ = v___x_4527_;
goto v___jp_4488_;
}
}
else
{
v___y_4489_ = v___x_4529_;
v___y_4490_ = v___y_4525_;
v___y_4491_ = v___x_4527_;
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
