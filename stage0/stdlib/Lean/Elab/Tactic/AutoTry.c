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
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
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
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_89_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_90_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__21_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_91_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_88_, v___x_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_92_;
v_res_92_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_();
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4____boxed(lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_();
return v_res_94_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__9_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_));
v___x_126_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_123_, v___x_124_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_127_;
v_res_127_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_();
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4____boxed(lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1181904795____hygCtx___hyg_4_();
return v_res_129_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_));
v___x_147_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_144_, v___x_145_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_148_;
v_res_148_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_();
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4____boxed(lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_419759358____hygCtx___hyg_4_();
return v_res_150_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__1_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__3_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_167_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_));
v___x_168_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_169_;
v_res_169_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_();
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4____boxed(lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3925664777____hygCtx___hyg_4_();
return v_res_171_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__2_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__4_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_));
v___x_197_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4__spec__0(v___x_194_, v___x_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_198_;
v_res_198_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_();
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4____boxed(lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_1514339415____hygCtx___hyg_4_();
return v_res_200_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_239_ = 0;
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__14_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_241_ = l_Lean_registerTraceClass(v___x_238_, v___x_239_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_242_;
v_res_242_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_();
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2____boxed(lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_();
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object* v_opts_245_, lean_object* v_opt_246_){
_start:
{
lean_object* v_name_247_; lean_object* v_defValue_248_; lean_object* v_map_249_; lean_object* v___x_250_; 
v_name_247_ = lean_ctor_get(v_opt_246_, 0);
v_defValue_248_ = lean_ctor_get(v_opt_246_, 1);
v_map_249_ = lean_ctor_get(v_opts_245_, 0);
v___x_250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_249_, v_name_247_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_inc(v_defValue_248_);
return v_defValue_248_;
}
else
{
lean_object* v_val_251_; 
v_val_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_val_251_);
lean_dec_ref_known(v___x_250_, 1);
if (lean_obj_tag(v_val_251_) == 3)
{
lean_object* v_v_252_; 
v_v_252_ = lean_ctor_get(v_val_251_, 0);
lean_inc(v_v_252_);
lean_dec_ref_known(v_val_251_, 1);
return v_v_252_;
}
else
{
lean_dec(v_val_251_);
lean_inc(v_defValue_248_);
return v_defValue_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___boxed(lean_object* v_opts_253_, lean_object* v_opt_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_253_, v_opt_254_);
lean_dec_ref(v_opt_254_);
lean_dec_ref(v_opts_253_);
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
v___x_269_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
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
v___x_273_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
lean_ctor_set(v___x_273_, 2, v___x_272_);
lean_ctor_set(v___x_273_, 3, v___x_272_);
lean_ctor_set(v___x_273_, 4, v___x_272_);
lean_ctor_set(v___x_273_, 5, v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(32u);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8(void){
_start:
{
size_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_277_ = ((size_t)5ULL);
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_unsigned_to_nat(32u);
v___x_280_ = lean_mk_empty_array_with_capacity(v___x_279_);
v___x_281_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7);
v___x_282_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
lean_ctor_set(v___x_282_, 2, v___x_278_);
lean_ctor_set(v___x_282_, 3, v___x_278_);
lean_ctor_set_usize(v___x_282_, 4, v___x_277_);
return v___x_282_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
lean_ctor_set(v___x_284_, 2, v___x_283_);
lean_ctor_set(v___x_284_, 3, v___x_283_);
lean_ctor_set(v___x_284_, 4, v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = l_Lean_Options_empty;
v___x_286_ = l_Lean_Core_getMaxHeartbeats(v___x_285_);
return v___x_286_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11(void){
_start:
{
lean_object* v___x_287_; uint16_t v___x_288_; 
v___x_287_ = l_Lean_Options_empty;
v___x_288_ = l_Lean_OptionFlags_ofOptions(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = l_Lean_firstFrontendMacroScope;
v___x_291_ = lean_nat_add(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17(void){
_start:
{
lean_object* v___x_302_; uint64_t v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_303_ = 0ULL;
v___x_304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set_uint64(v___x_304_, sizeof(void*)*1, v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = l_Lean_Options_empty;
v___x_309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_310_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
lean_ctor_set(v___x_310_, 2, v___x_309_);
lean_ctor_set(v___x_310_, 3, v___x_307_);
lean_ctor_set(v___x_310_, 4, v___x_307_);
lean_ctor_set(v___x_310_, 5, v___x_307_);
return v___x_310_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = l_Lean_NameSet_empty;
v___x_312_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
lean_ctor_set(v___x_313_, 2, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; 
v___x_314_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_315_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_316_ = 1;
v___x_317_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
lean_ctor_set(v___x_317_, 2, v___x_314_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*3, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = l_Lean_maxRecDepth;
v___x_322_ = l_Lean_Options_empty;
v___x_323_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v___x_322_, v___x_321_);
return v___x_323_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26(void){
_start:
{
uint16_t v___x_324_; uint16_t v___x_325_; uint16_t v___x_326_; 
v___x_324_ = 512;
v___x_325_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_326_ = lean_uint16_land(v___x_325_, v___x_324_);
return v___x_326_;
}
}
static uint8_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27(void){
_start:
{
uint16_t v___x_327_; uint16_t v___x_328_; uint8_t v___x_329_; 
v___x_327_ = 0;
v___x_328_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26);
v___x_329_ = lean_uint16_dec_eq(v___x_328_, v___x_327_);
return v___x_329_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object* v_env_330_, lean_object* v_mctx_331_, lean_object* v_lctx_332_, lean_object* v_opts_333_, lean_object* v_namingCtx_334_, lean_object* v_x_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_fileName_351_; lean_object* v_fileMap_352_; lean_object* v_ref_353_; lean_object* v_cancelTk_x3f_354_; lean_object* v_a_356_; lean_object* v_a_363_; lean_object* v_currNamespace_365_; lean_object* v_openDecls_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint16_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint16_t v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; uint16_t v___y_488_; uint8_t v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v_fileName_528_; lean_object* v_fileMap_529_; lean_object* v_currNamespace_530_; lean_object* v_openDecls_531_; lean_object* v_initHeartbeats_532_; lean_object* v_maxHeartbeats_533_; lean_object* v_quotContext_534_; lean_object* v_currMacroScope_535_; lean_object* v_cancelTk_x3f_536_; lean_object* v_inheritedTraceOptions_537_; lean_object* v_currRecDepth_538_; lean_object* v_ref_539_; uint8_t v_suppressElabErrors_540_; uint8_t v_isRecordingDeps_541_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___y_550_; lean_object* v_env_571_; uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_339_ = lean_box(1);
v___x_340_ = 0;
v___x_341_ = l_Lean_Environment_setExporting(v_env_330_, v___x_340_);
v___x_342_ = 1;
v___x_343_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_346_ = lean_box(0);
v___x_347_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_347_, 0, v___x_343_);
lean_ctor_set(v___x_347_, 1, v___x_339_);
lean_ctor_set(v___x_347_, 2, v_lctx_332_);
lean_ctor_set(v___x_347_, 3, v___x_345_);
lean_ctor_set(v___x_347_, 4, v___x_346_);
lean_ctor_set(v___x_347_, 5, v___x_344_);
lean_ctor_set(v___x_347_, 6, v___x_346_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*7, v___x_340_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*7 + 1, v___x_340_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*7 + 2, v___x_340_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*7 + 3, v___x_342_);
v___x_348_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6);
v___x_349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_350_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9);
v_fileName_351_ = lean_ctor_get(v_a_336_, 0);
v_fileMap_352_ = lean_ctor_get(v_a_336_, 1);
v_ref_353_ = lean_ctor_get(v_a_336_, 7);
v_cancelTk_x3f_354_ = lean_ctor_get(v_a_336_, 9);
v_currNamespace_365_ = lean_ctor_get(v_namingCtx_334_, 0);
lean_inc(v_currNamespace_365_);
v_openDecls_366_ = lean_ctor_get(v_namingCtx_334_, 1);
lean_inc(v_openDecls_366_);
lean_dec_ref(v_namingCtx_334_);
v___x_367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_367_, 0, v_mctx_331_);
lean_ctor_set(v___x_367_, 1, v___x_348_);
lean_ctor_set(v___x_367_, 2, v___x_339_);
lean_ctor_set(v___x_367_, 3, v___x_349_);
lean_ctor_set(v___x_367_, 4, v___x_350_);
v___x_368_ = l_Lean_Options_empty;
v___x_369_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_370_ = lean_box(0);
v___x_371_ = l_Lean_firstFrontendMacroScope;
v___x_372_ = lean_box(0);
v___x_373_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_374_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12);
v___x_375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15));
v___x_376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16));
v___x_377_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17);
v___x_378_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18);
v___x_379_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
v___x_380_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20);
v___x_381_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21);
v___x_382_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_382_, 0, v___x_341_);
lean_ctor_set(v___x_382_, 1, v___x_374_);
lean_ctor_set(v___x_382_, 2, v___x_375_);
lean_ctor_set(v___x_382_, 3, v___x_376_);
lean_ctor_set(v___x_382_, 4, v___x_377_);
lean_ctor_set(v___x_382_, 5, v___x_378_);
lean_ctor_set(v___x_382_, 6, v___x_379_);
lean_ctor_set(v___x_382_, 7, v___x_380_);
lean_ctor_set(v___x_382_, 8, v___x_381_);
lean_ctor_set(v___x_382_, 9, v___x_345_);
v___x_383_ = lean_io_get_num_heartbeats();
v___x_384_ = lean_st_mk_ref(v___x_382_);
v___x_546_ = l_Lean_inheritedTraceOptions;
v___x_547_ = lean_st_ref_get(v___x_546_);
v___x_548_ = lean_st_ref_get(v___x_384_);
v_env_571_ = lean_ctor_get(v___x_548_, 0);
lean_inc_ref(v_env_571_);
lean_dec(v___x_548_);
v___x_572_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_571_);
lean_dec_ref(v_env_571_);
v___x_573_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27);
if (v___x_573_ == 0)
{
if (v___x_572_ == 0)
{
v___y_550_ = v___x_342_;
goto v___jp_549_;
}
else
{
v_fileName_528_ = v_fileName_351_;
v_fileMap_529_ = v_fileMap_352_;
v_currNamespace_530_ = v_currNamespace_365_;
v_openDecls_531_ = v_openDecls_366_;
v_initHeartbeats_532_ = v___x_383_;
v_maxHeartbeats_533_ = v___x_369_;
v_quotContext_534_ = v___x_370_;
v_currMacroScope_535_ = v___x_371_;
v_cancelTk_x3f_536_ = v_cancelTk_x3f_354_;
v_inheritedTraceOptions_537_ = v___x_547_;
v_currRecDepth_538_ = v___x_344_;
v_ref_539_ = v___x_372_;
v_suppressElabErrors_540_ = v___x_340_;
v_isRecordingDeps_541_ = v___x_340_;
goto v___jp_527_;
}
}
else
{
if (v___x_572_ == 0)
{
v_fileName_528_ = v_fileName_351_;
v_fileMap_529_ = v_fileMap_352_;
v_currNamespace_530_ = v_currNamespace_365_;
v_openDecls_531_ = v_openDecls_366_;
v_initHeartbeats_532_ = v___x_383_;
v_maxHeartbeats_533_ = v___x_369_;
v_quotContext_534_ = v___x_370_;
v_currMacroScope_535_ = v___x_371_;
v_cancelTk_x3f_536_ = v_cancelTk_x3f_354_;
v_inheritedTraceOptions_537_ = v___x_547_;
v_currRecDepth_538_ = v___x_344_;
v_ref_539_ = v___x_372_;
v_suppressElabErrors_540_ = v___x_340_;
v_isRecordingDeps_541_ = v___x_340_;
goto v___jp_527_;
}
else
{
v___y_550_ = v___x_340_;
goto v___jp_549_;
}
}
v___jp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_357_ = lean_io_error_to_string(v_a_356_);
v___x_358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
v___x_359_ = l_Lean_MessageData_ofFormat(v___x_358_);
lean_inc(v_ref_353_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_ref_353_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
v___jp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = lean_mk_io_user_error(v_a_363_);
v_a_356_ = v___x_364_;
goto v___jp_355_;
}
v___jp_385_:
{
lean_object* v_toCold_391_; lean_object* v_currRecDepth_392_; lean_object* v_ref_393_; uint8_t v_suppressElabErrors_394_; uint8_t v_isRecordingDeps_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_486_; 
v_toCold_391_ = lean_ctor_get(v___y_389_, 0);
v_currRecDepth_392_ = lean_ctor_get(v___y_389_, 1);
v_ref_393_ = lean_ctor_get(v___y_389_, 2);
v_suppressElabErrors_394_ = lean_ctor_get_uint8(v___y_389_, sizeof(void*)*3 + 2);
v_isRecordingDeps_395_ = lean_ctor_get_uint8(v___y_389_, sizeof(void*)*3 + 3);
v_isSharedCheck_486_ = !lean_is_exclusive(v___y_389_);
if (v_isSharedCheck_486_ == 0)
{
v___x_397_ = v___y_389_;
v_isShared_398_ = v_isSharedCheck_486_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_ref_393_);
lean_inc(v_currRecDepth_392_);
lean_inc(v_toCold_391_);
lean_dec(v___y_389_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_486_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_fileName_399_; lean_object* v_fileMap_400_; lean_object* v_currNamespace_401_; lean_object* v_openDecls_402_; lean_object* v_initHeartbeats_403_; lean_object* v_maxHeartbeats_404_; lean_object* v_quotContext_405_; lean_object* v_currMacroScope_406_; lean_object* v_cancelTk_x3f_407_; lean_object* v_inheritedTraceOptions_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_483_; 
v_fileName_399_ = lean_ctor_get(v_toCold_391_, 0);
v_fileMap_400_ = lean_ctor_get(v_toCold_391_, 1);
v_currNamespace_401_ = lean_ctor_get(v_toCold_391_, 4);
v_openDecls_402_ = lean_ctor_get(v_toCold_391_, 5);
v_initHeartbeats_403_ = lean_ctor_get(v_toCold_391_, 6);
v_maxHeartbeats_404_ = lean_ctor_get(v_toCold_391_, 7);
v_quotContext_405_ = lean_ctor_get(v_toCold_391_, 8);
v_currMacroScope_406_ = lean_ctor_get(v_toCold_391_, 9);
v_cancelTk_x3f_407_ = lean_ctor_get(v_toCold_391_, 10);
v_inheritedTraceOptions_408_ = lean_ctor_get(v_toCold_391_, 11);
v_isSharedCheck_483_ = !lean_is_exclusive(v_toCold_391_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; lean_object* v_unused_485_; 
v_unused_484_ = lean_ctor_get(v_toCold_391_, 3);
lean_dec(v_unused_484_);
v_unused_485_ = lean_ctor_get(v_toCold_391_, 2);
lean_dec(v_unused_485_);
v___x_410_ = v_toCold_391_;
v_isShared_411_ = v_isSharedCheck_483_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_inheritedTraceOptions_408_);
lean_inc(v_cancelTk_x3f_407_);
lean_inc(v_currMacroScope_406_);
lean_inc(v_quotContext_405_);
lean_inc(v_maxHeartbeats_404_);
lean_inc(v_initHeartbeats_403_);
lean_inc(v_openDecls_402_);
lean_inc(v_currNamespace_401_);
lean_inc(v_fileMap_400_);
lean_inc(v_fileName_399_);
lean_dec(v_toCold_391_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_483_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v___y_388_, v___y_387_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 3, v___x_412_);
lean_ctor_set(v___x_410_, 2, v___y_388_);
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_fileName_399_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_fileMap_400_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v___y_388_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_currNamespace_401_);
lean_ctor_set(v_reuseFailAlloc_482_, 5, v_openDecls_402_);
lean_ctor_set(v_reuseFailAlloc_482_, 6, v_initHeartbeats_403_);
lean_ctor_set(v_reuseFailAlloc_482_, 7, v_maxHeartbeats_404_);
lean_ctor_set(v_reuseFailAlloc_482_, 8, v_quotContext_405_);
lean_ctor_set(v_reuseFailAlloc_482_, 9, v_currMacroScope_406_);
lean_ctor_set(v_reuseFailAlloc_482_, 10, v_cancelTk_x3f_407_);
lean_ctor_set(v_reuseFailAlloc_482_, 11, v_inheritedTraceOptions_408_);
v___x_414_ = v_reuseFailAlloc_482_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_414_);
v___x_416_ = v___x_397_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_currRecDepth_392_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_ref_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*3 + 2, v_suppressElabErrors_394_);
lean_ctor_set_uint8(v_reuseFailAlloc_481_, sizeof(void*)*3 + 3, v_isRecordingDeps_395_);
v___x_416_ = v_reuseFailAlloc_481_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_ctor_set_uint16(v___x_416_, sizeof(void*)*3, v___y_386_);
v___x_417_ = lean_st_mk_ref(v___x_367_);
lean_inc(v___x_417_);
v___x_418_ = lean_apply_5(v_x_335_, v___x_347_, v___x_417_, v___x_416_, v___y_390_, lean_box(0));
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_465_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_465_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_465_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_465_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_traceState_426_; lean_object* v_traceState_427_; lean_object* v_env_428_; lean_object* v_messages_429_; lean_object* v_scopes_430_; lean_object* v_usedQuotCtxts_431_; lean_object* v_nextMacroScope_432_; lean_object* v_maxRecDepth_433_; lean_object* v_ngen_434_; lean_object* v_auxDeclNGen_435_; lean_object* v_infoState_436_; lean_object* v_snapshotTasks_437_; lean_object* v_prevLinterStates_438_; lean_object* v_codeQualityEntryTasks_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_463_; 
v___x_423_ = lean_st_ref_get(v___x_417_);
lean_dec(v___x_417_);
lean_dec(v___x_423_);
v___x_424_ = lean_st_ref_get(v___x_384_);
lean_dec(v___x_384_);
v___x_425_ = lean_st_ref_take(v_a_337_);
v_traceState_426_ = lean_ctor_get(v___x_425_, 9);
lean_inc_ref(v_traceState_426_);
v_traceState_427_ = lean_ctor_get(v___x_424_, 4);
lean_inc_ref(v_traceState_427_);
v_env_428_ = lean_ctor_get(v___x_425_, 0);
v_messages_429_ = lean_ctor_get(v___x_425_, 1);
v_scopes_430_ = lean_ctor_get(v___x_425_, 2);
v_usedQuotCtxts_431_ = lean_ctor_get(v___x_425_, 3);
v_nextMacroScope_432_ = lean_ctor_get(v___x_425_, 4);
v_maxRecDepth_433_ = lean_ctor_get(v___x_425_, 5);
v_ngen_434_ = lean_ctor_get(v___x_425_, 6);
v_auxDeclNGen_435_ = lean_ctor_get(v___x_425_, 7);
v_infoState_436_ = lean_ctor_get(v___x_425_, 8);
v_snapshotTasks_437_ = lean_ctor_get(v___x_425_, 10);
v_prevLinterStates_438_ = lean_ctor_get(v___x_425_, 11);
v_codeQualityEntryTasks_439_ = lean_ctor_get(v___x_425_, 12);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v___x_425_, 9);
lean_dec(v_unused_464_);
v___x_441_ = v___x_425_;
v_isShared_442_ = v_isSharedCheck_463_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_codeQualityEntryTasks_439_);
lean_inc(v_prevLinterStates_438_);
lean_inc(v_snapshotTasks_437_);
lean_inc(v_infoState_436_);
lean_inc(v_auxDeclNGen_435_);
lean_inc(v_ngen_434_);
lean_inc(v_maxRecDepth_433_);
lean_inc(v_nextMacroScope_432_);
lean_inc(v_usedQuotCtxts_431_);
lean_inc(v_scopes_430_);
lean_inc(v_messages_429_);
lean_inc(v_env_428_);
lean_dec(v___x_425_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_463_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_messages_443_; uint64_t v_tid_444_; lean_object* v_traces_445_; lean_object* v_traces_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_462_; 
v_messages_443_ = lean_ctor_get(v___x_424_, 7);
lean_inc_ref(v_messages_443_);
lean_dec(v___x_424_);
v_tid_444_ = lean_ctor_get_uint64(v_traceState_426_, sizeof(void*)*1);
v_traces_445_ = lean_ctor_get(v_traceState_426_, 0);
lean_inc_ref(v_traces_445_);
lean_dec_ref(v_traceState_426_);
v_traces_446_ = lean_ctor_get(v_traceState_427_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_traceState_427_);
if (v_isSharedCheck_462_ == 0)
{
v___x_448_ = v_traceState_427_;
v_isShared_449_ = v_isSharedCheck_462_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_traces_446_);
lean_dec(v_traceState_427_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_462_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_450_ = l_Lean_MessageLog_append(v_messages_429_, v_messages_443_);
v___x_451_ = l_Lean_PersistentArray_append___redArg(v_traces_445_, v_traces_446_);
lean_dec_ref(v_traces_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_461_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_455_; 
lean_ctor_set_uint64(v___x_453_, sizeof(void*)*1, v_tid_444_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 9, v___x_453_);
lean_ctor_set(v___x_441_, 1, v___x_450_);
v___x_455_ = v___x_441_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_env_428_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_scopes_430_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v_usedQuotCtxts_431_);
lean_ctor_set(v_reuseFailAlloc_460_, 4, v_nextMacroScope_432_);
lean_ctor_set(v_reuseFailAlloc_460_, 5, v_maxRecDepth_433_);
lean_ctor_set(v_reuseFailAlloc_460_, 6, v_ngen_434_);
lean_ctor_set(v_reuseFailAlloc_460_, 7, v_auxDeclNGen_435_);
lean_ctor_set(v_reuseFailAlloc_460_, 8, v_infoState_436_);
lean_ctor_set(v_reuseFailAlloc_460_, 9, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_460_, 10, v_snapshotTasks_437_);
lean_ctor_set(v_reuseFailAlloc_460_, 11, v_prevLinterStates_438_);
lean_ctor_set(v_reuseFailAlloc_460_, 12, v_codeQualityEntryTasks_439_);
v___x_455_ = v_reuseFailAlloc_460_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_st_ref_put(v_a_337_, v___x_455_);
if (v_isShared_422_ == 0)
{
v___x_458_ = v___x_421_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_419_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_466_; 
lean_dec(v___x_417_);
lean_dec(v___x_384_);
v_a_466_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_418_, 1);
if (lean_obj_tag(v_a_466_) == 0)
{
lean_object* v_msg_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_msg_467_ = lean_ctor_get(v_a_466_, 1);
lean_inc_ref(v_msg_467_);
lean_dec_ref_known(v_a_466_, 2);
v___x_468_ = l_Lean_MessageData_toString(v_msg_467_);
v___x_469_ = lean_mk_io_user_error(v___x_468_);
v_a_356_ = v___x_469_;
goto v___jp_355_;
}
else
{
lean_object* v_id_470_; lean_object* v___x_471_; 
v_id_470_ = lean_ctor_get(v_a_466_, 0);
lean_inc(v_id_470_);
lean_dec_ref_known(v_a_466_, 2);
v___x_471_ = l_Lean_InternalExceptionId_getName(v_id_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v_id_470_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_474_ = l_Lean_Name_toString(v_a_472_, v___x_342_);
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
lean_dec_ref(v___x_474_);
v_a_363_ = v___x_475_;
goto v___jp_362_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec_ref_known(v___x_471_, 1);
v___x_476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23));
v___x_477_ = l_Nat_reprFast(v_id_470_);
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
lean_dec_ref(v___x_477_);
v___x_479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24));
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
v_a_363_ = v___x_480_;
goto v___jp_362_;
}
}
}
}
}
}
}
}
v___jp_487_:
{
lean_object* v___x_494_; lean_object* v_env_495_; lean_object* v_nextMacroScope_496_; lean_object* v_ngen_497_; lean_object* v_auxDeclNGen_498_; lean_object* v_traceState_499_; lean_object* v_recordedDeps_500_; lean_object* v_messages_501_; lean_object* v_infoState_502_; lean_object* v_snapshotTasks_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_512_; 
v___x_494_ = lean_st_ref_take(v___y_493_);
v_env_495_ = lean_ctor_get(v___x_494_, 0);
v_nextMacroScope_496_ = lean_ctor_get(v___x_494_, 1);
v_ngen_497_ = lean_ctor_get(v___x_494_, 2);
v_auxDeclNGen_498_ = lean_ctor_get(v___x_494_, 3);
v_traceState_499_ = lean_ctor_get(v___x_494_, 4);
v_recordedDeps_500_ = lean_ctor_get(v___x_494_, 6);
v_messages_501_ = lean_ctor_get(v___x_494_, 7);
v_infoState_502_ = lean_ctor_get(v___x_494_, 8);
v_snapshotTasks_503_ = lean_ctor_get(v___x_494_, 9);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v___x_494_, 5);
lean_dec(v_unused_513_);
v___x_505_ = v___x_494_;
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_snapshotTasks_503_);
lean_inc(v_infoState_502_);
lean_inc(v_messages_501_);
lean_inc(v_recordedDeps_500_);
lean_inc(v_traceState_499_);
lean_inc(v_auxDeclNGen_498_);
lean_inc(v_ngen_497_);
lean_inc(v_nextMacroScope_496_);
lean_inc(v_env_495_);
lean_dec(v___x_494_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = l_Lean_Kernel_enableDiag(v_env_495_, v___y_489_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 5, v___x_378_);
lean_ctor_set(v___x_505_, 0, v___x_507_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_nextMacroScope_496_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_ngen_497_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_auxDeclNGen_498_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_traceState_499_);
lean_ctor_set(v_reuseFailAlloc_511_, 5, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_511_, 6, v_recordedDeps_500_);
lean_ctor_set(v_reuseFailAlloc_511_, 7, v_messages_501_);
lean_ctor_set(v_reuseFailAlloc_511_, 8, v_infoState_502_);
lean_ctor_set(v_reuseFailAlloc_511_, 9, v_snapshotTasks_503_);
v___x_509_ = v_reuseFailAlloc_511_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; 
v___x_510_ = lean_st_ref_put(v___y_493_, v___x_509_);
v___y_386_ = v___y_488_;
v___y_387_ = v___y_490_;
v___y_388_ = v___y_491_;
v___y_389_ = v___y_492_;
v___y_390_ = v___y_493_;
goto v___jp_385_;
}
}
}
v___jp_514_:
{
uint16_t v___x_519_; lean_object* v___x_520_; lean_object* v_env_521_; uint8_t v___x_522_; uint16_t v___x_523_; uint16_t v___x_524_; uint16_t v___x_525_; uint8_t v___x_526_; 
v___x_519_ = l_Lean_OptionFlags_ofOptions(v___y_518_);
v___x_520_ = lean_st_ref_get(v___y_517_);
v_env_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_ref(v_env_521_);
lean_dec(v___x_520_);
v___x_522_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_521_);
lean_dec_ref(v_env_521_);
v___x_523_ = 512;
v___x_524_ = lean_uint16_land(v___x_519_, v___x_523_);
v___x_525_ = 0;
v___x_526_ = lean_uint16_dec_eq(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
if (v___x_522_ == 0)
{
v___y_488_ = v___x_519_;
v___y_489_ = v___x_342_;
v___y_490_ = v___y_515_;
v___y_491_ = v___y_518_;
v___y_492_ = v___y_516_;
v___y_493_ = v___y_517_;
goto v___jp_487_;
}
else
{
v___y_386_ = v___x_519_;
v___y_387_ = v___y_515_;
v___y_388_ = v___y_518_;
v___y_389_ = v___y_516_;
v___y_390_ = v___y_517_;
goto v___jp_385_;
}
}
else
{
if (v___x_522_ == 0)
{
v___y_386_ = v___x_519_;
v___y_387_ = v___y_515_;
v___y_388_ = v___y_518_;
v___y_389_ = v___y_516_;
v___y_390_ = v___y_517_;
goto v___jp_385_;
}
else
{
v___y_488_ = v___x_519_;
v___y_489_ = v___x_340_;
v___y_490_ = v___y_515_;
v___y_491_ = v___y_518_;
v___y_492_ = v___y_516_;
v___y_493_ = v___y_517_;
goto v___jp_487_;
}
}
}
v___jp_527_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = l_Lean_maxRecDepth;
v___x_543_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25);
lean_inc(v_cancelTk_x3f_536_);
lean_inc(v_currMacroScope_535_);
lean_inc(v_quotContext_534_);
lean_inc(v_maxHeartbeats_533_);
lean_inc_ref(v_fileMap_529_);
lean_inc_ref(v_fileName_528_);
v___x_544_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_544_, 0, v_fileName_528_);
lean_ctor_set(v___x_544_, 1, v_fileMap_529_);
lean_ctor_set(v___x_544_, 2, v___x_368_);
lean_ctor_set(v___x_544_, 3, v___x_543_);
lean_ctor_set(v___x_544_, 4, v_currNamespace_530_);
lean_ctor_set(v___x_544_, 5, v_openDecls_531_);
lean_ctor_set(v___x_544_, 6, v_initHeartbeats_532_);
lean_ctor_set(v___x_544_, 7, v_maxHeartbeats_533_);
lean_ctor_set(v___x_544_, 8, v_quotContext_534_);
lean_ctor_set(v___x_544_, 9, v_currMacroScope_535_);
lean_ctor_set(v___x_544_, 10, v_cancelTk_x3f_536_);
lean_ctor_set(v___x_544_, 11, v_inheritedTraceOptions_537_);
lean_inc(v_ref_539_);
v___x_545_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_currRecDepth_538_);
lean_ctor_set(v___x_545_, 2, v_ref_539_);
lean_ctor_set_uint16(v___x_545_, sizeof(void*)*3, v___x_373_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*3 + 2, v_suppressElabErrors_540_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*3 + 3, v_isRecordingDeps_541_);
lean_inc(v___x_384_);
v___y_515_ = v___x_542_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_384_;
v___y_518_ = v_opts_333_;
goto v___jp_514_;
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v_env_552_; lean_object* v_nextMacroScope_553_; lean_object* v_ngen_554_; lean_object* v_auxDeclNGen_555_; lean_object* v_traceState_556_; lean_object* v_recordedDeps_557_; lean_object* v_messages_558_; lean_object* v_infoState_559_; lean_object* v_snapshotTasks_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v___x_551_ = lean_st_ref_take(v___x_384_);
v_env_552_ = lean_ctor_get(v___x_551_, 0);
v_nextMacroScope_553_ = lean_ctor_get(v___x_551_, 1);
v_ngen_554_ = lean_ctor_get(v___x_551_, 2);
v_auxDeclNGen_555_ = lean_ctor_get(v___x_551_, 3);
v_traceState_556_ = lean_ctor_get(v___x_551_, 4);
v_recordedDeps_557_ = lean_ctor_get(v___x_551_, 6);
v_messages_558_ = lean_ctor_get(v___x_551_, 7);
v_infoState_559_ = lean_ctor_get(v___x_551_, 8);
v_snapshotTasks_560_ = lean_ctor_get(v___x_551_, 9);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v___x_551_, 5);
lean_dec(v_unused_570_);
v___x_562_ = v___x_551_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snapshotTasks_560_);
lean_inc(v_infoState_559_);
lean_inc(v_messages_558_);
lean_inc(v_recordedDeps_557_);
lean_inc(v_traceState_556_);
lean_inc(v_auxDeclNGen_555_);
lean_inc(v_ngen_554_);
lean_inc(v_nextMacroScope_553_);
lean_inc(v_env_552_);
lean_dec(v___x_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = l_Lean_Kernel_enableDiag(v_env_552_, v___y_550_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 5, v___x_378_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_nextMacroScope_553_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_ngen_554_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_auxDeclNGen_555_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_traceState_556_);
lean_ctor_set(v_reuseFailAlloc_568_, 5, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_568_, 6, v_recordedDeps_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 7, v_messages_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 8, v_infoState_559_);
lean_ctor_set(v_reuseFailAlloc_568_, 9, v_snapshotTasks_560_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_st_ref_put(v___x_384_, v___x_566_);
v_fileName_528_ = v_fileName_351_;
v_fileMap_529_ = v_fileMap_352_;
v_currNamespace_530_ = v_currNamespace_365_;
v_openDecls_531_ = v_openDecls_366_;
v_initHeartbeats_532_ = v___x_383_;
v_maxHeartbeats_533_ = v___x_369_;
v_quotContext_534_ = v___x_370_;
v_currMacroScope_535_ = v___x_371_;
v_cancelTk_x3f_536_ = v_cancelTk_x3f_354_;
v_inheritedTraceOptions_537_ = v___x_547_;
v_currRecDepth_538_ = v___x_344_;
v_ref_539_ = v___x_372_;
v_suppressElabErrors_540_ = v___x_340_;
v_isRecordingDeps_541_ = v___x_340_;
goto v___jp_527_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_330_ = stack[0].m_obj;
lean_object* v_mctx_331_ = stack[1].m_obj;
lean_object* v_lctx_332_ = stack[2].m_obj;
lean_object* v_opts_333_ = stack[3].m_obj;
lean_object* v_namingCtx_334_ = stack[4].m_obj;
lean_object* v_x_335_ = stack[5].m_obj;
lean_object* v_a_336_ = stack[6].m_obj;
lean_object* v_a_337_ = stack[7].m_obj;
lean_object* v_res_574_;
v_res_574_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_330_, v_mctx_331_, v_lctx_332_, v_opts_333_, v_namingCtx_334_, v_x_335_, v_a_336_, v_a_337_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_575_, lean_object* v_mctx_576_, lean_object* v_lctx_577_, lean_object* v_opts_578_, lean_object* v_namingCtx_579_, lean_object* v_x_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_575_, v_mctx_576_, v_lctx_577_, v_opts_578_, v_namingCtx_579_, v_x_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_584_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_585_, lean_object* v_env_586_, lean_object* v_mctx_587_, lean_object* v_lctx_588_, lean_object* v_opts_589_, lean_object* v_namingCtx_590_, lean_object* v_x_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_586_, v_mctx_587_, v_lctx_588_, v_opts_589_, v_namingCtx_590_, v_x_591_, v_a_592_, v_a_593_);
return v___x_595_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_586_ = stack[1].m_obj;
lean_object* v_mctx_587_ = stack[2].m_obj;
lean_object* v_lctx_588_ = stack[3].m_obj;
lean_object* v_opts_589_ = stack[4].m_obj;
lean_object* v_namingCtx_590_ = stack[5].m_obj;
lean_object* v_x_591_ = stack[6].m_obj;
lean_object* v_a_592_ = stack[7].m_obj;
lean_object* v_a_593_ = stack[8].m_obj;
lean_object* v_res_596_;
v_res_596_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_box(0), v_env_586_, v_mctx_587_, v_lctx_588_, v_opts_589_, v_namingCtx_590_, v_x_591_, v_a_592_, v_a_593_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_597_, lean_object* v_env_598_, lean_object* v_mctx_599_, lean_object* v_lctx_600_, lean_object* v_opts_601_, lean_object* v_namingCtx_602_, lean_object* v_x_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_597_, v_env_598_, v_mctx_599_, v_lctx_600_, v_opts_601_, v_namingCtx_602_, v_x_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
return v_res_607_;
}
}
uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_611_){
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
lean_dec(v_pre_615_);
lean_dec_ref_known(v_pre_614_, 2);
lean_dec_ref_known(v_pre_613_, 2);
lean_dec_ref_known(v___x_612_, 2);
v___x_632_ = 0;
return v___x_632_;
}
}
else
{
uint8_t v___x_633_; 
lean_dec_ref_known(v_pre_613_, 2);
lean_dec(v_pre_614_);
lean_dec_ref_known(v___x_612_, 2);
v___x_633_ = 0;
return v___x_633_;
}
}
else
{
uint8_t v___x_634_; 
lean_dec_ref_known(v___x_612_, 2);
lean_dec(v_pre_613_);
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
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_611_ = stack[0].m_obj;
uint8_t v_res_636_;
v_res_636_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_611_);
stack->m_num = v_res_636_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_637_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(lean_object* v_x_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_tag_nat(v_x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl___boxed(lean_object* v_x_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(v_x_642_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_712_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
lean_inc(v_p_710_);
v___x_713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v_p_710_);
lean_ctor_set(v___x_713_, 2, v___x_712_);
lean_ctor_set(v___x_713_, 3, v_p_710_);
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_711_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_start_718_; lean_object* v_stop_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v___x_716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
v_start_718_ = lean_ctor_get(v_range_715_, 0);
v_stop_719_ = lean_ctor_get(v_range_715_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_range_715_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v_range_715_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_stop_719_);
lean_inc(v_start_718_);
lean_dec(v_range_715_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_723_, 0, v___x_717_);
lean_ctor_set(v___x_723_, 1, v_start_718_);
lean_ctor_set(v___x_723_, 2, v___x_717_);
lean_ctor_set(v___x_723_, 3, v_stop_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 2);
lean_ctor_set(v___x_721_, 1, v___x_716_);
lean_ctor_set(v___x_721_, 0, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_716_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_728_, lean_object* v_nc_x3f_729_, lean_object* v_msg_730_, lean_object* v_acc_731_){
_start:
{
switch(lean_obj_tag(v_msg_730_))
{
case 3:
{
lean_object* v_a_732_; lean_object* v_a_733_; lean_object* v___x_734_; 
lean_dec(v_mc_x3f_728_);
v_a_732_ = lean_ctor_get(v_msg_730_, 0);
v_a_733_ = lean_ctor_get(v_msg_730_, 1);
lean_inc_ref(v_a_732_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v_a_732_);
v_mc_x3f_728_ = v___x_734_;
v_msg_730_ = v_a_733_;
goto _start;
}
case 4:
{
lean_object* v_a_736_; lean_object* v_a_737_; lean_object* v___x_738_; 
lean_dec(v_nc_x3f_729_);
v_a_736_ = lean_ctor_get(v_msg_730_, 0);
v_a_737_ = lean_ctor_get(v_msg_730_, 1);
lean_inc_ref(v_a_736_);
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v_a_736_);
v_nc_x3f_729_ = v___x_738_;
v_msg_730_ = v_a_737_;
goto _start;
}
case 5:
{
lean_object* v_a_740_; 
v_a_740_ = lean_ctor_get(v_msg_730_, 1);
v_msg_730_ = v_a_740_;
goto _start;
}
case 6:
{
lean_object* v_a_742_; 
v_a_742_ = lean_ctor_get(v_msg_730_, 0);
v_msg_730_ = v_a_742_;
goto _start;
}
case 8:
{
lean_object* v_a_744_; 
v_a_744_ = lean_ctor_get(v_msg_730_, 1);
v_msg_730_ = v_a_744_;
goto _start;
}
case 7:
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_746_ = lean_ctor_get(v_msg_730_, 0);
v_a_747_ = lean_ctor_get(v_msg_730_, 1);
lean_inc(v_nc_x3f_729_);
lean_inc(v_mc_x3f_728_);
v___x_748_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_728_, v_nc_x3f_729_, v_a_746_, v_acc_731_);
v_msg_730_ = v_a_747_;
v_acc_731_ = v___x_748_;
goto _start;
}
case 2:
{
lean_object* v_a_750_; 
v_a_750_ = lean_ctor_get(v_msg_730_, 1);
v_msg_730_ = v_a_750_;
goto _start;
}
case 9:
{
lean_object* v_msg_752_; lean_object* v_children_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_msg_752_ = lean_ctor_get(v_msg_730_, 1);
v_children_753_ = lean_ctor_get(v_msg_730_, 2);
lean_inc(v_nc_x3f_729_);
lean_inc(v_mc_x3f_728_);
v___x_754_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_728_, v_nc_x3f_729_, v_msg_752_, v_acc_731_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_array_get_size(v_children_753_);
v___x_757_ = lean_nat_dec_lt(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v_nc_x3f_729_);
lean_dec(v_mc_x3f_728_);
return v___x_754_;
}
else
{
uint8_t v___x_758_; 
v___x_758_ = lean_nat_dec_le(v___x_756_, v___x_756_);
if (v___x_758_ == 0)
{
if (v___x_757_ == 0)
{
lean_dec(v_nc_x3f_729_);
lean_dec(v_mc_x3f_728_);
return v___x_754_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_756_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_728_, v_nc_x3f_729_, v_children_753_, v___x_759_, v___x_760_, v___x_754_);
return v___x_761_;
}
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_756_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_728_, v_nc_x3f_729_, v_children_753_, v___x_762_, v___x_763_, v___x_754_);
return v___x_764_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_728_) == 1)
{
if (lean_obj_tag(v_nc_x3f_729_) == 1)
{
lean_object* v_a_765_; lean_object* v_val_766_; lean_object* v_val_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_a_765_ = lean_ctor_get(v_msg_730_, 0);
v_val_766_ = lean_ctor_get(v_mc_x3f_728_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v_mc_x3f_728_, 1);
v_val_767_ = lean_ctor_get(v_nc_x3f_729_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v_nc_x3f_729_, 1);
lean_inc(v_a_765_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_val_767_);
lean_ctor_set(v___x_768_, 1, v_a_765_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_val_766_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_array_push(v_acc_731_, v___x_769_);
return v___x_770_;
}
else
{
lean_dec_ref_known(v_mc_x3f_728_, 1);
lean_dec(v_nc_x3f_729_);
return v_acc_731_;
}
}
else
{
lean_dec(v_nc_x3f_729_);
lean_dec(v_mc_x3f_728_);
return v_acc_731_;
}
}
default: 
{
lean_dec(v_nc_x3f_729_);
lean_dec(v_mc_x3f_728_);
return v_acc_731_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_771_, lean_object* v_nc_x3f_772_, lean_object* v_as_773_, size_t v_i_774_, size_t v_stop_775_, lean_object* v_b_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_eq(v_i_774_, v_stop_775_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; 
v___x_778_ = lean_array_uget_borrowed(v_as_773_, v_i_774_);
lean_inc(v_nc_x3f_772_);
lean_inc(v_mc_x3f_771_);
v___x_779_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_771_, v_nc_x3f_772_, v___x_778_, v_b_776_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_774_, v___x_780_);
v_i_774_ = v___x_781_;
v_b_776_ = v___x_779_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_772_);
lean_dec(v_mc_x3f_771_);
return v_b_776_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mc_x3f_771_ = stack[0].m_obj;
lean_object* v_nc_x3f_772_ = stack[1].m_obj;
lean_object* v_as_773_ = stack[2].m_obj;
size_t v_i_774_ = stack[3].m_num;
size_t v_stop_775_ = stack[4].m_num;
lean_object* v_b_776_ = stack[5].m_obj;
lean_object* v_res_783_;
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_771_, v_nc_x3f_772_, v_as_773_, v_i_774_, v_stop_775_, v_b_776_);
stack->m_obj
 = v_res_783_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_784_, lean_object* v_nc_x3f_785_, lean_object* v_as_786_, lean_object* v_i_787_, lean_object* v_stop_788_, lean_object* v_b_789_){
_start:
{
size_t v_i_boxed_790_; size_t v_stop_boxed_791_; lean_object* v_res_792_; 
v_i_boxed_790_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_stop_boxed_791_ = lean_unbox_usize(v_stop_788_);
lean_dec(v_stop_788_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_784_, v_nc_x3f_785_, v_as_786_, v_i_boxed_790_, v_stop_boxed_791_, v_b_789_);
lean_dec_ref(v_as_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_793_, lean_object* v_nc_x3f_794_, lean_object* v_msg_795_, lean_object* v_acc_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_793_, v_nc_x3f_794_, v_msg_795_, v_acc_796_);
lean_dec_ref(v_msg_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_box(0);
v___x_802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_803_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_801_, v___x_801_, v_msg_800_, v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_804_);
lean_dec_ref(v_msg_804_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_808_, lean_object* v_stx_809_){
_start:
{
lean_object* v___x_810_; 
lean_inc(v_stx_809_);
v___x_810_ = l_Lean_Syntax_getKind(v_stx_809_);
if (lean_obj_tag(v___x_810_) == 1)
{
lean_object* v_pre_811_; 
v_pre_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_pre_811_);
if (lean_obj_tag(v_pre_811_) == 1)
{
lean_object* v_pre_812_; 
v_pre_812_ = lean_ctor_get(v_pre_811_, 0);
lean_inc(v_pre_812_);
if (lean_obj_tag(v_pre_812_) == 1)
{
lean_object* v_pre_813_; 
v_pre_813_ = lean_ctor_get(v_pre_812_, 0);
lean_inc(v_pre_813_);
if (lean_obj_tag(v_pre_813_) == 1)
{
lean_object* v_pre_814_; 
v_pre_814_ = lean_ctor_get(v_pre_813_, 0);
if (lean_obj_tag(v_pre_814_) == 0)
{
lean_object* v_str_815_; lean_object* v_str_816_; lean_object* v_str_817_; lean_object* v_str_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_str_815_ = lean_ctor_get(v___x_810_, 1);
lean_inc_ref(v_str_815_);
lean_dec_ref_known(v___x_810_, 2);
v_str_816_ = lean_ctor_get(v_pre_811_, 1);
lean_inc_ref(v_str_816_);
lean_dec_ref_known(v_pre_811_, 2);
v_str_817_ = lean_ctor_get(v_pre_812_, 1);
lean_inc_ref(v_str_817_);
lean_dec_ref_known(v_pre_812_, 2);
v_str_818_ = lean_ctor_get(v_pre_813_, 1);
lean_inc_ref(v_str_818_);
lean_dec_ref_known(v_pre_813_, 2);
v___x_819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_820_ = lean_string_dec_eq(v_str_818_, v___x_819_);
lean_dec_ref(v_str_818_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec_ref(v_str_817_);
lean_dec_ref(v_str_816_);
lean_dec_ref(v_str_815_);
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_821_ = lean_box(0);
return v___x_821_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_823_ = lean_string_dec_eq(v_str_817_, v___x_822_);
lean_dec_ref(v_str_817_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
lean_dec_ref(v_str_816_);
lean_dec_ref(v_str_815_);
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_824_ = lean_box(0);
return v___x_824_;
}
else
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_826_ = lean_string_dec_eq(v_str_816_, v___x_825_);
lean_dec_ref(v_str_816_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_dec_ref(v_str_815_);
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_827_ = lean_box(0);
return v___x_827_;
}
else
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_829_ = lean_string_dec_eq(v_str_815_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_831_ = lean_string_dec_eq(v_str_815_, v___x_830_);
lean_dec_ref(v_str_815_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v_body_834_; lean_object* v___y_836_; lean_object* v___x_839_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v_body_834_ = l_Lean_Syntax_getArg(v_stx_809_, v___x_833_);
v___x_839_ = l_Lean_Syntax_getTailPos_x3f(v_body_834_, v___x_829_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_unsigned_to_nat(2u);
v___x_841_ = l_Lean_Syntax_getArg(v_stx_809_, v___x_840_);
lean_dec(v_stx_809_);
v___x_842_ = l_Lean_Syntax_getPos_x3f(v___x_841_, v___x_829_);
lean_dec(v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_stop_843_; 
v_stop_843_ = lean_ctor_get(v_range_808_, 1);
lean_inc(v_stop_843_);
lean_dec_ref(v_range_808_);
v___y_836_ = v_stop_843_;
goto v___jp_835_;
}
else
{
lean_object* v_val_844_; 
lean_dec_ref(v_range_808_);
v_val_844_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v___x_842_, 1);
v___y_836_ = v_val_844_;
goto v___jp_835_;
}
}
else
{
lean_object* v_val_845_; 
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v_val_845_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_845_);
lean_dec_ref_known(v___x_839_, 1);
v___y_836_ = v_val_845_;
goto v___jp_835_;
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_body_834_);
lean_ctor_set(v___x_837_, 1, v___y_836_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
}
else
{
lean_object* v___x_846_; lean_object* v_body_847_; lean_object* v___y_849_; uint8_t v___x_852_; lean_object* v___x_853_; 
lean_dec_ref(v_str_815_);
v___x_846_ = lean_unsigned_to_nat(0u);
v_body_847_ = l_Lean_Syntax_getArg(v_stx_809_, v___x_846_);
lean_dec(v_stx_809_);
v___x_852_ = 0;
v___x_853_ = l_Lean_Syntax_getTailPos_x3f(v_body_847_, v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_stop_854_; 
v_stop_854_ = lean_ctor_get(v_range_808_, 1);
lean_inc(v_stop_854_);
lean_dec_ref(v_range_808_);
v___y_849_ = v_stop_854_;
goto v___jp_848_;
}
else
{
lean_object* v_val_855_; 
lean_dec_ref(v_range_808_);
v_val_855_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v___x_853_, 1);
v___y_849_ = v_val_855_;
goto v___jp_848_;
}
v___jp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_body_847_);
lean_ctor_set(v___x_850_, 1, v___y_849_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
}
}
}
}
else
{
lean_object* v___x_856_; 
lean_dec_ref_known(v_pre_813_, 2);
lean_dec_ref_known(v_pre_812_, 2);
lean_dec_ref_known(v_pre_811_, 2);
lean_dec_ref_known(v___x_810_, 2);
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_856_ = lean_box(0);
return v___x_856_;
}
}
else
{
lean_object* v___x_857_; 
lean_dec_ref_known(v_pre_812_, 2);
lean_dec(v_pre_813_);
lean_dec_ref_known(v_pre_811_, 2);
lean_dec_ref_known(v___x_810_, 2);
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_857_ = lean_box(0);
return v___x_857_;
}
}
else
{
lean_object* v___x_858_; 
lean_dec_ref_known(v_pre_811_, 2);
lean_dec(v_pre_812_);
lean_dec_ref_known(v___x_810_, 2);
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_858_ = lean_box(0);
return v___x_858_;
}
}
else
{
lean_object* v___x_859_; 
lean_dec(v_pre_811_);
lean_dec_ref_known(v___x_810_, 2);
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_859_ = lean_box(0);
return v___x_859_;
}
}
else
{
lean_object* v___x_860_; 
lean_dec(v___x_810_);
lean_dec(v_stx_809_);
lean_dec_ref(v_range_808_);
v___x_860_ = lean_box(0);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_864_, lean_object* v_stx_865_){
_start:
{
lean_object* v___x_866_; 
lean_inc(v_stx_865_);
lean_inc_ref(v_range_864_);
v___x_866_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_864_, v_stx_865_);
if (lean_obj_tag(v___x_866_) == 1)
{
lean_dec(v_stx_865_);
lean_dec_ref(v_range_864_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; size_t v_sz_870_; size_t v___x_871_; lean_object* v___x_872_; lean_object* v_fst_873_; 
lean_dec(v___x_866_);
v___x_867_ = l_Lean_Syntax_getArgs(v_stx_865_);
lean_dec(v_stx_865_);
v___x_868_ = lean_box(0);
v___x_869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_870_ = lean_array_size(v___x_867_);
v___x_871_ = ((size_t)0ULL);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_864_, v___x_867_, v_sz_870_, v___x_871_, v___x_869_);
lean_dec_ref(v___x_867_);
v_fst_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_fst_873_);
lean_dec_ref(v___x_872_);
if (lean_obj_tag(v_fst_873_) == 0)
{
return v___x_868_;
}
else
{
lean_object* v_val_874_; 
v_val_874_ = lean_ctor_get(v_fst_873_, 0);
lean_inc(v_val_874_);
lean_dec_ref_known(v_fst_873_, 1);
return v_val_874_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_875_, lean_object* v_as_876_, size_t v_sz_877_, size_t v_i_878_, lean_object* v_b_879_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = lean_usize_dec_lt(v_i_878_, v_sz_877_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_range_875_);
lean_inc_ref(v_b_879_);
return v_b_879_;
}
else
{
lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v___x_883_; 
v___x_881_ = lean_box(0);
v_a_882_ = lean_array_uget_borrowed(v_as_876_, v_i_878_);
lean_inc(v_a_882_);
lean_inc_ref(v_range_875_);
v___x_883_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_875_, v_a_882_);
if (lean_obj_tag(v___x_883_) == 1)
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec_ref(v_range_875_);
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_881_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; size_t v___x_887_; size_t v___x_888_; 
lean_dec(v___x_883_);
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_add(v_i_878_, v___x_887_);
v_i_878_ = v___x_888_;
v_b_879_ = v___x_886_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_875_ = stack[0].m_obj;
lean_object* v_as_876_ = stack[1].m_obj;
size_t v_sz_877_ = stack[2].m_num;
size_t v_i_878_ = stack[3].m_num;
lean_object* v_b_879_ = stack[4].m_obj;
lean_object* v_res_890_;
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_875_, v_as_876_, v_sz_877_, v_i_878_, v_b_879_);
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_891_, lean_object* v_as_892_, lean_object* v_sz_893_, lean_object* v_i_894_, lean_object* v_b_895_){
_start:
{
size_t v_sz_boxed_896_; size_t v_i_boxed_897_; lean_object* v_res_898_; 
v_sz_boxed_896_ = lean_unbox_usize(v_sz_893_);
lean_dec(v_sz_893_);
v_i_boxed_897_ = lean_unbox_usize(v_i_894_);
lean_dec(v_i_894_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_891_, v_as_892_, v_sz_boxed_896_, v_i_boxed_897_, v_b_895_);
lean_dec_ref(v_b_895_);
lean_dec_ref(v_as_892_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_899_, lean_object* v_stx_900_){
_start:
{
uint8_t v___x_901_; lean_object* v___x_902_; 
v___x_901_ = 0;
v___x_902_ = l_Lean_Syntax_getRange_x3f(v_stx_900_, v___x_901_);
if (lean_obj_tag(v___x_902_) == 1)
{
lean_object* v_val_903_; uint8_t v___x_904_; 
v_val_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_val_903_);
lean_dec_ref_known(v___x_902_, 1);
v___x_904_ = l_Lean_Syntax_Range_includes(v_val_903_, v_range_899_, v___x_901_, v___x_901_);
lean_dec(v_val_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
lean_dec(v_stx_900_);
lean_dec_ref(v_range_899_);
v___x_905_ = lean_box(0);
return v___x_905_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; size_t v_sz_908_; size_t v___x_909_; lean_object* v___x_910_; lean_object* v_fst_911_; 
v___x_906_ = l_Lean_Syntax_getArgs(v_stx_900_);
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_908_ = lean_array_size(v___x_906_);
v___x_909_ = ((size_t)0ULL);
lean_inc_ref(v_range_899_);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_899_, v___x_906_, v_sz_908_, v___x_909_, v___x_907_);
lean_dec_ref(v___x_906_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_fst_911_);
lean_dec_ref(v___x_910_);
if (lean_obj_tag(v_fst_911_) == 0)
{
lean_object* v___x_912_; 
v___x_912_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_899_, v_stx_900_);
return v___x_912_;
}
else
{
lean_object* v_val_913_; 
lean_dec(v_stx_900_);
lean_dec_ref(v_range_899_);
v_val_913_ = lean_ctor_get(v_fst_911_, 0);
lean_inc(v_val_913_);
lean_dec_ref_known(v_fst_911_, 1);
return v_val_913_;
}
}
}
else
{
lean_object* v___x_914_; 
lean_dec(v___x_902_);
lean_dec(v_stx_900_);
lean_dec_ref(v_range_899_);
v___x_914_ = lean_box(0);
return v___x_914_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_915_, lean_object* v_as_916_, size_t v_sz_917_, size_t v_i_918_, lean_object* v_b_919_){
_start:
{
uint8_t v___x_920_; 
v___x_920_ = lean_usize_dec_lt(v_i_918_, v_sz_917_);
if (v___x_920_ == 0)
{
lean_dec_ref(v_range_915_);
lean_inc_ref(v_b_919_);
return v_b_919_;
}
else
{
lean_object* v___x_921_; lean_object* v_a_922_; lean_object* v___x_923_; 
v___x_921_ = lean_box(0);
v_a_922_ = lean_array_uget_borrowed(v_as_916_, v_i_918_);
lean_inc(v_a_922_);
lean_inc_ref(v_range_915_);
v___x_923_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_915_, v_a_922_);
if (lean_obj_tag(v___x_923_) == 1)
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec_ref(v_range_915_);
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_921_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; size_t v___x_927_; size_t v___x_928_; 
lean_dec(v___x_923_);
v___x_926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_add(v_i_918_, v___x_927_);
v_i_918_ = v___x_928_;
v_b_919_ = v___x_926_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_915_ = stack[0].m_obj;
lean_object* v_as_916_ = stack[1].m_obj;
size_t v_sz_917_ = stack[2].m_num;
size_t v_i_918_ = stack[3].m_num;
lean_object* v_b_919_ = stack[4].m_obj;
lean_object* v_res_930_;
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_915_, v_as_916_, v_sz_917_, v_i_918_, v_b_919_);
stack->m_obj
 = v_res_930_;
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
uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_opts_942_, lean_object* v_opt_943_){
_start:
{
lean_object* v_name_944_; lean_object* v_defValue_945_; lean_object* v_map_946_; lean_object* v___x_947_; 
v_name_944_ = lean_ctor_get(v_opt_943_, 0);
v_defValue_945_ = lean_ctor_get(v_opt_943_, 1);
v_map_946_ = lean_ctor_get(v_opts_942_, 0);
v___x_947_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_946_, v_name_944_);
if (lean_obj_tag(v___x_947_) == 0)
{
uint8_t v___x_948_; 
v___x_948_ = lean_unbox(v_defValue_945_);
return v___x_948_;
}
else
{
lean_object* v_val_949_; 
v_val_949_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_val_949_);
lean_dec_ref_known(v___x_947_, 1);
if (lean_obj_tag(v_val_949_) == 1)
{
uint8_t v_v_950_; 
v_v_950_ = lean_ctor_get_uint8(v_val_949_, 0);
lean_dec_ref_known(v_val_949_, 0);
return v_v_950_;
}
else
{
uint8_t v___x_951_; 
lean_dec(v_val_949_);
v___x_951_ = lean_unbox(v_defValue_945_);
return v___x_951_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_942_ = stack[0].m_obj;
lean_object* v_opt_943_ = stack[1].m_obj;
uint8_t v_res_952_;
v_res_952_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_942_, v_opt_943_);
stack->m_num = v_res_952_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_opts_953_, lean_object* v_opt_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_953_, v_opt_954_);
lean_dec_ref(v_opt_954_);
lean_dec_ref(v_opts_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_957_, lean_object* v_info_958_, lean_object* v_acc_959_){
_start:
{
if (lean_obj_tag(v_info_958_) == 0)
{
lean_object* v_i_960_; lean_object* v_toElabInfo_961_; lean_object* v_mctxBefore_962_; lean_object* v_goalsBefore_963_; lean_object* v_stx_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_982_; 
v_i_960_ = lean_ctor_get(v_info_958_, 0);
lean_inc_ref(v_i_960_);
lean_dec_ref_known(v_info_958_, 1);
v_toElabInfo_961_ = lean_ctor_get(v_i_960_, 0);
lean_inc_ref(v_toElabInfo_961_);
v_mctxBefore_962_ = lean_ctor_get(v_i_960_, 1);
lean_inc_ref(v_mctxBefore_962_);
v_goalsBefore_963_ = lean_ctor_get(v_i_960_, 2);
lean_inc(v_goalsBefore_963_);
lean_dec_ref(v_i_960_);
v_stx_964_ = lean_ctor_get(v_toElabInfo_961_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_toElabInfo_961_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_toElabInfo_961_, 0);
lean_dec(v_unused_983_);
v___x_966_ = v_toElabInfo_961_;
v_isShared_967_ = v_isSharedCheck_982_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_stx_964_);
lean_dec(v_toElabInfo_961_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_982_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint8_t v___x_968_; 
lean_inc(v_stx_964_);
v___x_968_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_964_);
if (v___x_968_ == 0)
{
lean_del_object(v___x_966_);
lean_dec(v_stx_964_);
lean_dec(v_goalsBefore_963_);
lean_dec_ref(v_mctxBefore_962_);
return v_acc_959_;
}
else
{
lean_object* v___x_969_; 
v___x_969_ = l_List_head_x3f___redArg(v_goalsBefore_963_);
lean_dec(v_goalsBefore_963_);
if (lean_obj_tag(v___x_969_) == 1)
{
lean_object* v_toCommandContextInfo_970_; lean_object* v_val_971_; lean_object* v_env_972_; lean_object* v_options_973_; lean_object* v_currNamespace_974_; lean_object* v_openDecls_975_; lean_object* v_namingCtx_977_; 
v_toCommandContextInfo_970_ = lean_ctor_get(v_ctx_957_, 0);
v_val_971_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v___x_969_, 1);
v_env_972_ = lean_ctor_get(v_toCommandContextInfo_970_, 0);
v_options_973_ = lean_ctor_get(v_toCommandContextInfo_970_, 4);
v_currNamespace_974_ = lean_ctor_get(v_toCommandContextInfo_970_, 5);
v_openDecls_975_ = lean_ctor_get(v_toCommandContextInfo_970_, 6);
lean_inc(v_openDecls_975_);
lean_inc(v_currNamespace_974_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v_openDecls_975_);
lean_ctor_set(v___x_966_, 0, v_currNamespace_974_);
v_namingCtx_977_ = v___x_966_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_currNamespace_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_openDecls_975_);
v_namingCtx_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_box(1);
lean_inc_ref(v_options_973_);
lean_inc_ref(v_env_972_);
v___x_979_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v_stx_964_);
lean_ctor_set(v___x_979_, 2, v_env_972_);
lean_ctor_set(v___x_979_, 3, v_mctxBefore_962_);
lean_ctor_set(v___x_979_, 4, v_options_973_);
lean_ctor_set(v___x_979_, 5, v_namingCtx_977_);
lean_ctor_set(v___x_979_, 6, v_val_971_);
v___x_980_ = lean_array_push(v_acc_959_, v___x_979_);
return v___x_980_;
}
}
else
{
lean_dec(v___x_969_);
lean_del_object(v___x_966_);
lean_dec(v_stx_964_);
lean_dec_ref(v_mctxBefore_962_);
return v_acc_959_;
}
}
}
}
else
{
lean_dec_ref(v_info_958_);
return v_acc_959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_984_, lean_object* v_info_985_, lean_object* v_acc_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_984_, v_info_985_, v_acc_986_);
lean_dec_ref(v_ctx_984_);
return v_res_987_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1));
v___x_994_ = lean_name_eq(v_x_992_, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_992_ = stack[0].m_obj;
uint8_t v_res_995_;
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(v_x_992_);
stack->m_num = v_res_995_;
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(lean_object* v_a_999_, lean_object* v_x_1000_){
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
lean_object* v_key_1002_; lean_object* v_tail_1003_; uint8_t v___y_1005_; lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v_fst_1009_; lean_object* v_snd_1010_; uint8_t v___x_1011_; 
v_key_1002_ = lean_ctor_get(v_x_1000_, 0);
v_tail_1003_ = lean_ctor_get(v_x_1000_, 2);
v_fst_1007_ = lean_ctor_get(v_key_1002_, 0);
v_snd_1008_ = lean_ctor_get(v_key_1002_, 1);
v_fst_1009_ = lean_ctor_get(v_a_999_, 0);
v_snd_1010_ = lean_ctor_get(v_a_999_, 1);
v___x_1011_ = l_Lean_Syntax_instBEqRange_beq(v_fst_1007_, v_fst_1009_);
if (v___x_1011_ == 0)
{
v___y_1005_ = v___x_1011_;
goto v___jp_1004_;
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_instBEqMVarId_beq(v_snd_1008_, v_snd_1010_);
v___y_1005_ = v___x_1012_;
goto v___jp_1004_;
}
v___jp_1004_:
{
if (v___y_1005_ == 0)
{
v_x_1000_ = v_tail_1003_;
goto _start;
}
else
{
return v___y_1005_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_999_ = stack[0].m_obj;
lean_object* v_x_1000_ = stack[1].m_obj;
uint8_t v_res_1013_;
v_res_1013_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_999_, v_x_1000_);
stack->m_num = v_res_1013_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg___boxed(lean_object* v_a_1014_, lean_object* v_x_1015_){
_start:
{
uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_res_1016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1014_, v_x_1015_);
lean_dec(v_x_1015_);
lean_dec_ref(v_a_1014_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
return v_x_1018_;
}
else
{
lean_object* v_key_1020_; lean_object* v_value_1021_; lean_object* v_tail_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1049_; 
v_key_1020_ = lean_ctor_get(v_x_1019_, 0);
v_value_1021_ = lean_ctor_get(v_x_1019_, 1);
v_tail_1022_ = lean_ctor_get(v_x_1019_, 2);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1024_ = v_x_1019_;
v_isShared_1025_ = v_isSharedCheck_1049_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_tail_1022_);
lean_inc(v_value_1021_);
lean_inc(v_key_1020_);
lean_dec(v_x_1019_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1049_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_fst_1026_; lean_object* v_snd_1027_; lean_object* v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v_fold_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v_fst_1026_ = lean_ctor_get(v_key_1020_, 0);
v_snd_1027_ = lean_ctor_get(v_key_1020_, 1);
v___x_1028_ = lean_array_get_size(v_x_1018_);
v___x_1029_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1026_);
v___x_1030_ = l_Lean_instHashableMVarId_hash(v_snd_1027_);
v___x_1031_ = lean_uint64_mix_hash(v___x_1029_, v___x_1030_);
v___x_1032_ = 32ULL;
v___x_1033_ = lean_uint64_shift_right(v___x_1031_, v___x_1032_);
v_fold_1034_ = lean_uint64_xor(v___x_1031_, v___x_1033_);
v___x_1035_ = 16ULL;
v___x_1036_ = lean_uint64_shift_right(v_fold_1034_, v___x_1035_);
v___x_1037_ = lean_uint64_xor(v_fold_1034_, v___x_1036_);
v___x_1038_ = lean_uint64_to_usize(v___x_1037_);
v___x_1039_ = lean_usize_of_nat(v___x_1028_);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_sub(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_usize_land(v___x_1038_, v___x_1041_);
v___x_1043_ = lean_array_uget_borrowed(v_x_1018_, v___x_1042_);
lean_inc(v___x_1043_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 2, v___x_1043_);
v___x_1045_ = v___x_1024_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_key_1020_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_value_1021_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_array_uset(v_x_1018_, v___x_1042_, v___x_1045_);
v_x_1018_ = v___x_1046_;
v_x_1019_ = v_tail_1022_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1050_, lean_object* v_source_1051_, lean_object* v_target_1052_){
_start:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = lean_array_get_size(v_source_1051_);
v___x_1054_ = lean_nat_dec_lt(v_i_1050_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec_ref(v_source_1051_);
lean_dec(v_i_1050_);
return v_target_1052_;
}
else
{
lean_object* v_es_1055_; lean_object* v___x_1056_; lean_object* v_source_1057_; lean_object* v_target_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_es_1055_ = lean_array_fget(v_source_1051_, v_i_1050_);
v___x_1056_ = lean_box(0);
v_source_1057_ = lean_array_fset(v_source_1051_, v_i_1050_, v___x_1056_);
v_target_1058_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1052_, v_es_1055_);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_i_1050_, v___x_1059_);
lean_dec(v_i_1050_);
v_i_1050_ = v___x_1060_;
v_source_1051_ = v_source_1057_;
v_target_1052_ = v_target_1058_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(lean_object* v_data_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_nbuckets_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1063_ = lean_array_get_size(v_data_1062_);
v___x_1064_ = lean_unsigned_to_nat(2u);
v_nbuckets_1065_ = lean_nat_mul(v___x_1063_, v___x_1064_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_mk_array(v_nbuckets_1065_, v___x_1067_);
v___x_1069_ = lean_array_propagate_mark(v_data_1062_, v___x_1068_);
v___x_1070_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v___x_1066_, v_data_1062_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v_m_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_){
_start:
{
lean_object* v_size_1074_; lean_object* v_buckets_1075_; lean_object* v_fst_1076_; lean_object* v_snd_1077_; lean_object* v___x_1078_; uint64_t v___x_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v_fold_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v_bkt_1093_; uint8_t v___x_1094_; 
v_size_1074_ = lean_ctor_get(v_m_1071_, 0);
v_buckets_1075_ = lean_ctor_get(v_m_1071_, 1);
v_fst_1076_ = lean_ctor_get(v_a_1072_, 0);
v_snd_1077_ = lean_ctor_get(v_a_1072_, 1);
v___x_1078_ = lean_array_get_size(v_buckets_1075_);
v___x_1079_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1076_);
v___x_1080_ = l_Lean_instHashableMVarId_hash(v_snd_1077_);
v___x_1081_ = lean_uint64_mix_hash(v___x_1079_, v___x_1080_);
v___x_1082_ = 32ULL;
v___x_1083_ = lean_uint64_shift_right(v___x_1081_, v___x_1082_);
v_fold_1084_ = lean_uint64_xor(v___x_1081_, v___x_1083_);
v___x_1085_ = 16ULL;
v___x_1086_ = lean_uint64_shift_right(v_fold_1084_, v___x_1085_);
v___x_1087_ = lean_uint64_xor(v_fold_1084_, v___x_1086_);
v___x_1088_ = lean_uint64_to_usize(v___x_1087_);
v___x_1089_ = lean_usize_of_nat(v___x_1078_);
v___x_1090_ = ((size_t)1ULL);
v___x_1091_ = lean_usize_sub(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_usize_land(v___x_1088_, v___x_1091_);
v_bkt_1093_ = lean_array_uget_borrowed(v_buckets_1075_, v___x_1092_);
v___x_1094_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1072_, v_bkt_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1115_; 
lean_inc_ref(v_buckets_1075_);
lean_inc(v_size_1074_);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_m_1071_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; lean_object* v_unused_1117_; 
v_unused_1116_ = lean_ctor_get(v_m_1071_, 1);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_m_1071_, 0);
lean_dec(v_unused_1117_);
v___x_1096_ = v_m_1071_;
v_isShared_1097_ = v_isSharedCheck_1115_;
goto v_resetjp_1095_;
}
else
{
lean_dec(v_m_1071_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1115_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v_size_x27_1099_; lean_object* v___x_1100_; lean_object* v_buckets_x27_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1098_ = lean_unsigned_to_nat(1u);
v_size_x27_1099_ = lean_nat_add(v_size_1074_, v___x_1098_);
lean_dec(v_size_1074_);
lean_inc(v_bkt_1093_);
v___x_1100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1100_, 0, v_a_1072_);
lean_ctor_set(v___x_1100_, 1, v_b_1073_);
lean_ctor_set(v___x_1100_, 2, v_bkt_1093_);
v_buckets_x27_1101_ = lean_array_uset(v_buckets_1075_, v___x_1092_, v___x_1100_);
v___x_1102_ = lean_unsigned_to_nat(4u);
v___x_1103_ = lean_nat_mul(v_size_x27_1099_, v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(3u);
v___x_1105_ = lean_nat_div(v___x_1103_, v___x_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_array_get_size(v_buckets_x27_1101_);
v___x_1107_ = lean_nat_dec_le(v___x_1105_, v___x_1106_);
lean_dec(v___x_1105_);
if (v___x_1107_ == 0)
{
lean_object* v_val_1108_; lean_object* v___x_1110_; 
v_val_1108_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_buckets_x27_1101_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v_val_1108_);
lean_ctor_set(v___x_1096_, 0, v_size_x27_1099_);
v___x_1110_ = v___x_1096_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_size_x27_1099_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_val_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
lean_object* v___x_1113_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v_buckets_x27_1101_);
lean_ctor_set(v___x_1096_, 0, v_size_x27_1099_);
v___x_1113_ = v___x_1096_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_size_x27_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_buckets_x27_1101_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_dec(v_b_1073_);
lean_dec_ref(v_a_1072_);
return v_m_1071_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_buckets_1120_; lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1123_; uint64_t v___x_1124_; uint64_t v___x_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; uint64_t v___x_1128_; uint64_t v_fold_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_buckets_1120_ = lean_ctor_get(v_m_1118_, 1);
v_fst_1121_ = lean_ctor_get(v_a_1119_, 0);
v_snd_1122_ = lean_ctor_get(v_a_1119_, 1);
v___x_1123_ = lean_array_get_size(v_buckets_1120_);
v___x_1124_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1121_);
v___x_1125_ = l_Lean_instHashableMVarId_hash(v_snd_1122_);
v___x_1126_ = lean_uint64_mix_hash(v___x_1124_, v___x_1125_);
v___x_1127_ = 32ULL;
v___x_1128_ = lean_uint64_shift_right(v___x_1126_, v___x_1127_);
v_fold_1129_ = lean_uint64_xor(v___x_1126_, v___x_1128_);
v___x_1130_ = 16ULL;
v___x_1131_ = lean_uint64_shift_right(v_fold_1129_, v___x_1130_);
v___x_1132_ = lean_uint64_xor(v_fold_1129_, v___x_1131_);
v___x_1133_ = lean_uint64_to_usize(v___x_1132_);
v___x_1134_ = lean_usize_of_nat(v___x_1123_);
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = lean_usize_sub(v___x_1134_, v___x_1135_);
v___x_1137_ = lean_usize_land(v___x_1133_, v___x_1136_);
v___x_1138_ = lean_array_uget_borrowed(v_buckets_1120_, v___x_1137_);
v___x_1139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1119_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1118_ = stack[0].m_obj;
lean_object* v_a_1119_ = stack[1].m_obj;
uint8_t v_res_1140_;
v_res_1140_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1118_, v_a_1119_);
stack->m_num = v_res_1140_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object* v_m_1141_, lean_object* v_a_1142_){
_start:
{
uint8_t v_res_1143_; lean_object* v_r_1144_; 
v_res_1143_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1141_, v_a_1142_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_m_1141_);
v_r_1144_ = lean_box(v_res_1143_);
return v_r_1144_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object* v___x_1145_, lean_object* v_fst_1146_, lean_object* v_snd_1147_, lean_object* v___x_1148_, lean_object* v_as_1149_, size_t v_sz_1150_, size_t v_i_1151_, lean_object* v_b_1152_){
_start:
{
lean_object* v_a_1155_; uint8_t v___x_1159_; 
v___x_1159_ = lean_usize_dec_lt(v_i_1151_, v_sz_1150_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v___x_1148_);
lean_dec(v_snd_1147_);
lean_dec(v_fst_1146_);
lean_dec_ref(v___x_1145_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_b_1152_);
return v___x_1160_;
}
else
{
lean_object* v_a_1161_; lean_object* v_snd_1162_; lean_object* v_fst_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1199_; 
v_a_1161_ = lean_array_uget(v_as_1149_, v_i_1151_);
v_snd_1162_ = lean_ctor_get(v_a_1161_, 1);
v_fst_1163_ = lean_ctor_get(v_a_1161_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_a_1161_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1165_ = v_a_1161_;
v_isShared_1166_ = v_isSharedCheck_1199_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_snd_1162_);
lean_inc(v_fst_1163_);
lean_dec(v_a_1161_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1199_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1198_; 
v_fst_1167_ = lean_ctor_get(v_snd_1162_, 0);
v_snd_1168_ = lean_ctor_get(v_snd_1162_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_snd_1162_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1170_ = v_snd_1162_;
v_isShared_1171_ = v_isSharedCheck_1198_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snd_1168_);
lean_inc(v_fst_1167_);
lean_dec(v_snd_1162_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1198_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_fst_1172_; lean_object* v_snd_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1197_; 
v_fst_1172_ = lean_ctor_get(v_b_1152_, 0);
v_snd_1173_ = lean_ctor_get(v_b_1152_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_b_1152_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1175_ = v_b_1152_;
v_isShared_1176_ = v_isSharedCheck_1197_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_snd_1173_);
lean_inc(v_fst_1172_);
lean_dec(v_b_1152_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1197_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
lean_inc(v_snd_1168_);
lean_inc_ref(v___x_1145_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_snd_1168_);
lean_ctor_set(v___x_1175_, 0, v___x_1145_);
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_snd_1168_);
v___x_1178_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
uint8_t v___x_1179_; 
v___x_1179_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1173_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v_env_1180_; lean_object* v_mctx_1181_; lean_object* v_opts_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v_env_1180_ = lean_ctor_get(v_fst_1163_, 0);
lean_inc_ref(v_env_1180_);
v_mctx_1181_ = lean_ctor_get(v_fst_1163_, 1);
lean_inc_ref(v_mctx_1181_);
v_opts_1182_ = lean_ctor_get(v_fst_1163_, 3);
lean_inc_ref(v_opts_1182_);
lean_dec(v_fst_1163_);
v___x_1183_ = lean_box(0);
v___x_1184_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1173_, v___x_1178_, v___x_1183_);
lean_inc(v_snd_1147_);
lean_inc(v_fst_1146_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v_snd_1147_);
lean_ctor_set(v___x_1165_, 0, v_fst_1146_);
v___x_1186_ = v___x_1165_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_fst_1146_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_snd_1147_);
v___x_1186_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_inc(v___x_1148_);
v___x_1187_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1148_);
lean_ctor_set(v___x_1187_, 2, v_env_1180_);
lean_ctor_set(v___x_1187_, 3, v_mctx_1181_);
lean_ctor_set(v___x_1187_, 4, v_opts_1182_);
lean_ctor_set(v___x_1187_, 5, v_fst_1167_);
lean_ctor_set(v___x_1187_, 6, v_snd_1168_);
v___x_1188_ = lean_array_push(v_fst_1172_, v___x_1187_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1184_);
lean_ctor_set(v___x_1170_, 0, v___x_1188_);
v___x_1190_ = v___x_1170_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1184_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
v_a_1155_ = v___x_1190_;
goto v___jp_1154_;
}
}
}
else
{
lean_object* v___x_1194_; 
lean_dec_ref(v___x_1178_);
lean_dec(v_snd_1168_);
lean_dec(v_fst_1167_);
lean_del_object(v___x_1165_);
lean_dec(v_fst_1163_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_snd_1173_);
lean_ctor_set(v___x_1170_, 0, v_fst_1172_);
v___x_1194_ = v___x_1170_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_fst_1172_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_snd_1173_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
v_a_1155_ = v___x_1194_;
goto v___jp_1154_;
}
}
}
}
}
}
}
v___jp_1154_:
{
size_t v___x_1156_; size_t v___x_1157_; 
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_add(v_i_1151_, v___x_1156_);
v_i_1151_ = v___x_1157_;
v_b_1152_ = v_a_1155_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1145_ = stack[0].m_obj;
lean_object* v_fst_1146_ = stack[1].m_obj;
lean_object* v_snd_1147_ = stack[2].m_obj;
lean_object* v___x_1148_ = stack[3].m_obj;
lean_object* v_as_1149_ = stack[4].m_obj;
size_t v_sz_1150_ = stack[5].m_num;
size_t v_i_1151_ = stack[6].m_num;
lean_object* v_b_1152_ = stack[7].m_obj;
lean_object* v_res_1200_;
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1145_, v_fst_1146_, v_snd_1147_, v___x_1148_, v_as_1149_, v_sz_1150_, v_i_1151_, v_b_1152_);
stack->m_obj
 = v_res_1200_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object* v___x_1201_, lean_object* v_fst_1202_, lean_object* v_snd_1203_, lean_object* v___x_1204_, lean_object* v_as_1205_, lean_object* v_sz_1206_, lean_object* v_i_1207_, lean_object* v_b_1208_, lean_object* v___y_1209_){
_start:
{
size_t v_sz_boxed_1210_; size_t v_i_boxed_1211_; lean_object* v_res_1212_; 
v_sz_boxed_1210_ = lean_unbox_usize(v_sz_1206_);
lean_dec(v_sz_1206_);
v_i_boxed_1211_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_res_1212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1201_, v_fst_1202_, v_snd_1203_, v___x_1204_, v_as_1205_, v_sz_boxed_1210_, v_i_boxed_1211_, v_b_1208_);
lean_dec_ref(v_as_1205_);
return v_res_1212_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1215_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1216_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
lean_ctor_set(v___x_1218_, 2, v___x_1217_);
lean_ctor_set(v___x_1218_, 3, v___x_1217_);
lean_ctor_set(v___x_1218_, 4, v___x_1216_);
lean_ctor_set(v___x_1218_, 5, v___x_1216_);
lean_ctor_set(v___x_1218_, 6, v___x_1216_);
lean_ctor_set(v___x_1218_, 7, v___x_1216_);
lean_ctor_set(v___x_1218_, 8, v___x_1216_);
lean_ctor_set(v___x_1218_, 9, v___x_1216_);
lean_ctor_set(v___x_1218_, 10, v___x_1216_);
lean_ctor_set(v___x_1218_, 11, v___x_1215_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_unsigned_to_nat(32u);
v___x_1220_ = lean_mk_empty_array_with_capacity(v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1222_ = ((size_t)5ULL);
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_unsigned_to_nat(32u);
v___x_1225_ = lean_mk_empty_array_with_capacity(v___x_1224_);
v___x_1226_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2);
v___x_1227_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1225_);
lean_ctor_set(v___x_1227_, 2, v___x_1223_);
lean_ctor_set(v___x_1227_, 3, v___x_1223_);
lean_ctor_set_usize(v___x_1227_, 4, v___x_1222_);
return v___x_1227_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1228_ = lean_box(1);
v___x_1229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3);
v___x_1230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___x_1229_);
lean_ctor_set(v___x_1231_, 2, v___x_1228_);
return v___x_1231_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(lean_object* v_msgData_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_env_1236_; uint8_t v___x_1237_; lean_object* v_env_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_scopes_1241_; lean_object* v___x_1242_; lean_object* v_opts_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1235_ = lean_st_ref_get(v___y_1233_);
v_env_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc_ref(v_env_1236_);
lean_dec(v___x_1235_);
v___x_1237_ = 0;
v_env_1238_ = l_Lean_Environment_setRecordingDeps(v_env_1236_, v___x_1237_);
v___x_1239_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1240_ = lean_st_ref_get(v___y_1233_);
v_scopes_1241_ = lean_ctor_get(v___x_1240_, 2);
lean_inc(v_scopes_1241_);
lean_dec(v___x_1240_);
v___x_1242_ = l_List_head_x21___redArg(v___x_1239_, v_scopes_1241_);
lean_dec(v_scopes_1241_);
v_opts_1243_ = lean_ctor_get(v___x_1242_, 1);
lean_inc_ref(v_opts_1243_);
lean_dec(v___x_1242_);
v___x_1244_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1);
v___x_1245_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4);
v___x_1246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1246_, 0, v_env_1238_);
lean_ctor_set(v___x_1246_, 1, v___x_1244_);
lean_ctor_set(v___x_1246_, 2, v___x_1245_);
lean_ctor_set(v___x_1246_, 3, v_opts_1243_);
v___x_1247_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v_msgData_1232_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1232_ = stack[0].m_obj;
lean_object* v___y_1233_ = stack[1].m_obj;
lean_object* v_res_1249_;
v_res_1249_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_1232_, v___y_1233_);
stack->m_obj
 = v_res_1249_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_1250_, v___y_1251_);
lean_dec(v___y_1251_);
return v_res_1253_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1254_; double v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_float_of_nat(v___x_1254_);
return v___x_1255_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v_cls_1258_, lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_Elab_Command_getRef___redArg(v___y_1260_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1314_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msg_1259_, v___y_1261_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1314_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1314_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v_traceState_1271_; lean_object* v_env_1272_; lean_object* v_messages_1273_; lean_object* v_scopes_1274_; lean_object* v_usedQuotCtxts_1275_; lean_object* v_nextMacroScope_1276_; lean_object* v_maxRecDepth_1277_; lean_object* v_ngen_1278_; lean_object* v_auxDeclNGen_1279_; lean_object* v_infoState_1280_; lean_object* v_snapshotTasks_1281_; lean_object* v_prevLinterStates_1282_; lean_object* v_codeQualityEntryTasks_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1313_; 
v___x_1270_ = lean_st_ref_take(v___y_1261_);
v_traceState_1271_ = lean_ctor_get(v___x_1270_, 9);
v_env_1272_ = lean_ctor_get(v___x_1270_, 0);
v_messages_1273_ = lean_ctor_get(v___x_1270_, 1);
v_scopes_1274_ = lean_ctor_get(v___x_1270_, 2);
v_usedQuotCtxts_1275_ = lean_ctor_get(v___x_1270_, 3);
v_nextMacroScope_1276_ = lean_ctor_get(v___x_1270_, 4);
v_maxRecDepth_1277_ = lean_ctor_get(v___x_1270_, 5);
v_ngen_1278_ = lean_ctor_get(v___x_1270_, 6);
v_auxDeclNGen_1279_ = lean_ctor_get(v___x_1270_, 7);
v_infoState_1280_ = lean_ctor_get(v___x_1270_, 8);
v_snapshotTasks_1281_ = lean_ctor_get(v___x_1270_, 10);
v_prevLinterStates_1282_ = lean_ctor_get(v___x_1270_, 11);
v_codeQualityEntryTasks_1283_ = lean_ctor_get(v___x_1270_, 12);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1285_ = v___x_1270_;
v_isShared_1286_ = v_isSharedCheck_1313_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1283_);
lean_inc(v_prevLinterStates_1282_);
lean_inc(v_snapshotTasks_1281_);
lean_inc(v_traceState_1271_);
lean_inc(v_infoState_1280_);
lean_inc(v_auxDeclNGen_1279_);
lean_inc(v_ngen_1278_);
lean_inc(v_maxRecDepth_1277_);
lean_inc(v_nextMacroScope_1276_);
lean_inc(v_usedQuotCtxts_1275_);
lean_inc(v_scopes_1274_);
lean_inc(v_messages_1273_);
lean_inc(v_env_1272_);
lean_dec(v___x_1270_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1313_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint64_t v_tid_1287_; lean_object* v_traces_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1312_; 
v_tid_1287_ = lean_ctor_get_uint64(v_traceState_1271_, sizeof(void*)*1);
v_traces_1288_ = lean_ctor_get(v_traceState_1271_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_traceState_1271_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1290_ = v_traceState_1271_;
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_traces_1288_);
lean_dec(v_traceState_1271_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; double v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_1295_ = 0;
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1297_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1297_, 0, v_cls_1258_);
lean_ctor_set(v___x_1297_, 1, v___x_1293_);
lean_ctor_set(v___x_1297_, 2, v___x_1296_);
lean_ctor_set_float(v___x_1297_, sizeof(void*)*3, v___x_1294_);
lean_ctor_set_float(v___x_1297_, sizeof(void*)*3 + 8, v___x_1294_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*3 + 16, v___x_1295_);
v___x_1298_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_1299_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v_a_1266_);
lean_ctor_set(v___x_1299_, 2, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_a_1264_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = l_Lean_PersistentArray_push___redArg(v_traces_1288_, v___x_1300_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1301_);
v___x_1303_ = v___x_1290_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1301_);
lean_ctor_set_uint64(v_reuseFailAlloc_1311_, sizeof(void*)*1, v_tid_1287_);
v___x_1303_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 9, v___x_1303_);
v___x_1305_ = v___x_1285_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_env_1272_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_messages_1273_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_scopes_1274_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_usedQuotCtxts_1275_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_nextMacroScope_1276_);
lean_ctor_set(v_reuseFailAlloc_1310_, 5, v_maxRecDepth_1277_);
lean_ctor_set(v_reuseFailAlloc_1310_, 6, v_ngen_1278_);
lean_ctor_set(v_reuseFailAlloc_1310_, 7, v_auxDeclNGen_1279_);
lean_ctor_set(v_reuseFailAlloc_1310_, 8, v_infoState_1280_);
lean_ctor_set(v_reuseFailAlloc_1310_, 9, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1310_, 10, v_snapshotTasks_1281_);
lean_ctor_set(v_reuseFailAlloc_1310_, 11, v_prevLinterStates_1282_);
lean_ctor_set(v_reuseFailAlloc_1310_, 12, v_codeQualityEntryTasks_1283_);
v___x_1305_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_st_ref_put(v___y_1261_, v___x_1305_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1292_);
v___x_1308_ = v___x_1268_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1292_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_msg_1259_);
lean_dec(v_cls_1258_);
v_a_1315_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1263_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1263_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1258_ = stack[0].m_obj;
lean_object* v_msg_1259_ = stack[1].m_obj;
lean_object* v___y_1260_ = stack[2].m_obj;
lean_object* v___y_1261_ = stack[3].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_cls_1258_, v_msg_1259_, v___y_1260_, v___y_1261_);
stack->m_obj
 = v_res_1323_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(lean_object* v___x_1349_, lean_object* v_val_1350_, lean_object* v_cmd_1351_, uint8_t v_onUnsolved_1352_, uint8_t v___y_1353_, lean_object* v_as_1354_, size_t v_sz_1355_, size_t v_i_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
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
v_sz_1419_ = lean_array_size(v___y_1413_);
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1401_, v_fst_1407_, v_snd_1408_, v___y_1414_, v___y_1413_, v_sz_1419_, v___x_1420_, v___x_1418_);
lean_dec_ref(v___y_1413_);
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
v___y_1413_ = v___x_1443_;
v___y_1414_ = v___x_1442_;
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
v___y_1413_ = v___x_1443_;
v___y_1414_ = v___x_1442_;
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
v___y_1413_ = v___x_1443_;
v___y_1414_ = v___x_1442_;
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
v___y_1413_ = v___x_1443_;
v___y_1414_ = v___x_1442_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1349_ = stack[0].m_obj;
lean_object* v_val_1350_ = stack[1].m_obj;
lean_object* v_cmd_1351_ = stack[2].m_obj;
uint8_t v_onUnsolved_1352_ = stack[3].m_num;
uint8_t v___y_1353_ = stack[4].m_num;
lean_object* v_as_1354_ = stack[5].m_obj;
size_t v_sz_1355_ = stack[6].m_num;
size_t v_i_1356_ = stack[7].m_num;
lean_object* v_b_1357_ = stack[8].m_obj;
lean_object* v___y_1358_ = stack[9].m_obj;
lean_object* v___y_1359_ = stack[10].m_obj;
lean_object* v_res_1513_;
v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1349_, v_val_1350_, v_cmd_1351_, v_onUnsolved_1352_, v___y_1353_, v_as_1354_, v_sz_1355_, v_i_1356_, v_b_1357_, v___y_1358_, v___y_1359_);
stack->m_obj
 = v_res_1513_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___boxed(lean_object* v___x_1514_, lean_object* v_val_1515_, lean_object* v_cmd_1516_, lean_object* v_onUnsolved_1517_, lean_object* v___y_1518_, lean_object* v_as_1519_, lean_object* v_sz_1520_, lean_object* v_i_1521_, lean_object* v_b_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v_onUnsolved_boxed_1526_; uint8_t v___y_12291__boxed_1527_; size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_onUnsolved_boxed_1526_ = lean_unbox(v_onUnsolved_1517_);
v___y_12291__boxed_1527_ = lean_unbox(v___y_1518_);
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1520_);
lean_dec(v_sz_1520_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1521_);
lean_dec(v_i_1521_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1514_, v_val_1515_, v_cmd_1516_, v_onUnsolved_boxed_1526_, v___y_12291__boxed_1527_, v_as_1519_, v_sz_boxed_1528_, v_i_boxed_1529_, v_b_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec_ref(v_as_1519_);
lean_dec_ref(v_val_1515_);
lean_dec_ref(v___x_1514_);
return v_res_1530_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object* v___x_1531_, lean_object* v_val_1532_, lean_object* v_cmd_1533_, uint8_t v_onUnsolved_1534_, uint8_t v___y_1535_, lean_object* v_as_1536_, size_t v_sz_1537_, size_t v_i_1538_, lean_object* v_b_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_usize_dec_lt(v_i_1538_, v_sz_1537_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
lean_dec(v_cmd_1533_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_b_1539_);
return v___x_1544_;
}
else
{
lean_object* v_snd_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1693_; 
v_snd_1545_ = lean_ctor_get(v_b_1539_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_b_1539_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v_b_1539_, 0);
lean_dec(v_unused_1694_);
v___x_1547_ = v_b_1539_;
v_isShared_1548_ = v_isSharedCheck_1693_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_snd_1545_);
lean_dec(v_b_1539_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1693_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_fst_1549_; lean_object* v_snd_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1692_; 
v_fst_1549_ = lean_ctor_get(v_snd_1545_, 0);
v_snd_1550_ = lean_ctor_get(v_snd_1545_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_snd_1545_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1552_ = v_snd_1545_;
v_isShared_1553_ = v_isSharedCheck_1692_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_snd_1550_);
lean_inc(v_fst_1549_);
lean_dec(v_snd_1545_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1692_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_a_1554_; lean_object* v_pos_1555_; lean_object* v_endPos_1556_; uint8_t v_severity_1557_; lean_object* v_data_1558_; lean_object* v___x_1559_; lean_object* v_a_1561_; 
v_a_1554_ = lean_array_uget_borrowed(v_as_1536_, v_i_1538_);
v_pos_1555_ = lean_ctor_get(v_a_1554_, 1);
v_endPos_1556_ = lean_ctor_get(v_a_1554_, 2);
lean_inc(v_endPos_1556_);
v_severity_1557_ = lean_ctor_get_uint8(v_a_1554_, sizeof(void*)*5 + 1);
v_data_1558_ = lean_ctor_get(v_a_1554_, 4);
v___x_1559_ = lean_box(0);
if (v_severity_1557_ == 2)
{
lean_object* v___f_1574_; uint8_t v___x_1575_; 
v___f_1574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1558_);
v___x_1575_ = l_Lean_MessageData_hasTag(v___f_1574_, v_data_1558_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec(v_endPos_1556_);
lean_del_object(v___x_1547_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v_fst_1549_);
lean_ctor_set(v___x_1576_, 1, v_snd_1550_);
v_a_1561_ = v___x_1576_;
goto v___jp_1560_;
}
else
{
if (lean_obj_tag(v_endPos_1556_) == 1)
{
lean_object* v_val_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1689_; 
v_val_1577_ = lean_ctor_get(v_endPos_1556_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_endPos_1556_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1579_ = v_endPos_1556_;
v_isShared_1580_ = v_isSharedCheck_1689_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_val_1577_);
lean_dec(v_endPos_1556_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1689_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; uint8_t v___x_1585_; 
lean_inc_ref(v_pos_1555_);
v___x_1581_ = l_Lean_FileMap_ofPosition(v___x_1531_, v_pos_1555_);
v___x_1582_ = l_Lean_FileMap_ofPosition(v___x_1531_, v_val_1577_);
lean_inc(v___x_1582_);
lean_inc(v___x_1581_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = 0;
v___x_1585_ = l_Lean_Syntax_Range_includes(v_val_1532_, v___x_1583_, v___x_1584_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec_ref_known(v___x_1583_, 2);
lean_dec(v___x_1582_);
lean_dec(v___x_1581_);
lean_del_object(v___x_1579_);
lean_del_object(v___x_1547_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_fst_1549_);
lean_ctor_set(v___x_1586_, 1, v_snd_1550_);
v_a_1561_ = v___x_1586_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1587_; 
lean_inc(v_cmd_1533_);
lean_inc_ref(v___x_1583_);
v___x_1587_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1583_, v_cmd_1533_);
if (lean_obj_tag(v___x_1587_) == 1)
{
lean_object* v_val_1588_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v___x_1582_);
lean_dec(v___x_1581_);
lean_del_object(v___x_1579_);
v_val_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_fst_1589_ = lean_ctor_get(v_val_1588_, 0);
v_snd_1590_ = lean_ctor_get(v_val_1588_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_val_1588_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1592_ = v_val_1588_;
v_isShared_1593_ = v_isSharedCheck_1653_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_snd_1590_);
lean_inc(v_fst_1589_);
lean_dec(v_val_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1653_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; uint8_t v___y_1651_; lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Syntax_getPos_x3f(v_fst_1589_, v___x_1584_);
if (lean_obj_tag(v___x_1652_) == 0)
{
v___y_1651_ = v___x_1585_;
goto v___jp_1650_;
}
else
{
lean_dec_ref_known(v___x_1652_, 1);
v___y_1651_ = v___x_1584_;
goto v___jp_1650_;
}
v___jp_1594_:
{
lean_object* v___x_1600_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 1, v_snd_1550_);
lean_ctor_set(v___x_1592_, 0, v_fst_1549_);
v___x_1600_ = v___x_1592_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_fst_1549_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_snd_1550_);
v___x_1600_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
size_t v_sz_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v_sz_1601_ = lean_array_size(v___y_1596_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1583_, v_fst_1589_, v_snd_1590_, v___y_1595_, v___y_1596_, v_sz_1601_, v___x_1602_, v___x_1600_);
lean_dec_ref(v___y_1596_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v_fst_1605_; lean_object* v_snd_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v_fst_1605_ = lean_ctor_get(v_a_1604_, 0);
v_snd_1606_ = lean_ctor_get(v_a_1604_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_a_1604_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v_a_1604_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_snd_1606_);
lean_inc(v_fst_1605_);
lean_dec(v_a_1604_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_fst_1605_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_snd_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
v_a_1561_ = v___x_1611_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_del_object(v___x_1552_);
lean_dec(v_cmd_1533_);
v_a_1614_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1603_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1603_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
v___jp_1623_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
lean_inc_ref(v___x_1583_);
v___x_1624_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1583_);
v___x_1625_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1558_);
v___x_1626_ = lean_array_get_size(v___x_1625_);
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_nat_dec_eq(v___x_1626_, v___x_1627_);
if (v___x_1628_ == 0)
{
v___y_1595_ = v___x_1624_;
v___y_1596_ = v___x_1625_;
v___y_1597_ = v___y_1540_;
v___y_1598_ = v___y_1541_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v_scopes_1634_; lean_object* v___x_1635_; lean_object* v_opts_1636_; uint8_t v_hasTrace_1637_; 
v___x_1629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1630_ = l_Lean_inheritedTraceOptions;
v___x_1631_ = lean_st_ref_get(v___x_1630_);
v___x_1632_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1633_ = lean_st_ref_get(v___y_1541_);
v_scopes_1634_ = lean_ctor_get(v___x_1633_, 2);
lean_inc(v_scopes_1634_);
lean_dec(v___x_1633_);
v___x_1635_ = l_List_head_x21___redArg(v___x_1632_, v_scopes_1634_);
lean_dec(v_scopes_1634_);
v_opts_1636_ = lean_ctor_get(v___x_1635_, 1);
lean_inc_ref(v_opts_1636_);
lean_dec(v___x_1635_);
v_hasTrace_1637_ = lean_ctor_get_uint8(v_opts_1636_, sizeof(void*)*1);
if (v_hasTrace_1637_ == 0)
{
lean_dec_ref(v_opts_1636_);
lean_dec(v___x_1631_);
v___y_1595_ = v___x_1624_;
v___y_1596_ = v___x_1625_;
v___y_1597_ = v___y_1540_;
v___y_1598_ = v___y_1541_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1639_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1631_, v_opts_1636_, v___x_1638_);
lean_dec_ref(v_opts_1636_);
lean_dec(v___x_1631_);
if (v___x_1639_ == 0)
{
v___y_1595_ = v___x_1624_;
v___y_1596_ = v___x_1625_;
v___y_1597_ = v___y_1540_;
v___y_1598_ = v___y_1541_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1641_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1629_, v___x_1640_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec_ref_known(v___x_1641_, 1);
v___y_1595_ = v___x_1624_;
v___y_1596_ = v___x_1625_;
v___y_1597_ = v___y_1540_;
v___y_1598_ = v___y_1541_;
goto v___jp_1594_;
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v___x_1625_);
lean_dec(v___x_1624_);
lean_del_object(v___x_1592_);
lean_dec(v_snd_1590_);
lean_dec(v_fst_1589_);
lean_dec_ref_known(v___x_1583_, 2);
lean_del_object(v___x_1552_);
lean_dec(v_snd_1550_);
lean_dec(v_fst_1549_);
lean_dec(v_cmd_1533_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
}
}
v___jp_1650_:
{
if (v_onUnsolved_1534_ == 0)
{
if (v___y_1535_ == 0)
{
lean_del_object(v___x_1592_);
lean_dec(v_snd_1590_);
lean_dec(v_fst_1589_);
lean_dec_ref_known(v___x_1583_, 2);
goto v___jp_1568_;
}
else
{
if (v___y_1651_ == 0)
{
lean_del_object(v___x_1592_);
lean_dec(v_snd_1590_);
lean_dec(v_fst_1589_);
lean_dec_ref_known(v___x_1583_, 2);
goto v___jp_1568_;
}
else
{
lean_del_object(v___x_1547_);
goto v___jp_1623_;
}
}
}
else
{
lean_del_object(v___x_1547_);
goto v___jp_1623_;
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v_scopes_1659_; lean_object* v___x_1660_; lean_object* v_opts_1661_; uint8_t v_hasTrace_1662_; 
lean_dec(v___x_1587_);
lean_dec_ref_known(v___x_1583_, 2);
lean_del_object(v___x_1547_);
v___x_1654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1655_ = l_Lean_inheritedTraceOptions;
v___x_1656_ = lean_st_ref_get(v___x_1655_);
v___x_1657_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1658_ = lean_st_ref_get(v___y_1541_);
v_scopes_1659_ = lean_ctor_get(v___x_1658_, 2);
lean_inc(v_scopes_1659_);
lean_dec(v___x_1658_);
v___x_1660_ = l_List_head_x21___redArg(v___x_1657_, v_scopes_1659_);
lean_dec(v_scopes_1659_);
v_opts_1661_ = lean_ctor_get(v___x_1660_, 1);
lean_inc_ref(v_opts_1661_);
lean_dec(v___x_1660_);
v_hasTrace_1662_ = lean_ctor_get_uint8(v_opts_1661_, sizeof(void*)*1);
if (v_hasTrace_1662_ == 0)
{
lean_dec_ref(v_opts_1661_);
lean_dec(v___x_1656_);
lean_dec(v___x_1582_);
lean_dec(v___x_1581_);
lean_del_object(v___x_1579_);
goto v___jp_1572_;
}
else
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1664_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1656_, v_opts_1661_, v___x_1663_);
lean_dec_ref(v_opts_1661_);
lean_dec(v___x_1656_);
if (v___x_1664_ == 0)
{
lean_dec(v___x_1582_);
lean_dec(v___x_1581_);
lean_del_object(v___x_1579_);
goto v___jp_1572_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1665_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1666_ = l_Nat_reprFast(v___x_1581_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 3);
lean_ctor_set(v___x_1579_, 0, v___x_1666_);
v___x_1668_ = v___x_1579_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1669_ = l_Lean_MessageData_ofFormat(v___x_1668_);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1665_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Nat_reprFast(v___x_1582_);
v___x_1674_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
v___x_1675_ = l_Lean_MessageData_ofFormat(v___x_1674_);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1672_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1654_, v___x_1678_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_dec_ref_known(v___x_1679_, 1);
goto v___jp_1572_;
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_del_object(v___x_1552_);
lean_dec(v_snd_1550_);
lean_dec(v_fst_1549_);
lean_dec(v_cmd_1533_);
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
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
lean_object* v___x_1690_; 
lean_dec(v_endPos_1556_);
lean_del_object(v___x_1547_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_fst_1549_);
lean_ctor_set(v___x_1690_, 1, v_snd_1550_);
v_a_1561_ = v___x_1690_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v___x_1691_; 
lean_dec(v_endPos_1556_);
lean_del_object(v___x_1547_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_fst_1549_);
lean_ctor_set(v___x_1691_, 1, v_snd_1550_);
v_a_1561_ = v___x_1691_;
goto v___jp_1560_;
}
v___jp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v_a_1561_);
lean_ctor_set(v___x_1552_, 0, v___x_1559_);
v___x_1563_ = v___x_1552_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_a_1561_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = ((size_t)1ULL);
v___x_1565_ = lean_usize_add(v_i_1538_, v___x_1564_);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1531_, v_val_1532_, v_cmd_1533_, v_onUnsolved_1534_, v___y_1535_, v_as_1536_, v_sz_1537_, v___x_1565_, v___x_1563_, v___y_1540_, v___y_1541_);
return v___x_1566_;
}
}
v___jp_1568_:
{
lean_object* v___x_1570_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v_snd_1550_);
lean_ctor_set(v___x_1547_, 0, v_fst_1549_);
v___x_1570_ = v___x_1547_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_fst_1549_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_snd_1550_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
v_a_1561_ = v___x_1570_;
goto v___jp_1560_;
}
}
v___jp_1572_:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_fst_1549_);
lean_ctor_set(v___x_1573_, 1, v_snd_1550_);
v_a_1561_ = v___x_1573_;
goto v___jp_1560_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1531_ = stack[0].m_obj;
lean_object* v_val_1532_ = stack[1].m_obj;
lean_object* v_cmd_1533_ = stack[2].m_obj;
uint8_t v_onUnsolved_1534_ = stack[3].m_num;
uint8_t v___y_1535_ = stack[4].m_num;
lean_object* v_as_1536_ = stack[5].m_obj;
size_t v_sz_1537_ = stack[6].m_num;
size_t v_i_1538_ = stack[7].m_num;
lean_object* v_b_1539_ = stack[8].m_obj;
lean_object* v___y_1540_ = stack[9].m_obj;
lean_object* v___y_1541_ = stack[10].m_obj;
lean_object* v_res_1695_;
v_res_1695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_1531_, v_val_1532_, v_cmd_1533_, v_onUnsolved_1534_, v___y_1535_, v_as_1536_, v_sz_1537_, v_i_1538_, v_b_1539_, v___y_1540_, v___y_1541_);
stack->m_obj
 = v_res_1695_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object* v___x_1696_, lean_object* v_val_1697_, lean_object* v_cmd_1698_, lean_object* v_onUnsolved_1699_, lean_object* v___y_1700_, lean_object* v_as_1701_, lean_object* v_sz_1702_, lean_object* v_i_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_onUnsolved_boxed_1708_; uint8_t v___y_12798__boxed_1709_; size_t v_sz_boxed_1710_; size_t v_i_boxed_1711_; lean_object* v_res_1712_; 
v_onUnsolved_boxed_1708_ = lean_unbox(v_onUnsolved_1699_);
v___y_12798__boxed_1709_ = lean_unbox(v___y_1700_);
v_sz_boxed_1710_ = lean_unbox_usize(v_sz_1702_);
lean_dec(v_sz_1702_);
v_i_boxed_1711_ = lean_unbox_usize(v_i_1703_);
lean_dec(v_i_1703_);
v_res_1712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_1696_, v_val_1697_, v_cmd_1698_, v_onUnsolved_boxed_1708_, v___y_12798__boxed_1709_, v_as_1701_, v_sz_boxed_1710_, v_i_boxed_1711_, v_b_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec_ref(v_as_1701_);
lean_dec_ref(v_val_1697_);
lean_dec_ref(v___x_1696_);
return v_res_1712_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(lean_object* v___x_1713_, lean_object* v_val_1714_, lean_object* v_cmd_1715_, uint8_t v_onUnsolved_1716_, uint8_t v___y_1717_, lean_object* v_as_1718_, size_t v_sz_1719_, size_t v_i_1720_, lean_object* v_b_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_usize_dec_lt(v_i_1720_, v_sz_1719_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
lean_dec(v_cmd_1715_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_b_1721_);
return v___x_1726_;
}
else
{
lean_object* v_snd_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1875_; 
v_snd_1727_ = lean_ctor_get(v_b_1721_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_b_1721_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v_b_1721_, 0);
lean_dec(v_unused_1876_);
v___x_1729_ = v_b_1721_;
v_isShared_1730_ = v_isSharedCheck_1875_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_snd_1727_);
lean_dec(v_b_1721_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1875_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_fst_1731_; lean_object* v_snd_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1874_; 
v_fst_1731_ = lean_ctor_get(v_snd_1727_, 0);
v_snd_1732_ = lean_ctor_get(v_snd_1727_, 1);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_snd_1727_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1734_ = v_snd_1727_;
v_isShared_1735_ = v_isSharedCheck_1874_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snd_1732_);
lean_inc(v_fst_1731_);
lean_dec(v_snd_1727_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1874_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_a_1736_; lean_object* v_pos_1737_; lean_object* v_endPos_1738_; uint8_t v_severity_1739_; lean_object* v_data_1740_; lean_object* v___x_1741_; lean_object* v_a_1743_; 
v_a_1736_ = lean_array_uget_borrowed(v_as_1718_, v_i_1720_);
v_pos_1737_ = lean_ctor_get(v_a_1736_, 1);
v_endPos_1738_ = lean_ctor_get(v_a_1736_, 2);
lean_inc(v_endPos_1738_);
v_severity_1739_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*5 + 1);
v_data_1740_ = lean_ctor_get(v_a_1736_, 4);
v___x_1741_ = lean_box(0);
if (v_severity_1739_ == 2)
{
lean_object* v___f_1756_; uint8_t v___x_1757_; 
v___f_1756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1740_);
v___x_1757_ = l_Lean_MessageData_hasTag(v___f_1756_, v_data_1740_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_dec(v_endPos_1738_);
lean_del_object(v___x_1729_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_fst_1731_);
lean_ctor_set(v___x_1758_, 1, v_snd_1732_);
v_a_1743_ = v___x_1758_;
goto v___jp_1742_;
}
else
{
if (lean_obj_tag(v_endPos_1738_) == 1)
{
lean_object* v_val_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1871_; 
v_val_1759_ = lean_ctor_get(v_endPos_1738_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_endPos_1738_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1761_ = v_endPos_1738_;
v_isShared_1762_ = v_isSharedCheck_1871_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_val_1759_);
lean_dec(v_endPos_1738_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1871_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; uint8_t v___x_1767_; 
lean_inc_ref(v_pos_1737_);
v___x_1763_ = l_Lean_FileMap_ofPosition(v___x_1713_, v_pos_1737_);
v___x_1764_ = l_Lean_FileMap_ofPosition(v___x_1713_, v_val_1759_);
lean_inc(v___x_1764_);
lean_inc(v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = 0;
v___x_1767_ = l_Lean_Syntax_Range_includes(v_val_1714_, v___x_1765_, v___x_1766_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
lean_dec_ref_known(v___x_1765_, 2);
lean_dec(v___x_1764_);
lean_dec(v___x_1763_);
lean_del_object(v___x_1761_);
lean_del_object(v___x_1729_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v_fst_1731_);
lean_ctor_set(v___x_1768_, 1, v_snd_1732_);
v_a_1743_ = v___x_1768_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1769_; 
lean_inc(v_cmd_1715_);
lean_inc_ref(v___x_1765_);
v___x_1769_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1765_, v_cmd_1715_);
if (lean_obj_tag(v___x_1769_) == 1)
{
lean_object* v_val_1770_; lean_object* v_fst_1771_; lean_object* v_snd_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v___x_1764_);
lean_dec(v___x_1763_);
lean_del_object(v___x_1761_);
v_val_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v_fst_1771_ = lean_ctor_get(v_val_1770_, 0);
v_snd_1772_ = lean_ctor_get(v_val_1770_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_val_1770_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1774_ = v_val_1770_;
v_isShared_1775_ = v_isSharedCheck_1835_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_snd_1772_);
lean_inc(v_fst_1771_);
lean_dec(v_val_1770_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1835_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; uint8_t v___y_1833_; lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Syntax_getPos_x3f(v_fst_1771_, v___x_1766_);
if (lean_obj_tag(v___x_1834_) == 0)
{
v___y_1833_ = v___x_1767_;
goto v___jp_1832_;
}
else
{
lean_dec_ref_known(v___x_1834_, 1);
v___y_1833_ = v___x_1766_;
goto v___jp_1832_;
}
v___jp_1776_:
{
lean_object* v___x_1782_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_snd_1732_);
lean_ctor_set(v___x_1774_, 0, v_fst_1731_);
v___x_1782_ = v___x_1774_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_fst_1731_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_snd_1732_);
v___x_1782_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
size_t v_sz_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v_sz_1783_ = lean_array_size(v___y_1778_);
v___x_1784_ = ((size_t)0ULL);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1765_, v_fst_1771_, v_snd_1772_, v___y_1777_, v___y_1778_, v_sz_1783_, v___x_1784_, v___x_1782_);
lean_dec_ref(v___y_1778_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v_fst_1787_; lean_object* v_snd_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v_fst_1787_ = lean_ctor_get(v_a_1786_, 0);
v_snd_1788_ = lean_ctor_get(v_a_1786_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1786_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v_a_1786_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_snd_1788_);
lean_inc(v_fst_1787_);
lean_dec(v_a_1786_);
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
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_fst_1787_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_snd_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
v_a_1743_ = v___x_1793_;
goto v___jp_1742_;
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_del_object(v___x_1734_);
lean_dec(v_cmd_1715_);
v_a_1796_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1785_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1785_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
v___jp_1805_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
lean_inc_ref(v___x_1765_);
v___x_1806_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1765_);
v___x_1807_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1740_);
v___x_1808_ = lean_array_get_size(v___x_1807_);
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_nat_dec_eq(v___x_1808_, v___x_1809_);
if (v___x_1810_ == 0)
{
v___y_1777_ = v___x_1806_;
v___y_1778_ = v___x_1807_;
v___y_1779_ = v___y_1722_;
v___y_1780_ = v___y_1723_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_scopes_1816_; lean_object* v___x_1817_; lean_object* v_opts_1818_; uint8_t v_hasTrace_1819_; 
v___x_1811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1812_ = l_Lean_inheritedTraceOptions;
v___x_1813_ = lean_st_ref_get(v___x_1812_);
v___x_1814_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1815_ = lean_st_ref_get(v___y_1723_);
v_scopes_1816_ = lean_ctor_get(v___x_1815_, 2);
lean_inc(v_scopes_1816_);
lean_dec(v___x_1815_);
v___x_1817_ = l_List_head_x21___redArg(v___x_1814_, v_scopes_1816_);
lean_dec(v_scopes_1816_);
v_opts_1818_ = lean_ctor_get(v___x_1817_, 1);
lean_inc_ref(v_opts_1818_);
lean_dec(v___x_1817_);
v_hasTrace_1819_ = lean_ctor_get_uint8(v_opts_1818_, sizeof(void*)*1);
if (v_hasTrace_1819_ == 0)
{
lean_dec_ref(v_opts_1818_);
lean_dec(v___x_1813_);
v___y_1777_ = v___x_1806_;
v___y_1778_ = v___x_1807_;
v___y_1779_ = v___y_1722_;
v___y_1780_ = v___y_1723_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1813_, v_opts_1818_, v___x_1820_);
lean_dec_ref(v_opts_1818_);
lean_dec(v___x_1813_);
if (v___x_1821_ == 0)
{
v___y_1777_ = v___x_1806_;
v___y_1778_ = v___x_1807_;
v___y_1779_ = v___y_1722_;
v___y_1780_ = v___y_1723_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1823_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1811_, v___x_1822_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_dec_ref_known(v___x_1823_, 1);
v___y_1777_ = v___x_1806_;
v___y_1778_ = v___x_1807_;
v___y_1779_ = v___y_1722_;
v___y_1780_ = v___y_1723_;
goto v___jp_1776_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v___x_1807_);
lean_dec(v___x_1806_);
lean_del_object(v___x_1774_);
lean_dec(v_snd_1772_);
lean_dec(v_fst_1771_);
lean_dec_ref_known(v___x_1765_, 2);
lean_del_object(v___x_1734_);
lean_dec(v_snd_1732_);
lean_dec(v_fst_1731_);
lean_dec(v_cmd_1715_);
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
}
v___jp_1832_:
{
if (v_onUnsolved_1716_ == 0)
{
if (v___y_1717_ == 0)
{
lean_del_object(v___x_1774_);
lean_dec(v_snd_1772_);
lean_dec(v_fst_1771_);
lean_dec_ref_known(v___x_1765_, 2);
goto v___jp_1750_;
}
else
{
if (v___y_1833_ == 0)
{
lean_del_object(v___x_1774_);
lean_dec(v_snd_1772_);
lean_dec(v_fst_1771_);
lean_dec_ref_known(v___x_1765_, 2);
goto v___jp_1750_;
}
else
{
lean_del_object(v___x_1729_);
goto v___jp_1805_;
}
}
}
else
{
lean_del_object(v___x_1729_);
goto v___jp_1805_;
}
}
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_scopes_1841_; lean_object* v___x_1842_; lean_object* v_opts_1843_; uint8_t v_hasTrace_1844_; 
lean_dec(v___x_1769_);
lean_dec_ref_known(v___x_1765_, 2);
lean_del_object(v___x_1729_);
v___x_1836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1837_ = l_Lean_inheritedTraceOptions;
v___x_1838_ = lean_st_ref_get(v___x_1837_);
v___x_1839_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1840_ = lean_st_ref_get(v___y_1723_);
v_scopes_1841_ = lean_ctor_get(v___x_1840_, 2);
lean_inc(v_scopes_1841_);
lean_dec(v___x_1840_);
v___x_1842_ = l_List_head_x21___redArg(v___x_1839_, v_scopes_1841_);
lean_dec(v_scopes_1841_);
v_opts_1843_ = lean_ctor_get(v___x_1842_, 1);
lean_inc_ref(v_opts_1843_);
lean_dec(v___x_1842_);
v_hasTrace_1844_ = lean_ctor_get_uint8(v_opts_1843_, sizeof(void*)*1);
if (v_hasTrace_1844_ == 0)
{
lean_dec_ref(v_opts_1843_);
lean_dec(v___x_1838_);
lean_dec(v___x_1764_);
lean_dec(v___x_1763_);
lean_del_object(v___x_1761_);
goto v___jp_1754_;
}
else
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1846_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1838_, v_opts_1843_, v___x_1845_);
lean_dec_ref(v_opts_1843_);
lean_dec(v___x_1838_);
if (v___x_1846_ == 0)
{
lean_dec(v___x_1764_);
lean_dec(v___x_1763_);
lean_del_object(v___x_1761_);
goto v___jp_1754_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1847_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1848_ = l_Nat_reprFast(v___x_1763_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 3);
lean_ctor_set(v___x_1761_, 0, v___x_1848_);
v___x_1850_ = v___x_1761_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1851_ = l_Lean_MessageData_ofFormat(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1847_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Nat_reprFast(v___x_1764_);
v___x_1856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
v___x_1857_ = l_Lean_MessageData_ofFormat(v___x_1856_);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1854_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1836_, v___x_1860_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref_known(v___x_1861_, 1);
goto v___jp_1754_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_del_object(v___x_1734_);
lean_dec(v_snd_1732_);
lean_dec(v_fst_1731_);
lean_dec(v_cmd_1715_);
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
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
lean_object* v___x_1872_; 
lean_dec(v_endPos_1738_);
lean_del_object(v___x_1729_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_fst_1731_);
lean_ctor_set(v___x_1872_, 1, v_snd_1732_);
v_a_1743_ = v___x_1872_;
goto v___jp_1742_;
}
}
}
else
{
lean_object* v___x_1873_; 
lean_dec(v_endPos_1738_);
lean_del_object(v___x_1729_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_fst_1731_);
lean_ctor_set(v___x_1873_, 1, v_snd_1732_);
v_a_1743_ = v___x_1873_;
goto v___jp_1742_;
}
v___jp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v_a_1743_);
lean_ctor_set(v___x_1734_, 0, v___x_1741_);
v___x_1745_ = v___x_1734_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_a_1743_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
size_t v___x_1746_; size_t v___x_1747_; 
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_add(v_i_1720_, v___x_1746_);
v_i_1720_ = v___x_1747_;
v_b_1721_ = v___x_1745_;
goto _start;
}
}
v___jp_1750_:
{
lean_object* v___x_1752_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v_snd_1732_);
lean_ctor_set(v___x_1729_, 0, v_fst_1731_);
v___x_1752_ = v___x_1729_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_fst_1731_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_snd_1732_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
v_a_1743_ = v___x_1752_;
goto v___jp_1742_;
}
}
v___jp_1754_:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_fst_1731_);
lean_ctor_set(v___x_1755_, 1, v_snd_1732_);
v_a_1743_ = v___x_1755_;
goto v___jp_1742_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1713_ = stack[0].m_obj;
lean_object* v_val_1714_ = stack[1].m_obj;
lean_object* v_cmd_1715_ = stack[2].m_obj;
uint8_t v_onUnsolved_1716_ = stack[3].m_num;
uint8_t v___y_1717_ = stack[4].m_num;
lean_object* v_as_1718_ = stack[5].m_obj;
size_t v_sz_1719_ = stack[6].m_num;
size_t v_i_1720_ = stack[7].m_num;
lean_object* v_b_1721_ = stack[8].m_obj;
lean_object* v___y_1722_ = stack[9].m_obj;
lean_object* v___y_1723_ = stack[10].m_obj;
lean_object* v_res_1877_;
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1713_, v_val_1714_, v_cmd_1715_, v_onUnsolved_1716_, v___y_1717_, v_as_1718_, v_sz_1719_, v_i_1720_, v_b_1721_, v___y_1722_, v___y_1723_);
stack->m_obj
 = v_res_1877_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v___x_1878_, lean_object* v_val_1879_, lean_object* v_cmd_1880_, lean_object* v_onUnsolved_1881_, lean_object* v___y_1882_, lean_object* v_as_1883_, lean_object* v_sz_1884_, lean_object* v_i_1885_, lean_object* v_b_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
uint8_t v_onUnsolved_boxed_1890_; uint8_t v___y_13277__boxed_1891_; size_t v_sz_boxed_1892_; size_t v_i_boxed_1893_; lean_object* v_res_1894_; 
v_onUnsolved_boxed_1890_ = lean_unbox(v_onUnsolved_1881_);
v___y_13277__boxed_1891_ = lean_unbox(v___y_1882_);
v_sz_boxed_1892_ = lean_unbox_usize(v_sz_1884_);
lean_dec(v_sz_1884_);
v_i_boxed_1893_ = lean_unbox_usize(v_i_1885_);
lean_dec(v_i_1885_);
v_res_1894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1878_, v_val_1879_, v_cmd_1880_, v_onUnsolved_boxed_1890_, v___y_13277__boxed_1891_, v_as_1883_, v_sz_boxed_1892_, v_i_boxed_1893_, v_b_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_as_1883_);
lean_dec_ref(v_val_1879_);
lean_dec_ref(v___x_1878_);
return v_res_1894_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(lean_object* v___x_1895_, lean_object* v_val_1896_, lean_object* v_cmd_1897_, uint8_t v_onUnsolved_1898_, uint8_t v___y_1899_, lean_object* v_as_1900_, size_t v_sz_1901_, size_t v_i_1902_, lean_object* v_b_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_usize_dec_lt(v_i_1902_, v_sz_1901_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
lean_dec(v_cmd_1897_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_b_1903_);
return v___x_1908_;
}
else
{
lean_object* v_snd_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_2057_; 
v_snd_1909_ = lean_ctor_get(v_b_1903_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_b_1903_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_b_1903_, 0);
lean_dec(v_unused_2058_);
v___x_1911_ = v_b_1903_;
v_isShared_1912_ = v_isSharedCheck_2057_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_snd_1909_);
lean_dec(v_b_1903_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_2057_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_fst_1913_; lean_object* v_snd_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_2056_; 
v_fst_1913_ = lean_ctor_get(v_snd_1909_, 0);
v_snd_1914_ = lean_ctor_get(v_snd_1909_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_snd_1909_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_1916_ = v_snd_1909_;
v_isShared_1917_ = v_isSharedCheck_2056_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_snd_1914_);
lean_inc(v_fst_1913_);
lean_dec(v_snd_1909_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_2056_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_a_1918_; lean_object* v_pos_1919_; lean_object* v_endPos_1920_; uint8_t v_severity_1921_; lean_object* v_data_1922_; lean_object* v___x_1923_; lean_object* v_a_1925_; 
v_a_1918_ = lean_array_uget_borrowed(v_as_1900_, v_i_1902_);
v_pos_1919_ = lean_ctor_get(v_a_1918_, 1);
v_endPos_1920_ = lean_ctor_get(v_a_1918_, 2);
lean_inc(v_endPos_1920_);
v_severity_1921_ = lean_ctor_get_uint8(v_a_1918_, sizeof(void*)*5 + 1);
v_data_1922_ = lean_ctor_get(v_a_1918_, 4);
v___x_1923_ = lean_box(0);
if (v_severity_1921_ == 2)
{
lean_object* v___f_1938_; uint8_t v___x_1939_; 
v___f_1938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1922_);
v___x_1939_ = l_Lean_MessageData_hasTag(v___f_1938_, v_data_1922_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; 
lean_dec(v_endPos_1920_);
lean_del_object(v___x_1911_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_fst_1913_);
lean_ctor_set(v___x_1940_, 1, v_snd_1914_);
v_a_1925_ = v___x_1940_;
goto v___jp_1924_;
}
else
{
if (lean_obj_tag(v_endPos_1920_) == 1)
{
lean_object* v_val_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_2053_; 
v_val_1941_ = lean_ctor_get(v_endPos_1920_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_endPos_1920_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_1943_ = v_endPos_1920_;
v_isShared_1944_ = v_isSharedCheck_2053_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_val_1941_);
lean_dec(v_endPos_1920_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_2053_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; uint8_t v___x_1949_; 
lean_inc_ref(v_pos_1919_);
v___x_1945_ = l_Lean_FileMap_ofPosition(v___x_1895_, v_pos_1919_);
v___x_1946_ = l_Lean_FileMap_ofPosition(v___x_1895_, v_val_1941_);
lean_inc(v___x_1946_);
lean_inc(v___x_1945_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = 0;
v___x_1949_ = l_Lean_Syntax_Range_includes(v_val_1896_, v___x_1947_, v___x_1948_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec_ref_known(v___x_1947_, 2);
lean_dec(v___x_1946_);
lean_dec(v___x_1945_);
lean_del_object(v___x_1943_);
lean_del_object(v___x_1911_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v_fst_1913_);
lean_ctor_set(v___x_1950_, 1, v_snd_1914_);
v_a_1925_ = v___x_1950_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1951_; 
lean_inc(v_cmd_1897_);
lean_inc_ref(v___x_1947_);
v___x_1951_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1947_, v_cmd_1897_);
if (lean_obj_tag(v___x_1951_) == 1)
{
lean_object* v_val_1952_; lean_object* v_fst_1953_; lean_object* v_snd_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v___x_1946_);
lean_dec(v___x_1945_);
lean_del_object(v___x_1943_);
v_val_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_val_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v_fst_1953_ = lean_ctor_get(v_val_1952_, 0);
v_snd_1954_ = lean_ctor_get(v_val_1952_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_val_1952_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1956_ = v_val_1952_;
v_isShared_1957_ = v_isSharedCheck_2017_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_snd_1954_);
lean_inc(v_fst_1953_);
lean_dec(v_val_1952_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2017_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; uint8_t v___y_2015_; lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Syntax_getPos_x3f(v_fst_1953_, v___x_1948_);
if (lean_obj_tag(v___x_2016_) == 0)
{
v___y_2015_ = v___x_1949_;
goto v___jp_2014_;
}
else
{
lean_dec_ref_known(v___x_2016_, 1);
v___y_2015_ = v___x_1948_;
goto v___jp_2014_;
}
v___jp_1958_:
{
lean_object* v___x_1964_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v_snd_1914_);
lean_ctor_set(v___x_1956_, 0, v_fst_1913_);
v___x_1964_ = v___x_1956_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_fst_1913_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_snd_1914_);
v___x_1964_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
size_t v_sz_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
v_sz_1965_ = lean_array_size(v___y_1960_);
v___x_1966_ = ((size_t)0ULL);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1947_, v_fst_1953_, v_snd_1954_, v___y_1959_, v___y_1960_, v_sz_1965_, v___x_1966_, v___x_1964_);
lean_dec_ref(v___y_1960_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v_fst_1969_ = lean_ctor_get(v_a_1968_, 0);
v_snd_1970_ = lean_ctor_get(v_a_1968_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v_a_1968_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1970_);
lean_inc(v_fst_1969_);
lean_dec(v_a_1968_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_fst_1969_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_snd_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
v_a_1925_ = v___x_1975_;
goto v___jp_1924_;
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_del_object(v___x_1916_);
lean_dec(v_cmd_1897_);
v_a_1978_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1967_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1967_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
v___jp_1987_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
lean_inc_ref(v___x_1947_);
v___x_1988_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1947_);
v___x_1989_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1922_);
v___x_1990_ = lean_array_get_size(v___x_1989_);
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_nat_dec_eq(v___x_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
v___y_1959_ = v___x_1988_;
v___y_1960_ = v___x_1989_;
v___y_1961_ = v___y_1904_;
v___y_1962_ = v___y_1905_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_scopes_1998_; lean_object* v___x_1999_; lean_object* v_opts_2000_; uint8_t v_hasTrace_2001_; 
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1994_ = l_Lean_inheritedTraceOptions;
v___x_1995_ = lean_st_ref_get(v___x_1994_);
v___x_1996_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1997_ = lean_st_ref_get(v___y_1905_);
v_scopes_1998_ = lean_ctor_get(v___x_1997_, 2);
lean_inc(v_scopes_1998_);
lean_dec(v___x_1997_);
v___x_1999_ = l_List_head_x21___redArg(v___x_1996_, v_scopes_1998_);
lean_dec(v_scopes_1998_);
v_opts_2000_ = lean_ctor_get(v___x_1999_, 1);
lean_inc_ref(v_opts_2000_);
lean_dec(v___x_1999_);
v_hasTrace_2001_ = lean_ctor_get_uint8(v_opts_2000_, sizeof(void*)*1);
if (v_hasTrace_2001_ == 0)
{
lean_dec_ref(v_opts_2000_);
lean_dec(v___x_1995_);
v___y_1959_ = v___x_1988_;
v___y_1960_ = v___x_1989_;
v___y_1961_ = v___y_1904_;
v___y_1962_ = v___y_1905_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2003_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1995_, v_opts_2000_, v___x_2002_);
lean_dec_ref(v_opts_2000_);
lean_dec(v___x_1995_);
if (v___x_2003_ == 0)
{
v___y_1959_ = v___x_1988_;
v___y_1960_ = v___x_1989_;
v___y_1961_ = v___y_1904_;
v___y_1962_ = v___y_1905_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_2005_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1993_, v___x_2004_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_dec_ref_known(v___x_2005_, 1);
v___y_1959_ = v___x_1988_;
v___y_1960_ = v___x_1989_;
v___y_1961_ = v___y_1904_;
v___y_1962_ = v___y_1905_;
goto v___jp_1958_;
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref(v___x_1989_);
lean_dec(v___x_1988_);
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_dec(v_fst_1953_);
lean_dec_ref_known(v___x_1947_, 2);
lean_del_object(v___x_1916_);
lean_dec(v_snd_1914_);
lean_dec(v_fst_1913_);
lean_dec(v_cmd_1897_);
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
}
v___jp_2014_:
{
if (v_onUnsolved_1898_ == 0)
{
if (v___y_1899_ == 0)
{
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_dec(v_fst_1953_);
lean_dec_ref_known(v___x_1947_, 2);
goto v___jp_1932_;
}
else
{
if (v___y_2015_ == 0)
{
lean_del_object(v___x_1956_);
lean_dec(v_snd_1954_);
lean_dec(v_fst_1953_);
lean_dec_ref_known(v___x_1947_, 2);
goto v___jp_1932_;
}
else
{
lean_del_object(v___x_1911_);
goto v___jp_1987_;
}
}
}
else
{
lean_del_object(v___x_1911_);
goto v___jp_1987_;
}
}
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v_scopes_2023_; lean_object* v___x_2024_; lean_object* v_opts_2025_; uint8_t v_hasTrace_2026_; 
lean_dec(v___x_1951_);
lean_dec_ref_known(v___x_1947_, 2);
lean_del_object(v___x_1911_);
v___x_2018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2019_ = l_Lean_inheritedTraceOptions;
v___x_2020_ = lean_st_ref_get(v___x_2019_);
v___x_2021_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2022_ = lean_st_ref_get(v___y_1905_);
v_scopes_2023_ = lean_ctor_get(v___x_2022_, 2);
lean_inc(v_scopes_2023_);
lean_dec(v___x_2022_);
v___x_2024_ = l_List_head_x21___redArg(v___x_2021_, v_scopes_2023_);
lean_dec(v_scopes_2023_);
v_opts_2025_ = lean_ctor_get(v___x_2024_, 1);
lean_inc_ref(v_opts_2025_);
lean_dec(v___x_2024_);
v_hasTrace_2026_ = lean_ctor_get_uint8(v_opts_2025_, sizeof(void*)*1);
if (v_hasTrace_2026_ == 0)
{
lean_dec_ref(v_opts_2025_);
lean_dec(v___x_2020_);
lean_dec(v___x_1946_);
lean_dec(v___x_1945_);
lean_del_object(v___x_1943_);
goto v___jp_1936_;
}
else
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2028_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2020_, v_opts_2025_, v___x_2027_);
lean_dec_ref(v_opts_2025_);
lean_dec(v___x_2020_);
if (v___x_2028_ == 0)
{
lean_dec(v___x_1946_);
lean_dec(v___x_1945_);
lean_del_object(v___x_1943_);
goto v___jp_1936_;
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2029_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_2030_ = l_Nat_reprFast(v___x_1945_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set_tag(v___x_1943_, 3);
lean_ctor_set(v___x_1943_, 0, v___x_2030_);
v___x_2032_ = v___x_1943_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2033_ = l_Lean_MessageData_ofFormat(v___x_2032_);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2029_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = l_Nat_reprFast(v___x_1946_);
v___x_2038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = l_Lean_MessageData_ofFormat(v___x_2038_);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2036_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_2018_, v___x_2042_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_dec_ref_known(v___x_2043_, 1);
goto v___jp_1936_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_del_object(v___x_1916_);
lean_dec(v_snd_1914_);
lean_dec(v_fst_1913_);
lean_dec(v_cmd_1897_);
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
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
}
}
}
}
}
}
else
{
lean_object* v___x_2054_; 
lean_dec(v_endPos_1920_);
lean_del_object(v___x_1911_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_fst_1913_);
lean_ctor_set(v___x_2054_, 1, v_snd_1914_);
v_a_1925_ = v___x_2054_;
goto v___jp_1924_;
}
}
}
else
{
lean_object* v___x_2055_; 
lean_dec(v_endPos_1920_);
lean_del_object(v___x_1911_);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v_fst_1913_);
lean_ctor_set(v___x_2055_, 1, v_snd_1914_);
v_a_1925_ = v___x_2055_;
goto v___jp_1924_;
}
v___jp_1924_:
{
lean_object* v___x_1927_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v_a_1925_);
lean_ctor_set(v___x_1916_, 0, v___x_1923_);
v___x_1927_ = v___x_1916_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_a_1925_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)1ULL);
v___x_1929_ = lean_usize_add(v_i_1902_, v___x_1928_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1895_, v_val_1896_, v_cmd_1897_, v_onUnsolved_1898_, v___y_1899_, v_as_1900_, v_sz_1901_, v___x_1929_, v___x_1927_, v___y_1904_, v___y_1905_);
return v___x_1930_;
}
}
v___jp_1932_:
{
lean_object* v___x_1934_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 1, v_snd_1914_);
lean_ctor_set(v___x_1911_, 0, v_fst_1913_);
v___x_1934_ = v___x_1911_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_fst_1913_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_snd_1914_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
v_a_1925_ = v___x_1934_;
goto v___jp_1924_;
}
}
v___jp_1936_:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_fst_1913_);
lean_ctor_set(v___x_1937_, 1, v_snd_1914_);
v_a_1925_ = v___x_1937_;
goto v___jp_1924_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1895_ = stack[0].m_obj;
lean_object* v_val_1896_ = stack[1].m_obj;
lean_object* v_cmd_1897_ = stack[2].m_obj;
uint8_t v_onUnsolved_1898_ = stack[3].m_num;
uint8_t v___y_1899_ = stack[4].m_num;
lean_object* v_as_1900_ = stack[5].m_obj;
size_t v_sz_1901_ = stack[6].m_num;
size_t v_i_1902_ = stack[7].m_num;
lean_object* v_b_1903_ = stack[8].m_obj;
lean_object* v___y_1904_ = stack[9].m_obj;
lean_object* v___y_1905_ = stack[10].m_obj;
lean_object* v_res_2059_;
v_res_2059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_1895_, v_val_1896_, v_cmd_1897_, v_onUnsolved_1898_, v___y_1899_, v_as_1900_, v_sz_1901_, v_i_1902_, v_b_1903_, v___y_1904_, v___y_1905_);
stack->m_obj
 = v_res_2059_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11___boxed(lean_object* v___x_2060_, lean_object* v_val_2061_, lean_object* v_cmd_2062_, lean_object* v_onUnsolved_2063_, lean_object* v___y_2064_, lean_object* v_as_2065_, lean_object* v_sz_2066_, lean_object* v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
uint8_t v_onUnsolved_boxed_2072_; uint8_t v___y_13756__boxed_2073_; size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_onUnsolved_boxed_2072_ = lean_unbox(v_onUnsolved_2063_);
v___y_13756__boxed_2073_ = lean_unbox(v___y_2064_);
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2060_, v_val_2061_, v_cmd_2062_, v_onUnsolved_boxed_2072_, v___y_13756__boxed_2073_, v_as_2065_, v_sz_boxed_2074_, v_i_boxed_2075_, v_b_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec_ref(v_as_2065_);
lean_dec_ref(v_val_2061_);
lean_dec_ref(v___x_2060_);
return v_res_2076_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(lean_object* v_init_2077_, lean_object* v___x_2078_, lean_object* v_val_2079_, lean_object* v_cmd_2080_, uint8_t v_onUnsolved_2081_, uint8_t v___y_2082_, lean_object* v_n_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
if (lean_obj_tag(v_n_2083_) == 0)
{
lean_object* v_cs_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; size_t v_sz_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v_cs_2088_ = lean_ctor_get(v_n_2083_, 0);
v___x_2089_ = lean_box(0);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_b_2084_);
v_sz_2091_ = lean_array_size(v_cs_2088_);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2077_, v___x_2078_, v_val_2079_, v_cmd_2080_, v_onUnsolved_2081_, v___y_2082_, v_cs_2088_, v_sz_2091_, v___x_2092_, v___x_2090_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2108_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_fst_2098_; 
v_fst_2098_ = lean_ctor_get(v_a_2094_, 0);
if (lean_obj_tag(v_fst_2098_) == 0)
{
lean_object* v_snd_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v_snd_2099_ = lean_ctor_get(v_a_2094_, 1);
lean_inc(v_snd_2099_);
lean_dec(v_a_2094_);
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_snd_2099_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2100_);
v___x_2102_ = v___x_2096_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
lean_object* v_val_2104_; lean_object* v___x_2106_; 
lean_inc_ref(v_fst_2098_);
lean_dec(v_a_2094_);
v_val_2104_ = lean_ctor_get(v_fst_2098_, 0);
lean_inc(v_val_2104_);
lean_dec_ref_known(v_fst_2098_, 1);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v_val_2104_);
v___x_2106_ = v___x_2096_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_val_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_a_2109_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2093_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2093_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_vs_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; size_t v_sz_2120_; size_t v___x_2121_; lean_object* v___x_2122_; 
v_vs_2117_ = lean_ctor_get(v_n_2083_, 0);
v___x_2118_ = lean_box(0);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v_b_2084_);
v_sz_2120_ = lean_array_size(v_vs_2117_);
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2078_, v_val_2079_, v_cmd_2080_, v_onUnsolved_2081_, v___y_2082_, v_vs_2117_, v_sz_2120_, v___x_2121_, v___x_2119_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2137_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2137_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2137_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_fst_2127_; 
v_fst_2127_ = lean_ctor_get(v_a_2123_, 0);
if (lean_obj_tag(v_fst_2127_) == 0)
{
lean_object* v_snd_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
v_snd_2128_ = lean_ctor_get(v_a_2123_, 1);
lean_inc(v_snd_2128_);
lean_dec(v_a_2123_);
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_snd_2128_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2129_);
v___x_2131_ = v___x_2125_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
else
{
lean_object* v_val_2133_; lean_object* v___x_2135_; 
lean_inc_ref(v_fst_2127_);
lean_dec(v_a_2123_);
v_val_2133_ = lean_ctor_get(v_fst_2127_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v_fst_2127_, 1);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v_val_2133_);
v___x_2135_ = v___x_2125_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_val_2133_);
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
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
v_a_2138_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2122_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2122_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2077_ = stack[0].m_obj;
lean_object* v___x_2078_ = stack[1].m_obj;
lean_object* v_val_2079_ = stack[2].m_obj;
lean_object* v_cmd_2080_ = stack[3].m_obj;
uint8_t v_onUnsolved_2081_ = stack[4].m_num;
uint8_t v___y_2082_ = stack[5].m_num;
lean_object* v_n_2083_ = stack[6].m_obj;
lean_object* v_b_2084_ = stack[7].m_obj;
lean_object* v___y_2085_ = stack[8].m_obj;
lean_object* v___y_2086_ = stack[9].m_obj;
lean_object* v_res_2146_;
v_res_2146_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2077_, v___x_2078_, v_val_2079_, v_cmd_2080_, v_onUnsolved_2081_, v___y_2082_, v_n_2083_, v_b_2084_, v___y_2085_, v___y_2086_);
stack->m_obj
 = v_res_2146_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(lean_object* v_init_2147_, lean_object* v___x_2148_, lean_object* v_val_2149_, lean_object* v_cmd_2150_, uint8_t v_onUnsolved_2151_, uint8_t v___y_2152_, lean_object* v_as_2153_, size_t v_sz_2154_, size_t v_i_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v___x_2160_; 
v___x_2160_ = lean_usize_dec_lt(v_i_2155_, v_sz_2154_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; 
lean_dec(v_cmd_2150_);
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_b_2156_);
return v___x_2161_;
}
else
{
lean_object* v_snd_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2196_; 
v_snd_2162_ = lean_ctor_get(v_b_2156_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_b_2156_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v_b_2156_, 0);
lean_dec(v_unused_2197_);
v___x_2164_ = v_b_2156_;
v_isShared_2165_ = v_isSharedCheck_2196_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_snd_2162_);
lean_dec(v_b_2156_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2196_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v_a_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_box(0);
v_a_2167_ = lean_array_uget_borrowed(v_as_2153_, v_i_2155_);
lean_inc(v_snd_2162_);
lean_inc(v_cmd_2150_);
v___x_2168_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2147_, v___x_2148_, v_val_2149_, v_cmd_2150_, v_onUnsolved_2151_, v___y_2152_, v_a_2167_, v_snd_2162_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2187_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2187_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2187_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
if (lean_obj_tag(v_a_2169_) == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
lean_dec(v_cmd_2150_);
v___x_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_a_2169_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2173_);
v___x_2175_ = v___x_2164_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_snd_2162_);
v___x_2175_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2177_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2175_);
v___x_2177_ = v___x_2171_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; 
lean_del_object(v___x_2171_);
lean_dec(v_snd_2162_);
v_a_2180_ = lean_ctor_get(v_a_2169_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v_a_2169_, 1);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v_a_2180_);
lean_ctor_set(v___x_2164_, 0, v___x_2166_);
v___x_2182_ = v___x_2164_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_a_2180_);
v___x_2182_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
size_t v___x_2183_; size_t v___x_2184_; 
v___x_2183_ = ((size_t)1ULL);
v___x_2184_ = lean_usize_add(v_i_2155_, v___x_2183_);
v_i_2155_ = v___x_2184_;
v_b_2156_ = v___x_2182_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_del_object(v___x_2164_);
lean_dec(v_snd_2162_);
lean_dec(v_cmd_2150_);
v_a_2188_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2168_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2168_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2147_ = stack[0].m_obj;
lean_object* v___x_2148_ = stack[1].m_obj;
lean_object* v_val_2149_ = stack[2].m_obj;
lean_object* v_cmd_2150_ = stack[3].m_obj;
uint8_t v_onUnsolved_2151_ = stack[4].m_num;
uint8_t v___y_2152_ = stack[5].m_num;
lean_object* v_as_2153_ = stack[6].m_obj;
size_t v_sz_2154_ = stack[7].m_num;
size_t v_i_2155_ = stack[8].m_num;
lean_object* v_b_2156_ = stack[9].m_obj;
lean_object* v___y_2157_ = stack[10].m_obj;
lean_object* v___y_2158_ = stack[11].m_obj;
lean_object* v_res_2198_;
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2147_, v___x_2148_, v_val_2149_, v_cmd_2150_, v_onUnsolved_2151_, v___y_2152_, v_as_2153_, v_sz_2154_, v_i_2155_, v_b_2156_, v___y_2157_, v___y_2158_);
stack->m_obj
 = v_res_2198_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10___boxed(lean_object* v_init_2199_, lean_object* v___x_2200_, lean_object* v_val_2201_, lean_object* v_cmd_2202_, lean_object* v_onUnsolved_2203_, lean_object* v___y_2204_, lean_object* v_as_2205_, lean_object* v_sz_2206_, lean_object* v_i_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
uint8_t v_onUnsolved_boxed_2212_; uint8_t v___y_14204__boxed_2213_; size_t v_sz_boxed_2214_; size_t v_i_boxed_2215_; lean_object* v_res_2216_; 
v_onUnsolved_boxed_2212_ = lean_unbox(v_onUnsolved_2203_);
v___y_14204__boxed_2213_ = lean_unbox(v___y_2204_);
v_sz_boxed_2214_ = lean_unbox_usize(v_sz_2206_);
lean_dec(v_sz_2206_);
v_i_boxed_2215_ = lean_unbox_usize(v_i_2207_);
lean_dec(v_i_2207_);
v_res_2216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2199_, v___x_2200_, v_val_2201_, v_cmd_2202_, v_onUnsolved_boxed_2212_, v___y_14204__boxed_2213_, v_as_2205_, v_sz_boxed_2214_, v_i_boxed_2215_, v_b_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_as_2205_);
lean_dec_ref(v_val_2201_);
lean_dec_ref(v___x_2200_);
lean_dec_ref(v_init_2199_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8___boxed(lean_object* v_init_2217_, lean_object* v___x_2218_, lean_object* v_val_2219_, lean_object* v_cmd_2220_, lean_object* v_onUnsolved_2221_, lean_object* v___y_2222_, lean_object* v_n_2223_, lean_object* v_b_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v_onUnsolved_boxed_2228_; uint8_t v___y_14226__boxed_2229_; lean_object* v_res_2230_; 
v_onUnsolved_boxed_2228_ = lean_unbox(v_onUnsolved_2221_);
v___y_14226__boxed_2229_ = lean_unbox(v___y_2222_);
v_res_2230_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2217_, v___x_2218_, v_val_2219_, v_cmd_2220_, v_onUnsolved_boxed_2228_, v___y_14226__boxed_2229_, v_n_2223_, v_b_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v_n_2223_);
lean_dec_ref(v_val_2219_);
lean_dec_ref(v___x_2218_);
lean_dec_ref(v_init_2217_);
return v_res_2230_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object* v___x_2231_, lean_object* v_val_2232_, lean_object* v_cmd_2233_, uint8_t v_onUnsolved_2234_, uint8_t v___y_2235_, lean_object* v_t_2236_, lean_object* v_init_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_root_2241_; lean_object* v_tail_2242_; lean_object* v___x_2243_; 
v_root_2241_ = lean_ctor_get(v_t_2236_, 0);
v_tail_2242_ = lean_ctor_get(v_t_2236_, 1);
lean_inc(v_cmd_2233_);
lean_inc_ref(v_init_2237_);
v___x_2243_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2237_, v___x_2231_, v_val_2232_, v_cmd_2233_, v_onUnsolved_2234_, v___y_2235_, v_root_2241_, v_init_2237_, v___y_2238_, v___y_2239_);
lean_dec_ref(v_init_2237_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2280_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2280_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2280_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
if (lean_obj_tag(v_a_2244_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; 
lean_dec(v_cmd_2233_);
v_a_2248_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v_a_2244_, 1);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_a_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; size_t v_sz_2255_; size_t v___x_2256_; lean_object* v___x_2257_; 
lean_del_object(v___x_2246_);
v_a_2252_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v_a_2244_, 1);
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v_a_2252_);
v_sz_2255_ = lean_array_size(v_tail_2242_);
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_2231_, v_val_2232_, v_cmd_2233_, v_onUnsolved_2234_, v___y_2235_, v_tail_2242_, v_sz_2255_, v___x_2256_, v___x_2254_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2271_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2271_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2271_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v_fst_2262_; 
v_fst_2262_ = lean_ctor_get(v_a_2258_, 0);
if (lean_obj_tag(v_fst_2262_) == 0)
{
lean_object* v_snd_2263_; lean_object* v___x_2265_; 
v_snd_2263_ = lean_ctor_get(v_a_2258_, 1);
lean_inc(v_snd_2263_);
lean_dec(v_a_2258_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v_snd_2263_);
v___x_2265_ = v___x_2260_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_snd_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
else
{
lean_object* v_val_2267_; lean_object* v___x_2269_; 
lean_inc_ref(v_fst_2262_);
lean_dec(v_a_2258_);
v_val_2267_ = lean_ctor_get(v_fst_2262_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v_fst_2262_, 1);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v_val_2267_);
v___x_2269_ = v___x_2260_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_val_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
v_a_2272_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2257_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2257_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_cmd_2233_);
v_a_2281_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2243_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2243_);
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
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2231_ = stack[0].m_obj;
lean_object* v_val_2232_ = stack[1].m_obj;
lean_object* v_cmd_2233_ = stack[2].m_obj;
uint8_t v_onUnsolved_2234_ = stack[3].m_num;
uint8_t v___y_2235_ = stack[4].m_num;
lean_object* v_t_2236_ = stack[5].m_obj;
lean_object* v_init_2237_ = stack[6].m_obj;
lean_object* v___y_2238_ = stack[7].m_obj;
lean_object* v___y_2239_ = stack[8].m_obj;
lean_object* v_res_2289_;
v_res_2289_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2231_, v_val_2232_, v_cmd_2233_, v_onUnsolved_2234_, v___y_2235_, v_t_2236_, v_init_2237_, v___y_2238_, v___y_2239_);
stack->m_obj
 = v_res_2289_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object* v___x_2290_, lean_object* v_val_2291_, lean_object* v_cmd_2292_, lean_object* v_onUnsolved_2293_, lean_object* v___y_2294_, lean_object* v_t_2295_, lean_object* v_init_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v_onUnsolved_boxed_2300_; uint8_t v___y_14529__boxed_2301_; lean_object* v_res_2302_; 
v_onUnsolved_boxed_2300_ = lean_unbox(v_onUnsolved_2293_);
v___y_14529__boxed_2301_ = lean_unbox(v___y_2294_);
v_res_2302_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2290_, v_val_2291_, v_cmd_2292_, v_onUnsolved_boxed_2300_, v___y_14529__boxed_2301_, v_t_2295_, v_init_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v_t_2295_);
lean_dec_ref(v_val_2291_);
lean_dec_ref(v___x_2290_);
return v_res_2302_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_unsigned_to_nat(16u);
v___x_2305_ = lean_mk_array(v___x_2304_, v___x_2303_);
return v___x_2305_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2306_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v___x_2306_);
return v___x_2308_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2312_, lean_object* v_opts_2313_, lean_object* v_tree_2314_, lean_object* v_msgs_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
uint8_t v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; uint8_t v___y_2323_; lean_object* v___y_2324_; uint8_t v___y_2325_; uint8_t v___y_2351_; uint8_t v___y_2352_; lean_object* v_acc_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___f_2357_; uint8_t v___y_2359_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___f_2357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2366_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2367_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2313_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2369_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2313_, v___x_2368_);
v___y_2359_ = v___x_2369_;
goto v___jp_2358_;
}
else
{
v___y_2359_ = v___x_2367_;
goto v___jp_2358_;
}
v___jp_2319_:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_Syntax_getRange_x3f(v_cmd_2312_, v___y_2325_);
if (lean_obj_tag(v___x_2326_) == 1)
{
lean_object* v_val_2327_; lean_object* v_fileMap_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_val_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v_fileMap_2328_ = lean_ctor_get(v___y_2324_, 1);
v___x_2329_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___y_2321_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v_fileMap_2328_, v_val_2327_, v_cmd_2312_, v___y_2320_, v___y_2323_, v_msgs_2315_, v___x_2330_, v___y_2324_, v___y_2322_);
lean_dec(v_val_2327_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v_fst_2336_; lean_object* v___x_2338_; 
v_fst_2336_ = lean_ctor_get(v_a_2332_, 0);
lean_inc(v_fst_2336_);
lean_dec(v_a_2332_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v_fst_2336_);
v___x_2338_ = v___x_2334_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_fst_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_a_2341_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2331_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2331_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v___x_2349_; 
lean_dec(v___x_2326_);
lean_dec(v_cmd_2312_);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___y_2321_);
return v___x_2349_;
}
}
v___jp_2350_:
{
if (v___y_2351_ == 0)
{
if (v___y_2352_ == 0)
{
lean_object* v___x_2356_; 
lean_dec(v_cmd_2312_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_acc_2353_);
return v___x_2356_;
}
else
{
v___y_2320_ = v___y_2351_;
v___y_2321_ = v_acc_2353_;
v___y_2322_ = v___y_2355_;
v___y_2323_ = v___y_2352_;
v___y_2324_ = v___y_2354_;
v___y_2325_ = v___y_2352_;
goto v___jp_2319_;
}
}
else
{
v___y_2320_ = v___y_2351_;
v___y_2321_ = v_acc_2353_;
v___y_2322_ = v___y_2355_;
v___y_2323_ = v___y_2352_;
v___y_2324_ = v___y_2354_;
v___y_2325_ = v___y_2351_;
goto v___jp_2319_;
}
}
v___jp_2358_:
{
lean_object* v___x_2360_; uint8_t v_onUnsolved_2361_; lean_object* v___x_2362_; uint8_t v_onSorry_2363_; lean_object* v_acc_2364_; 
v___x_2360_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2361_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2313_, v___x_2360_);
v___x_2362_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2363_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2313_, v___x_2362_);
v_acc_2364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2363_ == 0)
{
lean_dec_ref(v_tree_2314_);
v___y_2351_ = v_onUnsolved_2361_;
v___y_2352_ = v___y_2359_;
v_acc_2353_ = v_acc_2364_;
v___y_2354_ = v_a_2316_;
v___y_2355_ = v_a_2317_;
goto v___jp_2350_;
}
else
{
lean_object* v_acc_2365_; 
v_acc_2365_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2357_, v_acc_2364_, v_tree_2314_);
v___y_2351_ = v_onUnsolved_2361_;
v___y_2352_ = v___y_2359_;
v_acc_2353_ = v_acc_2365_;
v___y_2354_ = v_a_2316_;
v___y_2355_ = v_a_2317_;
goto v___jp_2350_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_2312_ = stack[0].m_obj;
lean_object* v_opts_2313_ = stack[1].m_obj;
lean_object* v_tree_2314_ = stack[2].m_obj;
lean_object* v_msgs_2315_ = stack[3].m_obj;
lean_object* v_a_2316_ = stack[4].m_obj;
lean_object* v_a_2317_ = stack[5].m_obj;
lean_object* v_res_2370_;
v_res_2370_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2312_, v_opts_2313_, v_tree_2314_, v_msgs_2315_, v_a_2316_, v_a_2317_);
stack->m_obj
 = v_res_2370_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2371_, lean_object* v_opts_2372_, lean_object* v_tree_2373_, lean_object* v_msgs_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2371_, v_opts_2372_, v_tree_2373_, v_msgs_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec_ref(v_msgs_2374_);
lean_dec_ref(v_opts_2372_);
return v_res_2378_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2379_, lean_object* v_m_2380_, lean_object* v_a_2381_){
_start:
{
uint8_t v___x_2382_; 
v___x_2382_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2380_, v_a_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2380_ = stack[1].m_obj;
lean_object* v_a_2381_ = stack[2].m_obj;
uint8_t v_res_2383_;
v_res_2383_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_box(0), v_m_2380_, v_a_2381_);
stack->m_num = v_res_2383_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object* v_00_u03b2_2384_, lean_object* v_m_2385_, lean_object* v_a_2386_){
_start:
{
uint8_t v_res_2387_; lean_object* v_r_2388_; 
v_res_2387_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(v_00_u03b2_2384_, v_m_2385_, v_a_2386_);
lean_dec_ref(v_a_2386_);
lean_dec_ref(v_m_2385_);
v_r_2388_ = lean_box(v_res_2387_);
return v_r_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v_00_u03b2_2389_, lean_object* v_m_2390_, lean_object* v_a_2391_, lean_object* v_b_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_2390_, v_a_2391_, v_b_2392_);
return v___x_2393_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v___x_2394_, lean_object* v_fst_2395_, lean_object* v_snd_2396_, lean_object* v___x_2397_, lean_object* v_as_2398_, size_t v_sz_2399_, size_t v_i_2400_, lean_object* v_b_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_2394_, v_fst_2395_, v_snd_2396_, v___x_2397_, v_as_2398_, v_sz_2399_, v_i_2400_, v_b_2401_);
return v___x_2405_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2394_ = stack[0].m_obj;
lean_object* v_fst_2395_ = stack[1].m_obj;
lean_object* v_snd_2396_ = stack[2].m_obj;
lean_object* v___x_2397_ = stack[3].m_obj;
lean_object* v_as_2398_ = stack[4].m_obj;
size_t v_sz_2399_ = stack[5].m_num;
size_t v_i_2400_ = stack[6].m_num;
lean_object* v_b_2401_ = stack[7].m_obj;
lean_object* v___y_2402_ = stack[8].m_obj;
lean_object* v___y_2403_ = stack[9].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2394_, v_fst_2395_, v_snd_2396_, v___x_2397_, v_as_2398_, v_sz_2399_, v_i_2400_, v_b_2401_, v___y_2402_, v___y_2403_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v___x_2407_, lean_object* v_fst_2408_, lean_object* v_snd_2409_, lean_object* v___x_2410_, lean_object* v_as_2411_, lean_object* v_sz_2412_, lean_object* v_i_2413_, lean_object* v_b_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
size_t v_sz_boxed_2418_; size_t v_i_boxed_2419_; lean_object* v_res_2420_; 
v_sz_boxed_2418_ = lean_unbox_usize(v_sz_2412_);
lean_dec(v_sz_2412_);
v_i_boxed_2419_ = lean_unbox_usize(v_i_2413_);
lean_dec(v_i_2413_);
v_res_2420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2407_, v_fst_2408_, v_snd_2409_, v___x_2410_, v_as_2411_, v_sz_boxed_2418_, v_i_boxed_2419_, v_b_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec_ref(v_as_2411_);
return v_res_2420_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(lean_object* v_msgData_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_2421_, v___y_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2421_ = stack[0].m_obj;
lean_object* v___y_2422_ = stack[1].m_obj;
lean_object* v___y_2423_ = stack[2].m_obj;
lean_object* v_res_2426_;
v_res_2426_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(v_msgData_2421_, v___y_2422_, v___y_2423_);
stack->m_obj
 = v_res_2426_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___boxed(lean_object* v_msgData_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(v_msgData_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2431_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_object* v_00_u03b2_2432_, lean_object* v_a_2433_, lean_object* v_x_2434_){
_start:
{
uint8_t v___x_2435_; 
v___x_2435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_2433_, v_x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2433_ = stack[1].m_obj;
lean_object* v_x_2434_ = stack[2].m_obj;
uint8_t v_res_2436_;
v_res_2436_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_box(0), v_a_2433_, v_x_2434_);
stack->m_num = v_res_2436_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2437_, lean_object* v_a_2438_, lean_object* v_x_2439_){
_start:
{
uint8_t v_res_2440_; lean_object* v_r_2441_; 
v_res_2440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(v_00_u03b2_2437_, v_a_2438_, v_x_2439_);
lean_dec(v_x_2439_);
lean_dec_ref(v_a_2438_);
v_r_2441_ = lean_box(v_res_2440_);
return v_r_2441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3(lean_object* v_00_u03b2_2442_, lean_object* v_data_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_data_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2445_, lean_object* v_i_2446_, lean_object* v_source_2447_, lean_object* v_target_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v_i_2446_, v_source_2447_, v_target_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_x_2451_, v_x_2452_);
return v___x_2453_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2462_; 
lean_inc(v___y_2456_);
lean_inc_ref(v___y_2455_);
v___x_2462_ = lean_apply_7(v_x_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, lean_box(0));
return v___x_2462_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2454_ = stack[0].m_obj;
lean_object* v___y_2455_ = stack[1].m_obj;
lean_object* v___y_2456_ = stack[2].m_obj;
lean_object* v___y_2457_ = stack[3].m_obj;
lean_object* v___y_2458_ = stack[4].m_obj;
lean_object* v___y_2459_ = stack[5].m_obj;
lean_object* v___y_2460_ = stack[6].m_obj;
lean_object* v_res_2463_;
v_res_2463_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
stack->m_obj
 = v_res_2463_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
return v_res_2472_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2473_, lean_object* v_x_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v___f_2482_; lean_object* v___x_2483_; 
lean_inc(v___y_2476_);
lean_inc_ref(v___y_2475_);
v___f_2482_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2482_, 0, v_x_2474_);
lean_closure_set(v___f_2482_, 1, v___y_2475_);
lean_closure_set(v___f_2482_, 2, v___y_2476_);
v___x_2483_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2473_, v___f_2482_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_2483_) == 0)
{
return v___x_2483_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2473_ = stack[0].m_obj;
lean_object* v_x_2474_ = stack[1].m_obj;
lean_object* v___y_2475_ = stack[2].m_obj;
lean_object* v___y_2476_ = stack[3].m_obj;
lean_object* v___y_2477_ = stack[4].m_obj;
lean_object* v___y_2478_ = stack[5].m_obj;
lean_object* v___y_2479_ = stack[6].m_obj;
lean_object* v___y_2480_ = stack[7].m_obj;
lean_object* v_res_2492_;
v_res_2492_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2473_, v_x_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
stack->m_obj
 = v_res_2492_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2493_, lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2493_, v_x_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2502_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2503_, lean_object* v_mvarId_2504_, lean_object* v_x_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2504_, v_x_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2504_ = stack[1].m_obj;
lean_object* v_x_2505_ = stack[2].m_obj;
lean_object* v___y_2506_ = stack[3].m_obj;
lean_object* v___y_2507_ = stack[4].m_obj;
lean_object* v___y_2508_ = stack[5].m_obj;
lean_object* v___y_2509_ = stack[6].m_obj;
lean_object* v___y_2510_ = stack[7].m_obj;
lean_object* v___y_2511_ = stack[8].m_obj;
lean_object* v_res_2514_;
v_res_2514_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_box(0), v_mvarId_2504_, v_x_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
stack->m_obj
 = v_res_2514_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2515_, lean_object* v_mvarId_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2515_, v_mvarId_2516_, v_x_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2525_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_2530_ = stack[0].m_obj;
lean_object* v___y_2531_ = stack[1].m_obj;
lean_object* v___y_2532_ = stack[2].m_obj;
lean_object* v___y_2533_ = stack[3].m_obj;
lean_object* v___y_2534_ = stack[4].m_obj;
lean_object* v___y_2535_ = stack[5].m_obj;
lean_object* v___y_2536_ = stack[6].m_obj;
lean_object* v___y_2537_ = stack[7].m_obj;
lean_object* v___y_2538_ = stack[8].m_obj;
lean_object* v_res_2542_;
v_res_2542_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
stack->m_obj
 = v_res_2542_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2553_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_2554_ = stack[0].m_obj;
lean_object* v___y_2555_ = stack[1].m_obj;
lean_object* v___y_2556_ = stack[2].m_obj;
lean_object* v___y_2557_ = stack[3].m_obj;
lean_object* v___y_2558_ = stack[4].m_obj;
lean_object* v_res_2562_;
v_res_2562_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
stack->m_obj
 = v_res_2562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2569_;
}
}
uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2570_, lean_object* v_x_2571_){
_start:
{
return v___x_2570_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2570_ = stack[0].m_num;
lean_object* v_x_2571_ = stack[1].m_obj;
uint8_t v_res_2572_;
v_res_2572_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_2570_, v_x_2571_);
stack->m_num = v_res_2572_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2573_, lean_object* v_x_2574_){
_start:
{
uint8_t v___x_11110__boxed_2575_; uint8_t v_res_2576_; lean_object* v_r_2577_; 
v___x_11110__boxed_2575_ = lean_unbox(v___x_2573_);
v_res_2576_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_11110__boxed_2575_, v_x_2574_);
lean_dec(v_x_2574_);
v_r_2577_ = lean_box(v_res_2576_);
return v_r_2577_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; lean_object* v_env_2585_; uint8_t v___x_2586_; lean_object* v_env_2587_; lean_object* v___x_2588_; lean_object* v_toCold_2589_; lean_object* v_mctx_2590_; lean_object* v_lctx_2591_; lean_object* v_options_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2584_ = lean_st_ref_get(v___y_2582_);
v_env_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc_ref(v_env_2585_);
lean_dec(v___x_2584_);
v___x_2586_ = 0;
v_env_2587_ = l_Lean_Environment_setRecordingDeps(v_env_2585_, v___x_2586_);
v___x_2588_ = lean_st_ref_get(v___y_2580_);
v_toCold_2589_ = lean_ctor_get(v___y_2581_, 0);
v_mctx_2590_ = lean_ctor_get(v___x_2588_, 0);
lean_inc_ref(v_mctx_2590_);
lean_dec(v___x_2588_);
v_lctx_2591_ = lean_ctor_get(v___y_2579_, 2);
v_options_2592_ = lean_ctor_get(v_toCold_2589_, 2);
lean_inc_ref(v_options_2592_);
lean_inc_ref(v_lctx_2591_);
v___x_2593_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2593_, 0, v_env_2587_);
lean_ctor_set(v___x_2593_, 1, v_mctx_2590_);
lean_ctor_set(v___x_2593_, 2, v_lctx_2591_);
lean_ctor_set(v___x_2593_, 3, v_options_2592_);
v___x_2594_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v_msgData_2578_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2578_ = stack[0].m_obj;
lean_object* v___y_2579_ = stack[1].m_obj;
lean_object* v___y_2580_ = stack[2].m_obj;
lean_object* v___y_2581_ = stack[3].m_obj;
lean_object* v___y_2582_ = stack[4].m_obj;
lean_object* v_res_2596_;
v_res_2596_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
stack->m_obj
 = v_res_2596_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
return v_res_2603_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2604_, lean_object* v_msg_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_ref_2611_; lean_object* v___x_2612_; lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2658_; 
v_ref_2611_ = lean_ctor_get(v___y_2608_, 2);
v___x_2612_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2658_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2658_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; lean_object* v_traceState_2618_; lean_object* v_env_2619_; lean_object* v_nextMacroScope_2620_; lean_object* v_ngen_2621_; lean_object* v_auxDeclNGen_2622_; lean_object* v_cache_2623_; lean_object* v_recordedDeps_2624_; lean_object* v_messages_2625_; lean_object* v_infoState_2626_; lean_object* v_snapshotTasks_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2657_; 
v___x_2617_ = lean_st_ref_take(v___y_2609_);
v_traceState_2618_ = lean_ctor_get(v___x_2617_, 4);
v_env_2619_ = lean_ctor_get(v___x_2617_, 0);
v_nextMacroScope_2620_ = lean_ctor_get(v___x_2617_, 1);
v_ngen_2621_ = lean_ctor_get(v___x_2617_, 2);
v_auxDeclNGen_2622_ = lean_ctor_get(v___x_2617_, 3);
v_cache_2623_ = lean_ctor_get(v___x_2617_, 5);
v_recordedDeps_2624_ = lean_ctor_get(v___x_2617_, 6);
v_messages_2625_ = lean_ctor_get(v___x_2617_, 7);
v_infoState_2626_ = lean_ctor_get(v___x_2617_, 8);
v_snapshotTasks_2627_ = lean_ctor_get(v___x_2617_, 9);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2629_ = v___x_2617_;
v_isShared_2630_ = v_isSharedCheck_2657_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_snapshotTasks_2627_);
lean_inc(v_infoState_2626_);
lean_inc(v_messages_2625_);
lean_inc(v_recordedDeps_2624_);
lean_inc(v_cache_2623_);
lean_inc(v_traceState_2618_);
lean_inc(v_auxDeclNGen_2622_);
lean_inc(v_ngen_2621_);
lean_inc(v_nextMacroScope_2620_);
lean_inc(v_env_2619_);
lean_dec(v___x_2617_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2657_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
uint64_t v_tid_2631_; lean_object* v_traces_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2656_; 
v_tid_2631_ = lean_ctor_get_uint64(v_traceState_2618_, sizeof(void*)*1);
v_traces_2632_ = lean_ctor_get(v_traceState_2618_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_traceState_2618_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2634_ = v_traceState_2618_;
v_isShared_2635_ = v_isSharedCheck_2656_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_traces_2632_);
lean_dec(v_traceState_2618_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2656_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; double v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_box(0);
v___x_2638_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2639_ = 0;
v___x_2640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2641_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2641_, 0, v_cls_2604_);
lean_ctor_set(v___x_2641_, 1, v___x_2637_);
lean_ctor_set(v___x_2641_, 2, v___x_2640_);
lean_ctor_set_float(v___x_2641_, sizeof(void*)*3, v___x_2638_);
lean_ctor_set_float(v___x_2641_, sizeof(void*)*3 + 8, v___x_2638_);
lean_ctor_set_uint8(v___x_2641_, sizeof(void*)*3 + 16, v___x_2639_);
v___x_2642_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2643_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set(v___x_2643_, 1, v_a_2613_);
lean_ctor_set(v___x_2643_, 2, v___x_2642_);
lean_inc(v_ref_2611_);
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v_ref_2611_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = l_Lean_PersistentArray_push___redArg(v_traces_2632_, v___x_2644_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2645_);
v___x_2647_ = v___x_2634_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2645_);
lean_ctor_set_uint64(v_reuseFailAlloc_2655_, sizeof(void*)*1, v_tid_2631_);
v___x_2647_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2649_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 4, v___x_2647_);
v___x_2649_ = v___x_2629_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_env_2619_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_nextMacroScope_2620_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_ngen_2621_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_auxDeclNGen_2622_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2654_, 5, v_cache_2623_);
lean_ctor_set(v_reuseFailAlloc_2654_, 6, v_recordedDeps_2624_);
lean_ctor_set(v_reuseFailAlloc_2654_, 7, v_messages_2625_);
lean_ctor_set(v_reuseFailAlloc_2654_, 8, v_infoState_2626_);
lean_ctor_set(v_reuseFailAlloc_2654_, 9, v_snapshotTasks_2627_);
v___x_2649_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2650_ = lean_st_ref_put(v___y_2609_, v___x_2649_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2636_);
v___x_2652_ = v___x_2615_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2636_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2604_ = stack[0].m_obj;
lean_object* v_msg_2605_ = stack[1].m_obj;
lean_object* v___y_2606_ = stack[2].m_obj;
lean_object* v___y_2607_ = stack[3].m_obj;
lean_object* v___y_2608_ = stack[4].m_obj;
lean_object* v___y_2609_ = stack[5].m_obj;
lean_object* v_res_2659_;
v_res_2659_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2604_, v_msg_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
stack->m_obj
 = v_res_2659_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2660_, lean_object* v_msg_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2660_, v_msg_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2667_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
return v___x_2670_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2671_, lean_object* v___f_2672_, lean_object* v___x_2673_, lean_object* v___x_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v_a_2684_; lean_object* v___y_2688_; lean_object* v___x_2702_; 
v___x_2682_ = lean_st_mk_ref(v___x_2671_);
v___x_2702_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2682_, v___y_2676_, v___y_2678_, v___y_2680_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2674_, v___x_2673_, v___x_2682_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; 
lean_dec(v_a_2703_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v___f_2672_);
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v_a_2684_ = v_a_2705_;
goto v___jp_2683_;
}
else
{
lean_object* v_a_2706_; uint8_t v___y_2708_; uint8_t v___x_2752_; 
v_a_2706_ = lean_ctor_get(v___x_2704_, 0);
v___x_2752_ = l_Lean_Exception_isInterrupt(v_a_2706_);
if (v___x_2752_ == 0)
{
uint8_t v___x_2753_; 
lean_inc(v_a_2706_);
v___x_2753_ = l_Lean_Exception_isRuntime(v_a_2706_);
v___y_2708_ = v___x_2753_;
goto v___jp_2707_;
}
else
{
v___y_2708_ = v___x_2752_;
goto v___jp_2707_;
}
v___jp_2707_:
{
if (v___y_2708_ == 0)
{
lean_object* v___x_2709_; 
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2704_, 1);
v___x_2709_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2703_, v___y_2708_, v___x_2682_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2742_; 
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v___x_2709_, 0);
lean_dec(v_unused_2743_);
v___x_2711_ = v___x_2709_;
v_isShared_2712_ = v_isSharedCheck_2742_;
goto v_resetjp_2710_;
}
else
{
lean_dec(v___x_2709_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2742_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
uint8_t v___x_2713_; 
v___x_2713_ = l_Lean_Exception_isInterrupt(v_a_2706_);
if (v___x_2713_ == 0)
{
uint8_t v___x_2714_; 
lean_inc(v_a_2706_);
v___x_2714_ = l_Lean_Exception_isMaxRecDepth(v_a_2706_);
if (v___x_2714_ == 0)
{
lean_object* v_toCold_2715_; lean_object* v_options_2716_; uint8_t v_hasTrace_2717_; 
lean_del_object(v___x_2711_);
v_toCold_2715_ = lean_ctor_get(v___y_2679_, 0);
v_options_2716_ = lean_ctor_get(v_toCold_2715_, 2);
v_hasTrace_2717_ = lean_ctor_get_uint8(v_options_2716_, sizeof(void*)*1);
if (v_hasTrace_2717_ == 0)
{
lean_dec(v_a_2706_);
goto v___jp_2699_;
}
else
{
lean_object* v_inheritedTraceOptions_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v_inheritedTraceOptions_2718_ = lean_ctor_get(v_toCold_2715_, 11);
v___x_2719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2720_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2718_, v_options_2716_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_dec(v_a_2706_);
goto v___jp_2699_;
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2722_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2723_ = l_Lean_Exception_toMessageData(v_a_2706_);
v___x_2724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2722_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2719_, v___x_2724_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
lean_inc(v___x_2682_);
v___x_2727_ = lean_apply_10(v___f_2672_, v_a_2726_, v___x_2673_, v___x_2682_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, lean_box(0));
v___y_2688_ = v___x_2727_;
goto v___jp_2687_;
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v___x_2682_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v___f_2672_);
v_a_2728_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2725_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2725_);
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
}
}
}
else
{
lean_object* v___x_2737_; 
lean_dec(v___x_2682_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v___f_2672_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 1);
lean_ctor_set(v___x_2711_, 0, v_a_2706_);
v___x_2737_ = v___x_2711_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2706_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
else
{
lean_object* v___x_2740_; 
lean_dec(v___x_2682_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v___f_2672_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 1);
lean_ctor_set(v___x_2711_, 0, v_a_2706_);
v___x_2740_ = v___x_2711_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2706_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_a_2706_);
lean_dec(v___x_2682_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v___f_2672_);
v_a_2744_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2709_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2709_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_dec(v_a_2703_);
lean_dec(v___x_2682_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v___f_2672_);
return v___x_2704_;
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v___x_2682_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___x_2674_);
lean_dec_ref(v___x_2673_);
lean_dec_ref(v___f_2672_);
v_a_2754_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2702_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2702_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
v___jp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_st_ref_get(v___x_2682_);
lean_dec(v___x_2682_);
lean_dec(v___x_2685_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_a_2684_);
return v___x_2686_;
}
v___jp_2687_:
{
if (lean_obj_tag(v___y_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v_a_2690_; 
v_a_2689_ = lean_ctor_get(v___y_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___y_2688_, 1);
v_a_2690_ = lean_ctor_get(v_a_2689_, 0);
lean_inc(v_a_2690_);
lean_dec(v_a_2689_);
v_a_2684_ = v_a_2690_;
goto v___jp_2683_;
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v___x_2682_);
v_a_2691_ = lean_ctor_get(v___y_2688_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___y_2688_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___y_2688_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___y_2688_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
v___jp_2699_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_box(0);
lean_inc(v___x_2682_);
v___x_2701_ = lean_apply_10(v___f_2672_, v___x_2700_, v___x_2673_, v___x_2682_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, lean_box(0));
v___y_2688_ = v___x_2701_;
goto v___jp_2687_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2671_ = stack[0].m_obj;
lean_object* v___f_2672_ = stack[1].m_obj;
lean_object* v___x_2673_ = stack[2].m_obj;
lean_object* v___x_2674_ = stack[3].m_obj;
lean_object* v___y_2675_ = stack[4].m_obj;
lean_object* v___y_2676_ = stack[5].m_obj;
lean_object* v___y_2677_ = stack[6].m_obj;
lean_object* v___y_2678_ = stack[7].m_obj;
lean_object* v___y_2679_ = stack[8].m_obj;
lean_object* v___y_2680_ = stack[9].m_obj;
lean_object* v_res_2762_;
v_res_2762_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2671_, v___f_2672_, v___x_2673_, v___x_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
stack->m_obj
 = v_res_2762_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2763_, lean_object* v___f_2764_, lean_object* v___x_2765_, lean_object* v___x_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2763_, v___f_2764_, v___x_2765_, v___x_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
return v_res_2774_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2775_, uint8_t v___x_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2775_, v___x_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2775_ = stack[0].m_obj;
uint8_t v___x_2776_ = stack[1].m_num;
lean_object* v___y_2777_ = stack[2].m_obj;
lean_object* v___y_2778_ = stack[3].m_obj;
lean_object* v___y_2779_ = stack[4].m_obj;
lean_object* v___y_2780_ = stack[5].m_obj;
lean_object* v___y_2781_ = stack[6].m_obj;
lean_object* v___y_2782_ = stack[7].m_obj;
lean_object* v_res_2785_;
v_res_2785_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2775_, v___x_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
stack->m_obj
 = v_res_2785_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
uint8_t v___x_11607__boxed_2795_; lean_object* v_res_2796_; 
v___x_11607__boxed_2795_ = lean_unbox(v___x_2787_);
v_res_2796_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2786_, v___x_11607__boxed_2795_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2796_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2797_, lean_object* v_msg_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_ref_2804_; lean_object* v___x_2805_; lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2851_; 
v_ref_2804_ = lean_ctor_get(v___y_2801_, 2);
v___x_2805_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2851_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2851_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; lean_object* v_traceState_2811_; lean_object* v_env_2812_; lean_object* v_nextMacroScope_2813_; lean_object* v_ngen_2814_; lean_object* v_auxDeclNGen_2815_; lean_object* v_cache_2816_; lean_object* v_recordedDeps_2817_; lean_object* v_messages_2818_; lean_object* v_infoState_2819_; lean_object* v_snapshotTasks_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2850_; 
v___x_2810_ = lean_st_ref_take(v___y_2802_);
v_traceState_2811_ = lean_ctor_get(v___x_2810_, 4);
v_env_2812_ = lean_ctor_get(v___x_2810_, 0);
v_nextMacroScope_2813_ = lean_ctor_get(v___x_2810_, 1);
v_ngen_2814_ = lean_ctor_get(v___x_2810_, 2);
v_auxDeclNGen_2815_ = lean_ctor_get(v___x_2810_, 3);
v_cache_2816_ = lean_ctor_get(v___x_2810_, 5);
v_recordedDeps_2817_ = lean_ctor_get(v___x_2810_, 6);
v_messages_2818_ = lean_ctor_get(v___x_2810_, 7);
v_infoState_2819_ = lean_ctor_get(v___x_2810_, 8);
v_snapshotTasks_2820_ = lean_ctor_get(v___x_2810_, 9);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2822_ = v___x_2810_;
v_isShared_2823_ = v_isSharedCheck_2850_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_snapshotTasks_2820_);
lean_inc(v_infoState_2819_);
lean_inc(v_messages_2818_);
lean_inc(v_recordedDeps_2817_);
lean_inc(v_cache_2816_);
lean_inc(v_traceState_2811_);
lean_inc(v_auxDeclNGen_2815_);
lean_inc(v_ngen_2814_);
lean_inc(v_nextMacroScope_2813_);
lean_inc(v_env_2812_);
lean_dec(v___x_2810_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2850_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
uint64_t v_tid_2824_; lean_object* v_traces_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2849_; 
v_tid_2824_ = lean_ctor_get_uint64(v_traceState_2811_, sizeof(void*)*1);
v_traces_2825_ = lean_ctor_get(v_traceState_2811_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_traceState_2811_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2827_ = v_traceState_2811_;
v_isShared_2828_ = v_isSharedCheck_2849_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_traces_2825_);
lean_dec(v_traceState_2811_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2849_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; double v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2832_ = 0;
v___x_2833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2834_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2834_, 0, v_cls_2797_);
lean_ctor_set(v___x_2834_, 1, v___x_2830_);
lean_ctor_set(v___x_2834_, 2, v___x_2833_);
lean_ctor_set_float(v___x_2834_, sizeof(void*)*3, v___x_2831_);
lean_ctor_set_float(v___x_2834_, sizeof(void*)*3 + 8, v___x_2831_);
lean_ctor_set_uint8(v___x_2834_, sizeof(void*)*3 + 16, v___x_2832_);
v___x_2835_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2836_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v_a_2806_);
lean_ctor_set(v___x_2836_, 2, v___x_2835_);
lean_inc(v_ref_2804_);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v_ref_2804_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = l_Lean_PersistentArray_push___redArg(v_traces_2825_, v___x_2837_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2838_);
v___x_2840_ = v___x_2827_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2838_);
lean_ctor_set_uint64(v_reuseFailAlloc_2848_, sizeof(void*)*1, v_tid_2824_);
v___x_2840_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2842_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 4, v___x_2840_);
v___x_2842_ = v___x_2822_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_env_2812_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_nextMacroScope_2813_);
lean_ctor_set(v_reuseFailAlloc_2847_, 2, v_ngen_2814_);
lean_ctor_set(v_reuseFailAlloc_2847_, 3, v_auxDeclNGen_2815_);
lean_ctor_set(v_reuseFailAlloc_2847_, 4, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2847_, 5, v_cache_2816_);
lean_ctor_set(v_reuseFailAlloc_2847_, 6, v_recordedDeps_2817_);
lean_ctor_set(v_reuseFailAlloc_2847_, 7, v_messages_2818_);
lean_ctor_set(v_reuseFailAlloc_2847_, 8, v_infoState_2819_);
lean_ctor_set(v_reuseFailAlloc_2847_, 9, v_snapshotTasks_2820_);
v___x_2842_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2843_ = lean_st_ref_put(v___y_2802_, v___x_2842_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2829_);
v___x_2845_ = v___x_2808_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2829_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2797_ = stack[0].m_obj;
lean_object* v_msg_2798_ = stack[1].m_obj;
lean_object* v___y_2799_ = stack[2].m_obj;
lean_object* v___y_2800_ = stack[3].m_obj;
lean_object* v___y_2801_ = stack[4].m_obj;
lean_object* v___y_2802_ = stack[5].m_obj;
lean_object* v_res_2852_;
v_res_2852_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2797_, v_msg_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
stack->m_obj
 = v_res_2852_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2853_, lean_object* v_msg_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2853_, v_msg_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
return v_res_2860_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2863_ = l_Lean_stringToMessageData(v___x_2862_);
return v___x_2863_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v___f_2864_, lean_object* v_term_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___y_2874_; lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2865_, v___x_2866_, v___x_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2904_; 
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___f_2864_);
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2904_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2904_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v_fst_2900_; lean_object* v___x_2902_; 
v_fst_2900_ = lean_ctor_get(v_a_2896_, 0);
lean_inc(v_fst_2900_);
lean_dec(v_a_2896_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v_fst_2900_);
v___x_2902_ = v___x_2898_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_fst_2900_);
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
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2945_; 
v_a_2905_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2907_ = v___x_2895_;
v_isShared_2908_ = v_isSharedCheck_2945_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2895_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2945_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
uint8_t v___y_2910_; uint8_t v___x_2943_; 
v___x_2943_ = l_Lean_Exception_isInterrupt(v_a_2905_);
if (v___x_2943_ == 0)
{
uint8_t v___x_2944_; 
lean_inc(v_a_2905_);
v___x_2944_ = l_Lean_Exception_isRuntime(v_a_2905_);
v___y_2910_ = v___x_2944_;
goto v___jp_2909_;
}
else
{
v___y_2910_ = v___x_2943_;
goto v___jp_2909_;
}
v___jp_2909_:
{
if (v___y_2910_ == 0)
{
uint8_t v___x_2911_; 
v___x_2911_ = l_Lean_Exception_isInterrupt(v_a_2905_);
if (v___x_2911_ == 0)
{
uint8_t v___x_2912_; 
lean_inc(v_a_2905_);
v___x_2912_ = l_Lean_Exception_isMaxRecDepth(v_a_2905_);
if (v___x_2912_ == 0)
{
lean_object* v_toCold_2913_; lean_object* v_options_2914_; uint8_t v_hasTrace_2915_; 
lean_del_object(v___x_2907_);
v_toCold_2913_ = lean_ctor_get(v___y_2870_, 0);
v_options_2914_ = lean_ctor_get(v_toCold_2913_, 2);
v_hasTrace_2915_ = lean_ctor_get_uint8(v_options_2914_, sizeof(void*)*1);
if (v_hasTrace_2915_ == 0)
{
lean_dec(v_a_2905_);
goto v___jp_2892_;
}
else
{
lean_object* v_inheritedTraceOptions_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; 
v_inheritedTraceOptions_2916_ = lean_ctor_get(v_toCold_2913_, 11);
v___x_2917_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2919_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2916_, v_options_2914_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_dec(v_a_2905_);
goto v___jp_2892_;
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2920_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2921_ = l_Lean_Exception_toMessageData(v_a_2905_);
v___x_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2917_, v___x_2922_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = lean_apply_6(v___f_2864_, v_a_2924_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, lean_box(0));
v___y_2874_ = v___x_2925_;
goto v___jp_2873_;
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___f_2864_);
v_a_2926_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2923_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2923_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
}
else
{
lean_object* v___x_2935_; 
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___f_2864_);
if (v_isShared_2908_ == 0)
{
v___x_2935_ = v___x_2907_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2905_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
else
{
lean_object* v___x_2938_; 
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___f_2864_);
if (v_isShared_2908_ == 0)
{
v___x_2938_ = v___x_2907_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2905_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_object* v___x_2941_; 
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___f_2864_);
if (v_isShared_2908_ == 0)
{
v___x_2941_ = v___x_2907_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2905_);
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
v___jp_2873_:
{
if (lean_obj_tag(v___y_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2883_; 
v_a_2875_ = lean_ctor_get(v___y_2874_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___y_2874_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2877_ = v___y_2874_;
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___y_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v_a_2879_; lean_object* v___x_2881_; 
v_a_2879_ = lean_ctor_get(v_a_2875_, 0);
lean_inc(v_a_2879_);
lean_dec(v_a_2875_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v_a_2879_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
v_a_2884_ = lean_ctor_get(v___y_2874_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___y_2874_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___y_2874_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___y_2874_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
v___jp_2892_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_box(0);
v___x_2894_ = lean_apply_6(v___f_2864_, v___x_2893_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, lean_box(0));
v___y_2874_ = v___x_2894_;
goto v___jp_2873_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2864_ = stack[0].m_obj;
lean_object* v_term_2865_ = stack[1].m_obj;
lean_object* v___x_2866_ = stack[2].m_obj;
lean_object* v___x_2867_ = stack[3].m_obj;
lean_object* v___y_2868_ = stack[4].m_obj;
lean_object* v___y_2869_ = stack[5].m_obj;
lean_object* v___y_2870_ = stack[6].m_obj;
lean_object* v___y_2871_ = stack[7].m_obj;
lean_object* v_res_2946_;
v_res_2946_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v___f_2864_, v_term_2865_, v___x_2866_, v___x_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
stack->m_obj
 = v_res_2946_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v___f_2947_, lean_object* v_term_2948_, lean_object* v___x_2949_, lean_object* v___x_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v___f_2947_, v_term_2948_, v___x_2949_, v___x_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2957_, lean_object* v_vals_2958_, lean_object* v_i_2959_, lean_object* v_k_2960_){
_start:
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = lean_array_get_size(v_keys_2957_);
v___x_2962_ = lean_nat_dec_lt(v_i_2959_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; 
lean_dec(v_i_2959_);
v___x_2963_ = lean_box(0);
return v___x_2963_;
}
else
{
lean_object* v_k_x27_2964_; uint8_t v___x_2965_; 
v_k_x27_2964_ = lean_array_fget_borrowed(v_keys_2957_, v_i_2959_);
v___x_2965_ = l_Lean_instBEqMVarId_beq(v_k_2960_, v_k_x27_2964_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_unsigned_to_nat(1u);
v___x_2967_ = lean_nat_add(v_i_2959_, v___x_2966_);
lean_dec(v_i_2959_);
v_i_2959_ = v___x_2967_;
goto _start;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_array_fget_borrowed(v_vals_2958_, v_i_2959_);
lean_dec(v_i_2959_);
lean_inc(v___x_2969_);
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
return v___x_2970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2971_, lean_object* v_vals_2972_, lean_object* v_i_2973_, lean_object* v_k_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2971_, v_vals_2972_, v_i_2973_, v_k_2974_);
lean_dec(v_k_2974_);
lean_dec_ref(v_vals_2972_);
lean_dec_ref(v_keys_2971_);
return v_res_2975_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2976_, size_t v_x_2977_, lean_object* v_x_2978_){
_start:
{
if (lean_obj_tag(v_x_2976_) == 0)
{
lean_object* v_es_2979_; lean_object* v___x_2980_; size_t v___x_2981_; size_t v___x_2982_; lean_object* v_j_2983_; lean_object* v___x_2984_; 
v_es_2979_ = lean_ctor_get(v_x_2976_, 0);
v___x_2980_ = lean_box(2);
v___x_2981_ = ((size_t)31ULL);
v___x_2982_ = lean_usize_land(v_x_2977_, v___x_2981_);
v_j_2983_ = lean_usize_to_nat(v___x_2982_);
v___x_2984_ = lean_array_get_borrowed(v___x_2980_, v_es_2979_, v_j_2983_);
lean_dec(v_j_2983_);
switch(lean_obj_tag(v___x_2984_))
{
case 0:
{
lean_object* v_key_2985_; lean_object* v_val_2986_; uint8_t v___x_2987_; 
v_key_2985_ = lean_ctor_get(v___x_2984_, 0);
v_val_2986_ = lean_ctor_get(v___x_2984_, 1);
v___x_2987_ = l_Lean_instBEqMVarId_beq(v_x_2978_, v_key_2985_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_box(0);
return v___x_2988_;
}
else
{
lean_object* v___x_2989_; 
lean_inc(v_val_2986_);
v___x_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_val_2986_);
return v___x_2989_;
}
}
case 1:
{
lean_object* v_node_2990_; size_t v___x_2991_; size_t v___x_2992_; 
v_node_2990_ = lean_ctor_get(v___x_2984_, 0);
v___x_2991_ = ((size_t)5ULL);
v___x_2992_ = lean_usize_shift_right(v_x_2977_, v___x_2991_);
v_x_2976_ = v_node_2990_;
v_x_2977_ = v___x_2992_;
goto _start;
}
default: 
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_box(0);
return v___x_2994_;
}
}
}
else
{
lean_object* v_ks_2995_; lean_object* v_vs_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_ks_2995_ = lean_ctor_get(v_x_2976_, 0);
v_vs_2996_ = lean_ctor_get(v_x_2976_, 1);
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2995_, v_vs_2996_, v___x_2997_, v_x_2978_);
return v___x_2998_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2976_ = stack[0].m_obj;
size_t v_x_2977_ = stack[1].m_num;
lean_object* v_x_2978_ = stack[2].m_obj;
lean_object* v_res_2999_;
v_res_2999_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2976_, v_x_2977_, v_x_2978_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_3000_, lean_object* v_x_3001_, lean_object* v_x_3002_){
_start:
{
size_t v_x_12086__boxed_3003_; lean_object* v_res_3004_; 
v_x_12086__boxed_3003_ = lean_unbox_usize(v_x_3001_);
lean_dec(v_x_3001_);
v_res_3004_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3000_, v_x_12086__boxed_3003_, v_x_3002_);
lean_dec(v_x_3002_);
lean_dec_ref(v_x_3000_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_3005_, lean_object* v_x_3006_){
_start:
{
uint64_t v___x_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v___x_3007_ = l_Lean_instHashableMVarId_hash(v_x_3006_);
v___x_3008_ = lean_uint64_to_usize(v___x_3007_);
v___x_3009_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3005_, v___x_3008_, v_x_3006_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_3010_, lean_object* v_x_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3010_, v_x_3011_);
lean_dec(v_x_3011_);
lean_dec_ref(v_x_3010_);
return v_res_3012_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v_mctx_3042_; lean_object* v_env_3043_; lean_object* v_opts_3044_; lean_object* v_namingCtx_3045_; lean_object* v_goal_3046_; lean_object* v_decls_3047_; lean_object* v___x_3048_; 
v_mctx_3042_ = lean_ctor_get(v_c_3038_, 3);
lean_inc_ref(v_mctx_3042_);
v_env_3043_ = lean_ctor_get(v_c_3038_, 2);
lean_inc_ref(v_env_3043_);
v_opts_3044_ = lean_ctor_get(v_c_3038_, 4);
lean_inc_ref(v_opts_3044_);
v_namingCtx_3045_ = lean_ctor_get(v_c_3038_, 5);
lean_inc_ref(v_namingCtx_3045_);
v_goal_3046_ = lean_ctor_get(v_c_3038_, 6);
lean_inc(v_goal_3046_);
lean_dec_ref(v_c_3038_);
v_decls_3047_ = lean_ctor_get(v_mctx_3042_, 5);
v___x_3048_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3047_, v_goal_3046_);
if (lean_obj_tag(v___x_3048_) == 1)
{
lean_object* v_val_3049_; lean_object* v_lctx_3050_; lean_object* v___f_3051_; lean_object* v___f_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___f_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; lean_object* v_term_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___f_3064_; lean_object* v___x_3065_; 
v_val_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_val_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v_lctx_3050_ = lean_ctor_get(v_val_3049_, 1);
lean_inc_ref(v_lctx_3050_);
lean_dec(v_val_3049_);
v___f_3051_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_3052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_3053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_3054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_3055_ = lean_box(0);
lean_inc(v_goal_3046_);
v___x_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3056_, 0, v_goal_3046_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___f_3057_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3057_, 0, v___x_3056_);
lean_closure_set(v___f_3057_, 1, v___f_3051_);
lean_closure_set(v___f_3057_, 2, v___x_3054_);
lean_closure_set(v___f_3057_, 3, v___x_3053_);
v___x_3058_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_3058_, 0, lean_box(0));
lean_closure_set(v___x_3058_, 1, v_goal_3046_);
lean_closure_set(v___x_3058_, 2, v___f_3057_);
v___x_3059_ = 1;
v___x_3060_ = lean_box(v___x_3059_);
v_term_3061_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3061_, 0, v___x_3058_);
lean_closure_set(v_term_3061_, 1, v___x_3060_);
v___x_3062_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3064_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3064_, 0, v___f_3052_);
lean_closure_set(v___f_3064_, 1, v_term_3061_);
lean_closure_set(v___f_3064_, 2, v___x_3062_);
lean_closure_set(v___f_3064_, 3, v___x_3063_);
v___x_3065_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3043_, v_mctx_3042_, v_lctx_3050_, v_opts_3044_, v_namingCtx_3045_, v___f_3064_, v_a_3039_, v_a_3040_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_dec(v___x_3048_);
lean_dec(v_goal_3046_);
lean_dec_ref(v_namingCtx_3045_);
lean_dec_ref(v_opts_3044_);
lean_dec_ref(v_env_3043_);
lean_dec_ref(v_mctx_3042_);
v___x_3066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
return v___x_3067_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3038_ = stack[0].m_obj;
lean_object* v_a_3039_ = stack[1].m_obj;
lean_object* v_a_3040_ = stack[2].m_obj;
lean_object* v_res_3068_;
v_res_3068_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3038_, v_a_3039_, v_a_3040_);
stack->m_obj
 = v_res_3068_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3069_, v_a_3070_, v_a_3071_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3075_, v_x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3078_, lean_object* v_x_3079_, lean_object* v_x_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3078_, v_x_3079_, v_x_3080_);
lean_dec(v_x_3080_);
lean_dec_ref(v_x_3079_);
return v_res_3081_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3082_, lean_object* v_msg_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3082_, v_msg_3083_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3082_ = stack[0].m_obj;
lean_object* v_msg_3083_ = stack[1].m_obj;
lean_object* v___y_3084_ = stack[2].m_obj;
lean_object* v___y_3085_ = stack[3].m_obj;
lean_object* v___y_3086_ = stack[4].m_obj;
lean_object* v___y_3087_ = stack[5].m_obj;
lean_object* v___y_3088_ = stack[6].m_obj;
lean_object* v___y_3089_ = stack[7].m_obj;
lean_object* v___y_3090_ = stack[8].m_obj;
lean_object* v___y_3091_ = stack[9].m_obj;
lean_object* v_res_3094_;
v_res_3094_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3082_, v_msg_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
stack->m_obj
 = v_res_3094_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3095_, lean_object* v_msg_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3095_, v_msg_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
return v_res_3106_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3107_, lean_object* v_x_3108_, size_t v_x_3109_, lean_object* v_x_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3108_, v_x_3109_, v_x_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3108_ = stack[1].m_obj;
size_t v_x_3109_ = stack[2].m_num;
lean_object* v_x_3110_ = stack[3].m_obj;
lean_object* v_res_3112_;
v_res_3112_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_box(0), v_x_3108_, v_x_3109_, v_x_3110_);
stack->m_obj
 = v_res_3112_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3113_, lean_object* v_x_3114_, lean_object* v_x_3115_, lean_object* v_x_3116_){
_start:
{
size_t v_x_12444__boxed_3117_; lean_object* v_res_3118_; 
v_x_12444__boxed_3117_ = lean_unbox_usize(v_x_3115_);
lean_dec(v_x_3115_);
v_res_3118_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3113_, v_x_3114_, v_x_12444__boxed_3117_, v_x_3116_);
lean_dec(v_x_3116_);
lean_dec_ref(v_x_3114_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3119_, lean_object* v_keys_3120_, lean_object* v_vals_3121_, lean_object* v_heq_3122_, lean_object* v_i_3123_, lean_object* v_k_3124_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3120_, v_vals_3121_, v_i_3123_, v_k_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3126_, lean_object* v_keys_3127_, lean_object* v_vals_3128_, lean_object* v_heq_3129_, lean_object* v_i_3130_, lean_object* v_k_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3126_, v_keys_3127_, v_vals_3128_, v_heq_3129_, v_i_3130_, v_k_3131_);
lean_dec(v_k_3131_);
lean_dec_ref(v_vals_3128_);
lean_dec_ref(v_keys_3127_);
return v_res_3132_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3135_, lean_object* v___x_3136_, lean_object* v_ref_3137_, lean_object* v_a_3138_, lean_object* v___x_3139_, lean_object* v___x_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
if (v___x_3135_ == 0)
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3136_);
v___x_3145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3146_ = lean_box(0);
v___x_3147_ = 4;
v___x_3148_ = l_Lean_MessageData_nil;
v___x_3149_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3137_, v_a_3138_, v___x_3144_, v___x_3145_, v___x_3146_, v___x_3147_, v___x_3148_, v___y_3141_, v___y_3142_);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3150_ = lean_array_get(v___x_3139_, v_a_3138_, v___x_3140_);
lean_dec_ref(v_a_3138_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3136_);
v___x_3152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3153_ = lean_box(0);
v___x_3154_ = 4;
v___x_3155_ = l_Lean_MessageData_nil;
v___x_3156_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3137_, v___x_3150_, v___x_3151_, v___x_3152_, v___x_3153_, v___x_3154_, v___x_3155_, v___y_3141_, v___y_3142_);
return v___x_3156_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3135_ = stack[0].m_num;
lean_object* v___x_3136_ = stack[1].m_obj;
lean_object* v_ref_3137_ = stack[2].m_obj;
lean_object* v_a_3138_ = stack[3].m_obj;
lean_object* v___x_3139_ = stack[4].m_obj;
lean_object* v___x_3140_ = stack[5].m_obj;
lean_object* v___y_3141_ = stack[6].m_obj;
lean_object* v___y_3142_ = stack[7].m_obj;
lean_object* v_res_3157_;
v_res_3157_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3135_, v___x_3136_, v_ref_3137_, v_a_3138_, v___x_3139_, v___x_3140_, v___y_3141_, v___y_3142_);
stack->m_obj
 = v_res_3157_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v_ref_3160_, lean_object* v_a_3161_, lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
uint8_t v___x_3494__boxed_3167_; lean_object* v_res_3168_; 
v___x_3494__boxed_3167_ = lean_unbox(v___x_3158_);
v_res_3168_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3494__boxed_3167_, v___x_3159_, v_ref_3160_, v_a_3161_, v___x_3162_, v___x_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___x_3163_);
lean_dec_ref(v___x_3162_);
return v_res_3168_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3169_, uint8_t v___y_3170_, lean_object* v_x_3171_){
_start:
{
if (lean_obj_tag(v_x_3171_) == 1)
{
lean_object* v_pre_3172_; 
v_pre_3172_ = lean_ctor_get(v_x_3171_, 0);
if (lean_obj_tag(v_pre_3172_) == 0)
{
lean_object* v_str_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v_str_3173_ = lean_ctor_get(v_x_3171_, 1);
v___x_3174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1));
v___x_3175_ = lean_string_dec_eq(v_str_3173_, v___x_3174_);
if (v___x_3175_ == 0)
{
return v___x_3175_;
}
else
{
return v_suppressElabErrors_3169_;
}
}
else
{
return v___y_3170_;
}
}
else
{
return v___y_3170_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_3169_ = stack[0].m_num;
uint8_t v___y_3170_ = stack[1].m_num;
lean_object* v_x_3171_ = stack[2].m_obj;
uint8_t v_res_3176_;
v_res_3176_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_3169_, v___y_3170_, v_x_3171_);
stack->m_num = v_res_3176_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3177_, lean_object* v___y_3178_, lean_object* v_x_3179_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3180_; uint8_t v___y_3578__boxed_3181_; uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_suppressElabErrors_boxed_3180_ = lean_unbox(v_suppressElabErrors_3177_);
v___y_3578__boxed_3181_ = lean_unbox(v___y_3178_);
v_res_3182_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3180_, v___y_3578__boxed_3181_, v_x_3179_);
lean_dec(v_x_3179_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3184_, lean_object* v_msgData_3185_, uint8_t v_severity_3186_, uint8_t v_isSilent_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___y_3192_; uint8_t v___y_3193_; lean_object* v___y_3194_; uint8_t v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; uint8_t v___y_3257_; lean_object* v___y_3258_; uint8_t v___y_3259_; uint8_t v___y_3260_; lean_object* v___y_3261_; uint8_t v___y_3285_; uint8_t v___y_3286_; uint8_t v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; uint8_t v___y_3293_; uint8_t v___y_3294_; uint8_t v___y_3295_; uint8_t v___x_3310_; uint8_t v___y_3312_; uint8_t v___y_3313_; uint8_t v___y_3314_; uint8_t v___y_3316_; uint8_t v___x_3328_; 
v___x_3310_ = 2;
v___x_3328_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3186_, v___x_3310_);
if (v___x_3328_ == 0)
{
v___y_3316_ = v___x_3328_;
goto v___jp_3315_;
}
else
{
uint8_t v___x_3329_; 
lean_inc_ref(v_msgData_3185_);
v___x_3329_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3185_);
v___y_3316_ = v___x_3329_;
goto v___jp_3315_;
}
v___jp_3191_:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Elab_Command_getScope___redArg(v___y_3199_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v_currNamespace_3202_; lean_object* v___x_3203_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v_currNamespace_3202_ = lean_ctor_get(v_a_3201_, 2);
lean_inc(v_currNamespace_3202_);
lean_dec(v_a_3201_);
v___x_3203_ = l_Lean_Elab_Command_getScope___redArg(v___y_3199_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3239_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3239_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3239_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v_openDecls_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_env_3213_; lean_object* v_messages_3214_; lean_object* v_scopes_3215_; lean_object* v_usedQuotCtxts_3216_; lean_object* v_nextMacroScope_3217_; lean_object* v_maxRecDepth_3218_; lean_object* v_ngen_3219_; lean_object* v_auxDeclNGen_3220_; lean_object* v_infoState_3221_; lean_object* v_traceState_3222_; lean_object* v_snapshotTasks_3223_; lean_object* v_prevLinterStates_3224_; lean_object* v_codeQualityEntryTasks_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3238_; 
v_openDecls_3208_ = lean_ctor_get(v_a_3204_, 3);
lean_inc(v_openDecls_3208_);
lean_dec(v_a_3204_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v_currNamespace_3202_);
lean_ctor_set(v___x_3209_, 1, v_openDecls_3208_);
v___x_3210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v___y_3198_);
lean_inc_ref(v___y_3192_);
lean_inc_ref(v___y_3197_);
v___x_3211_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3211_, 0, v___y_3197_);
lean_ctor_set(v___x_3211_, 1, v___y_3194_);
lean_ctor_set(v___x_3211_, 2, v___y_3196_);
lean_ctor_set(v___x_3211_, 3, v___y_3192_);
lean_ctor_set(v___x_3211_, 4, v___x_3210_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*5, v___y_3193_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*5 + 1, v___y_3195_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*5 + 2, v_isSilent_3187_);
v___x_3212_ = lean_st_ref_take(v___y_3199_);
v_env_3213_ = lean_ctor_get(v___x_3212_, 0);
v_messages_3214_ = lean_ctor_get(v___x_3212_, 1);
v_scopes_3215_ = lean_ctor_get(v___x_3212_, 2);
v_usedQuotCtxts_3216_ = lean_ctor_get(v___x_3212_, 3);
v_nextMacroScope_3217_ = lean_ctor_get(v___x_3212_, 4);
v_maxRecDepth_3218_ = lean_ctor_get(v___x_3212_, 5);
v_ngen_3219_ = lean_ctor_get(v___x_3212_, 6);
v_auxDeclNGen_3220_ = lean_ctor_get(v___x_3212_, 7);
v_infoState_3221_ = lean_ctor_get(v___x_3212_, 8);
v_traceState_3222_ = lean_ctor_get(v___x_3212_, 9);
v_snapshotTasks_3223_ = lean_ctor_get(v___x_3212_, 10);
v_prevLinterStates_3224_ = lean_ctor_get(v___x_3212_, 11);
v_codeQualityEntryTasks_3225_ = lean_ctor_get(v___x_3212_, 12);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3227_ = v___x_3212_;
v_isShared_3228_ = v_isSharedCheck_3238_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3225_);
lean_inc(v_prevLinterStates_3224_);
lean_inc(v_snapshotTasks_3223_);
lean_inc(v_traceState_3222_);
lean_inc(v_infoState_3221_);
lean_inc(v_auxDeclNGen_3220_);
lean_inc(v_ngen_3219_);
lean_inc(v_maxRecDepth_3218_);
lean_inc(v_nextMacroScope_3217_);
lean_inc(v_usedQuotCtxts_3216_);
lean_inc(v_scopes_3215_);
lean_inc(v_messages_3214_);
lean_inc(v_env_3213_);
lean_dec(v___x_3212_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3238_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3229_ = lean_box(0);
v___x_3230_ = l_Lean_MessageLog_add(v___x_3211_, v_messages_3214_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 1, v___x_3230_);
v___x_3232_ = v___x_3227_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_env_3213_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3237_, 2, v_scopes_3215_);
lean_ctor_set(v_reuseFailAlloc_3237_, 3, v_usedQuotCtxts_3216_);
lean_ctor_set(v_reuseFailAlloc_3237_, 4, v_nextMacroScope_3217_);
lean_ctor_set(v_reuseFailAlloc_3237_, 5, v_maxRecDepth_3218_);
lean_ctor_set(v_reuseFailAlloc_3237_, 6, v_ngen_3219_);
lean_ctor_set(v_reuseFailAlloc_3237_, 7, v_auxDeclNGen_3220_);
lean_ctor_set(v_reuseFailAlloc_3237_, 8, v_infoState_3221_);
lean_ctor_set(v_reuseFailAlloc_3237_, 9, v_traceState_3222_);
lean_ctor_set(v_reuseFailAlloc_3237_, 10, v_snapshotTasks_3223_);
lean_ctor_set(v_reuseFailAlloc_3237_, 11, v_prevLinterStates_3224_);
lean_ctor_set(v_reuseFailAlloc_3237_, 12, v_codeQualityEntryTasks_3225_);
v___x_3232_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3233_ = lean_st_ref_put(v___y_3199_, v___x_3232_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3229_);
v___x_3235_ = v___x_3206_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3229_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_currNamespace_3202_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3194_);
v_a_3240_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3203_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3203_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3194_);
v_a_3248_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3200_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3200_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
v___jp_3256_:
{
lean_object* v_fileName_3262_; lean_object* v_fileMap_3263_; uint8_t v_suppressElabErrors_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___f_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3283_; 
v_fileName_3262_ = lean_ctor_get(v___y_3188_, 0);
v_fileMap_3263_ = lean_ctor_get(v___y_3188_, 1);
v_suppressElabErrors_3264_ = lean_ctor_get_uint8(v___y_3188_, sizeof(void*)*10);
v___x_3265_ = lean_box(v_suppressElabErrors_3264_);
v___x_3266_ = lean_box(v___y_3257_);
v___f_3267_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3267_, 0, v___x_3265_);
lean_closure_set(v___f_3267_, 1, v___x_3266_);
v___x_3268_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3185_);
v___x_3269_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v___x_3268_, v___y_3189_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3283_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3283_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_inc_ref_n(v_fileMap_3263_, 2);
v___x_3274_ = l_Lean_FileMap_toPosition(v_fileMap_3263_, v___y_3258_);
lean_dec(v___y_3258_);
v___x_3275_ = l_Lean_FileMap_toPosition(v_fileMap_3263_, v___y_3261_);
lean_dec(v___y_3261_);
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
v___x_3277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3264_ == 0)
{
lean_del_object(v___x_3272_);
lean_dec_ref(v___f_3267_);
v___y_3192_ = v___x_3277_;
v___y_3193_ = v___y_3259_;
v___y_3194_ = v___x_3274_;
v___y_3195_ = v___y_3260_;
v___y_3196_ = v___x_3276_;
v___y_3197_ = v_fileName_3262_;
v___y_3198_ = v_a_3270_;
v___y_3199_ = v___y_3189_;
goto v___jp_3191_;
}
else
{
uint8_t v___x_3278_; 
lean_inc(v_a_3270_);
v___x_3278_ = l_Lean_MessageData_hasTag(v___f_3267_, v_a_3270_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
lean_dec_ref_known(v___x_3276_, 1);
lean_dec_ref(v___x_3274_);
lean_dec(v_a_3270_);
v___x_3279_ = lean_box(0);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3279_);
v___x_3281_ = v___x_3272_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
else
{
lean_del_object(v___x_3272_);
v___y_3192_ = v___x_3277_;
v___y_3193_ = v___y_3259_;
v___y_3194_ = v___x_3274_;
v___y_3195_ = v___y_3260_;
v___y_3196_ = v___x_3276_;
v___y_3197_ = v_fileName_3262_;
v___y_3198_ = v_a_3270_;
v___y_3199_ = v___y_3189_;
goto v___jp_3191_;
}
}
}
}
v___jp_3284_:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Syntax_getTailPos_x3f(v___y_3288_, v___y_3286_);
lean_dec(v___y_3288_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_inc(v___y_3289_);
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3289_;
v___y_3259_ = v___y_3286_;
v___y_3260_ = v___y_3287_;
v___y_3261_ = v___y_3289_;
goto v___jp_3256_;
}
else
{
lean_object* v_val_3291_; 
v_val_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v___x_3290_, 1);
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3289_;
v___y_3259_ = v___y_3286_;
v___y_3260_ = v___y_3287_;
v___y_3261_ = v_val_3291_;
goto v___jp_3256_;
}
}
v___jp_3292_:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Elab_Command_getRef___redArg(v___y_3188_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v_ref_3298_; lean_object* v___x_3299_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v_ref_3298_ = l_Lean_replaceRef(v_ref_3184_, v_a_3297_);
lean_dec(v_a_3297_);
v___x_3299_ = l_Lean_Syntax_getPos_x3f(v_ref_3298_, v___y_3294_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_unsigned_to_nat(0u);
v___y_3285_ = v___y_3293_;
v___y_3286_ = v___y_3294_;
v___y_3287_ = v___y_3295_;
v___y_3288_ = v_ref_3298_;
v___y_3289_ = v___x_3300_;
goto v___jp_3284_;
}
else
{
lean_object* v_val_3301_; 
v_val_3301_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_val_3301_);
lean_dec_ref_known(v___x_3299_, 1);
v___y_3285_ = v___y_3293_;
v___y_3286_ = v___y_3294_;
v___y_3287_ = v___y_3295_;
v___y_3288_ = v_ref_3298_;
v___y_3289_ = v_val_3301_;
goto v___jp_3284_;
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v_msgData_3185_);
v_a_3302_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3296_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3296_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
v___jp_3311_:
{
if (v___y_3314_ == 0)
{
v___y_3293_ = v___y_3312_;
v___y_3294_ = v___y_3313_;
v___y_3295_ = v_severity_3186_;
goto v___jp_3292_;
}
else
{
v___y_3293_ = v___y_3312_;
v___y_3294_ = v___y_3313_;
v___y_3295_ = v___x_3310_;
goto v___jp_3292_;
}
}
v___jp_3315_:
{
if (v___y_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v_scopes_3319_; lean_object* v___x_3320_; lean_object* v_opts_3321_; uint8_t v___x_3322_; uint8_t v___x_3323_; 
v___x_3317_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3318_ = lean_st_ref_get(v___y_3189_);
v_scopes_3319_ = lean_ctor_get(v___x_3318_, 2);
lean_inc(v_scopes_3319_);
lean_dec(v___x_3318_);
v___x_3320_ = l_List_head_x21___redArg(v___x_3317_, v_scopes_3319_);
lean_dec(v_scopes_3319_);
v_opts_3321_ = lean_ctor_get(v___x_3320_, 1);
lean_inc_ref(v_opts_3321_);
lean_dec(v___x_3320_);
v___x_3322_ = 1;
v___x_3323_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3186_, v___x_3322_);
if (v___x_3323_ == 0)
{
lean_dec_ref(v_opts_3321_);
v___y_3312_ = v___y_3316_;
v___y_3313_ = v___y_3316_;
v___y_3314_ = v___x_3323_;
goto v___jp_3311_;
}
else
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = l_Lean_warningAsError;
v___x_3325_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3321_, v___x_3324_);
lean_dec_ref(v_opts_3321_);
v___y_3312_ = v___y_3316_;
v___y_3313_ = v___y_3316_;
v___y_3314_ = v___x_3325_;
goto v___jp_3311_;
}
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_dec_ref(v_msgData_3185_);
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3184_ = stack[0].m_obj;
lean_object* v_msgData_3185_ = stack[1].m_obj;
uint8_t v_severity_3186_ = stack[2].m_num;
uint8_t v_isSilent_3187_ = stack[3].m_num;
lean_object* v___y_3188_ = stack[4].m_obj;
lean_object* v___y_3189_ = stack[5].m_obj;
lean_object* v_res_3330_;
v_res_3330_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3184_, v_msgData_3185_, v_severity_3186_, v_isSilent_3187_, v___y_3188_, v___y_3189_);
stack->m_obj
 = v_res_3330_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3331_, lean_object* v_msgData_3332_, lean_object* v_severity_3333_, lean_object* v_isSilent_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
uint8_t v_severity_boxed_3338_; uint8_t v_isSilent_boxed_3339_; lean_object* v_res_3340_; 
v_severity_boxed_3338_ = lean_unbox(v_severity_3333_);
v_isSilent_boxed_3339_ = lean_unbox(v_isSilent_3334_);
v_res_3340_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3331_, v_msgData_3332_, v_severity_boxed_3338_, v_isSilent_boxed_3339_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v_ref_3331_);
return v_res_3340_;
}
}
lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3341_, lean_object* v_msgData_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
uint8_t v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = 0;
v___x_3347_ = 0;
v___x_3348_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3341_, v_msgData_3342_, v___x_3346_, v___x_3347_, v___y_3343_, v___y_3344_);
return v___x_3348_;
}
}
LEAN_EXPORT void l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3341_ = stack[0].m_obj;
lean_object* v_msgData_3342_ = stack[1].m_obj;
lean_object* v___y_3343_ = stack[2].m_obj;
lean_object* v___y_3344_ = stack[3].m_obj;
lean_object* v_res_3349_;
v_res_3349_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3341_, v_msgData_3342_, v___y_3343_, v___y_3344_);
stack->m_obj
 = v_res_3349_;
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3350_, lean_object* v_msgData_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3350_, v_msgData_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v_ref_3350_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3357_, lean_object* v_x_3358_){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3360_ = lean_string_append(v___x_3359_, v___x_3357_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3361_, lean_object* v_x_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3361_, v_x_3362_);
lean_dec_ref(v_x_3362_);
lean_dec_ref(v___x_3361_);
return v_res_3363_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3366_ = l_Lean_stringToMessageData(v___x_3365_);
return v___x_3366_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3369_ = l_Lean_stringToMessageData(v___x_3368_);
return v___x_3369_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3372_ = l_Lean_stringToMessageData(v___x_3371_);
return v___x_3372_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3373_, uint8_t v___x_3374_, lean_object* v___x_3375_, lean_object* v_insertPos_3376_, lean_object* v_cmdLine_3377_, lean_object* v_ref_3378_, size_t v_sz_3379_, size_t v_i_3380_, lean_object* v_bs_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_usize_dec_lt(v_i_3380_, v_sz_3379_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; 
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___x_3373_);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_bs_3381_);
return v___x_3386_;
}
else
{
lean_object* v_v_3387_; lean_object* v___x_3388_; lean_object* v_bs_x27_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v_v_3387_ = lean_array_uget(v_bs_3381_, v_i_3380_);
v___x_3388_ = lean_unsigned_to_nat(0u);
v_bs_x27_3389_ = lean_array_uset(v_bs_3381_, v_i_3380_, v___x_3388_);
lean_inc(v_v_3387_);
v___x_3390_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3390_, 0, v_v_3387_);
v___x_3391_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3390_, v___y_3382_, v___y_3383_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___f_3395_; lean_object* v___x_3396_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = l_Std_Format_defWidth;
v___x_3394_ = l_Std_Format_pretty(v_a_3392_, v___x_3393_, v___x_3388_, v___x_3388_);
lean_inc_ref(v___x_3394_);
v___f_3395_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3395_, 0, v___x_3394_);
lean_inc_ref(v___x_3373_);
v___x_3396_ = lean_string_append(v___x_3373_, v___x_3394_);
lean_dec_ref(v___x_3394_);
if (v___x_3374_ == 0)
{
goto v___jp_3397_;
}
else
{
lean_object* v___x_3408_; lean_object* v_line_3409_; lean_object* v_column_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3445_; 
lean_inc_ref(v___x_3375_);
v___x_3408_ = l_Lean_FileMap_toPosition(v___x_3375_, v_insertPos_3376_);
v_line_3409_ = lean_ctor_get(v___x_3408_, 0);
v_column_3410_ = lean_ctor_get(v___x_3408_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3412_ = v___x_3408_;
v_isShared_3413_ = v_isSharedCheck_3445_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_column_3410_);
lean_inc(v_line_3409_);
lean_dec(v___x_3408_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3445_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3414_ = lean_nat_sub(v_line_3409_, v_cmdLine_3377_);
lean_dec(v_line_3409_);
v___x_3415_ = lean_unsigned_to_nat(1u);
v___x_3416_ = lean_nat_add(v___x_3414_, v___x_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3396_);
v___x_3418_ = l_String_quote(v___x_3396_);
v___x_3419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
v___x_3420_ = l_Lean_MessageData_ofFormat(v___x_3419_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 7);
lean_ctor_set(v___x_3412_, 1, v___x_3420_);
lean_ctor_set(v___x_3412_, 0, v___x_3417_);
v___x_3422_ = v___x_3412_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3423_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = l_Nat_reprFast(v___x_3416_);
v___x_3426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
v___x_3427_ = l_Lean_MessageData_ofFormat(v___x_3426_);
v___x_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3424_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Nat_reprFast(v_column_3410_);
v___x_3432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
v___x_3433_ = l_Lean_MessageData_ofFormat(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3430_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3378_, v___x_3434_, v___y_3382_, v___y_3383_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_dec_ref_known(v___x_3435_, 1);
goto v___jp_3397_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v___x_3396_);
lean_dec_ref(v___f_3395_);
lean_dec_ref(v_bs_x27_3389_);
lean_dec(v_v_3387_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___x_3373_);
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
v___jp_3397_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; 
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
v___x_3399_ = lean_box(0);
v___x_3400_ = l_Lean_MessageData_ofSyntax(v_v_3387_);
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___f_3395_);
v___x_3403_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3398_);
lean_ctor_set(v___x_3403_, 1, v___x_3399_);
lean_ctor_set(v___x_3403_, 2, v___x_3399_);
lean_ctor_set(v___x_3403_, 3, v___x_3399_);
lean_ctor_set(v___x_3403_, 4, v___x_3401_);
lean_ctor_set(v___x_3403_, 5, v___x_3402_);
v___x_3404_ = ((size_t)1ULL);
v___x_3405_ = lean_usize_add(v_i_3380_, v___x_3404_);
v___x_3406_ = lean_array_uset(v_bs_x27_3389_, v_i_3380_, v___x_3403_);
v_i_3380_ = v___x_3405_;
v_bs_3381_ = v___x_3406_;
goto _start;
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec_ref(v_bs_x27_3389_);
lean_dec(v_v_3387_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___x_3373_);
v_a_3446_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3391_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3391_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3373_ = stack[0].m_obj;
uint8_t v___x_3374_ = stack[1].m_num;
lean_object* v___x_3375_ = stack[2].m_obj;
lean_object* v_insertPos_3376_ = stack[3].m_obj;
lean_object* v_cmdLine_3377_ = stack[4].m_obj;
lean_object* v_ref_3378_ = stack[5].m_obj;
size_t v_sz_3379_ = stack[6].m_num;
size_t v_i_3380_ = stack[7].m_num;
lean_object* v_bs_3381_ = stack[8].m_obj;
lean_object* v___y_3382_ = stack[9].m_obj;
lean_object* v___y_3383_ = stack[10].m_obj;
lean_object* v_res_3454_;
v_res_3454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3373_, v___x_3374_, v___x_3375_, v_insertPos_3376_, v_cmdLine_3377_, v_ref_3378_, v_sz_3379_, v_i_3380_, v_bs_3381_, v___y_3382_, v___y_3383_);
stack->m_obj
 = v_res_3454_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3455_, lean_object* v___x_3456_, lean_object* v___x_3457_, lean_object* v_insertPos_3458_, lean_object* v_cmdLine_3459_, lean_object* v_ref_3460_, lean_object* v_sz_3461_, lean_object* v_i_3462_, lean_object* v_bs_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
uint8_t v___x_4038__boxed_3467_; size_t v_sz_boxed_3468_; size_t v_i_boxed_3469_; lean_object* v_res_3470_; 
v___x_4038__boxed_3467_ = lean_unbox(v___x_3456_);
v_sz_boxed_3468_ = lean_unbox_usize(v_sz_3461_);
lean_dec(v_sz_3461_);
v_i_boxed_3469_ = lean_unbox_usize(v_i_3462_);
lean_dec(v_i_3462_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3455_, v___x_4038__boxed_3467_, v___x_3457_, v_insertPos_3458_, v_cmdLine_3459_, v_ref_3460_, v_sz_boxed_3468_, v_i_boxed_3469_, v_bs_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v_ref_3460_);
lean_dec(v_cmdLine_3459_);
lean_dec(v_insertPos_3458_);
return v_res_3470_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3471_, lean_object* v_ref_3472_, lean_object* v_insertPos_3473_, lean_object* v_suggs_3474_, lean_object* v_cmdLine_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = lean_array_get_size(v_suggs_3474_);
v___x_3480_ = lean_unsigned_to_nat(0u);
v___x_3481_ = lean_nat_dec_eq(v___x_3479_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v_fileMap_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v_scopes_3488_; lean_object* v___x_3489_; lean_object* v_opts_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; size_t v_sz_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v_fileMap_3482_ = lean_ctor_get(v_a_3476_, 1);
v___x_3483_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_inc_ref_n(v_fileMap_3482_, 2);
v___x_3484_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3471_, v_fileMap_3482_);
lean_inc(v_insertPos_3473_);
v___x_3485_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3473_);
v___x_3486_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3487_ = lean_st_ref_get(v_a_3477_);
v_scopes_3488_ = lean_ctor_get(v___x_3487_, 2);
lean_inc(v_scopes_3488_);
lean_dec(v___x_3487_);
v___x_3489_ = l_List_head_x21___redArg(v___x_3486_, v_scopes_3488_);
lean_dec(v_scopes_3488_);
v_opts_3490_ = lean_ctor_get(v___x_3489_, 1);
lean_inc_ref(v_opts_3490_);
lean_dec(v___x_3489_);
v___x_3491_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3492_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3490_, v___x_3491_);
lean_dec_ref(v_opts_3490_);
v_sz_3493_ = lean_array_size(v_suggs_3474_);
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3484_, v___x_3492_, v_fileMap_3482_, v_insertPos_3473_, v_cmdLine_3475_, v_ref_3472_, v_sz_3493_, v___x_3494_, v_suggs_3474_, v_a_3476_, v_a_3477_);
lean_dec(v_insertPos_3473_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___y_3501_; lean_object* v___x_3502_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = lean_array_get_size(v_a_3496_);
v___x_3498_ = lean_unsigned_to_nat(1u);
v___x_3499_ = lean_nat_dec_eq(v___x_3497_, v___x_3498_);
v___x_3500_ = lean_box(v___x_3499_);
v___y_3501_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3501_, 0, v___x_3500_);
lean_closure_set(v___y_3501_, 1, v___x_3485_);
lean_closure_set(v___y_3501_, 2, v_ref_3472_);
lean_closure_set(v___y_3501_, 3, v_a_3496_);
lean_closure_set(v___y_3501_, 4, v___x_3483_);
lean_closure_set(v___y_3501_, 5, v___x_3480_);
v___x_3502_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3501_, v_a_3476_, v_a_3477_);
return v___x_3502_;
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v___x_3485_);
lean_dec(v_ref_3472_);
v_a_3503_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3495_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3495_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec_ref(v_suggs_3474_);
lean_dec(v_insertPos_3473_);
lean_dec(v_ref_3472_);
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
return v___x_3512_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticSeq_3471_ = stack[0].m_obj;
lean_object* v_ref_3472_ = stack[1].m_obj;
lean_object* v_insertPos_3473_ = stack[2].m_obj;
lean_object* v_suggs_3474_ = stack[3].m_obj;
lean_object* v_cmdLine_3475_ = stack[4].m_obj;
lean_object* v_a_3476_ = stack[5].m_obj;
lean_object* v_a_3477_ = stack[6].m_obj;
lean_object* v_res_3513_;
v_res_3513_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3471_, v_ref_3472_, v_insertPos_3473_, v_suggs_3474_, v_cmdLine_3475_, v_a_3476_, v_a_3477_);
stack->m_obj
 = v_res_3513_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3514_, lean_object* v_ref_3515_, lean_object* v_insertPos_3516_, lean_object* v_suggs_3517_, lean_object* v_cmdLine_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3514_, v_ref_3515_, v_insertPos_3516_, v_suggs_3517_, v_cmdLine_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_cmdLine_3518_);
lean_dec(v_tacticSeq_3514_);
return v_res_3522_;
}
}
uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3523_){
_start:
{
uint8_t v___x_3524_; 
v___x_3524_ = 0;
return v___x_3524_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3523_ = stack[0].m_obj;
uint8_t v_res_3525_;
v_res_3525_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3523_);
stack->m_num = v_res_3525_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3526_){
_start:
{
uint8_t v_res_3527_; lean_object* v_r_3528_; 
v_res_3527_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3526_);
lean_dec(v_x_3526_);
v_r_3528_ = lean_box(v_res_3527_);
return v_r_3528_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Array_mkArray0___redArg();
return v___x_3539_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3549_, lean_object* v_ref_3550_, lean_object* v_goal_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_toCold_3560_; lean_object* v_currRecDepth_3561_; lean_object* v_ref_3562_; uint16_t v_optionFlags_3563_; uint8_t v_suppressElabErrors_3564_; uint8_t v_isRecordingDeps_3565_; uint8_t v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v_ref_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_toCold_3560_ = lean_ctor_get(v___y_3554_, 0);
v_currRecDepth_3561_ = lean_ctor_get(v___y_3554_, 1);
v_ref_3562_ = lean_ctor_get(v___y_3554_, 2);
v_optionFlags_3563_ = lean_ctor_get_uint16(v___y_3554_, sizeof(void*)*3);
v_suppressElabErrors_3564_ = lean_ctor_get_uint8(v___y_3554_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3565_ = lean_ctor_get_uint8(v___y_3554_, sizeof(void*)*3 + 3);
v___x_3566_ = 0;
v___x_3567_ = l_Lean_SourceInfo_fromRef(v_ref_3562_, v___x_3566_);
v___x_3568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0));
lean_inc_n(v___x_3567_, 3);
v___x_3569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3572_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5);
v___x_3573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3567_);
lean_ctor_set(v___x_3573_, 1, v___x_3571_);
lean_ctor_set(v___x_3573_, 2, v___x_3572_);
v___x_3574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7));
v___x_3575_ = l_Lean_Syntax_node1(v___x_3567_, v___x_3574_, v___x_3573_);
v___x_3576_ = l_Lean_Syntax_node2(v___x_3567_, v___x_3570_, v___x_3569_, v___x_3575_);
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_box(0);
v___x_3579_ = 1;
v___x_3580_ = lean_box(1);
v___x_3581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3582_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3582_, 0, v___x_3577_);
lean_ctor_set(v___x_3582_, 1, v___x_3578_);
lean_ctor_set(v___x_3582_, 2, v___x_3577_);
lean_ctor_set(v___x_3582_, 3, v___f_3549_);
lean_ctor_set(v___x_3582_, 4, v___x_3580_);
lean_ctor_set(v___x_3582_, 5, v___x_3580_);
lean_ctor_set(v___x_3582_, 6, v___x_3577_);
lean_ctor_set(v___x_3582_, 7, v___x_3581_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8, v___x_3579_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 1, v___x_3579_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 2, v___x_3579_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 3, v___x_3579_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 4, v___x_3566_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 5, v___x_3566_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 6, v___x_3566_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 7, v___x_3566_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 8, v___x_3579_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 9, v___x_3566_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*8 + 10, v___x_3579_);
v___x_3583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v___x_3584_ = lean_box(0);
v_ref_3585_ = l_Lean_replaceRef(v_ref_3550_, v_ref_3562_);
lean_inc(v_currRecDepth_3561_);
lean_inc_ref(v_toCold_3560_);
v___x_3586_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3586_, 0, v_toCold_3560_);
lean_ctor_set(v___x_3586_, 1, v_currRecDepth_3561_);
lean_ctor_set(v___x_3586_, 2, v_ref_3585_);
lean_ctor_set_uint16(v___x_3586_, sizeof(void*)*3, v_optionFlags_3563_);
lean_ctor_set_uint8(v___x_3586_, sizeof(void*)*3 + 2, v_suppressElabErrors_3564_);
lean_ctor_set_uint8(v___x_3586_, sizeof(void*)*3 + 3, v_isRecordingDeps_3565_);
v___x_3587_ = l_Lean_Elab_runTactic(v_goal_3551_, v___x_3576_, v___x_3582_, v___x_3583_, v___y_3552_, v___y_3553_, v___x_3586_, v___y_3555_);
lean_dec_ref_known(v___x_3586_, 3);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v___x_3587_, 0);
lean_dec(v_unused_3595_);
v___x_3589_ = v___x_3587_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_dec(v___x_3587_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3584_);
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3584_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3621_; 
v_a_3596_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3598_ = v___x_3587_;
v_isShared_3599_ = v_isSharedCheck_3621_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3587_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3621_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
lean_inc(v_a_3596_);
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
uint8_t v___y_3603_; uint8_t v___y_3615_; uint8_t v___x_3618_; 
v___x_3618_ = l_Lean_Exception_isInterrupt(v_a_3596_);
if (v___x_3618_ == 0)
{
uint8_t v___x_3619_; 
lean_inc(v_a_3596_);
v___x_3619_ = l_Lean_Exception_isRuntime(v_a_3596_);
v___y_3615_ = v___x_3619_;
goto v___jp_3614_;
}
else
{
v___y_3615_ = v___x_3618_;
goto v___jp_3614_;
}
v___jp_3602_:
{
if (v___y_3603_ == 0)
{
lean_object* v_options_3604_; uint8_t v_hasTrace_3605_; 
lean_dec_ref(v___x_3601_);
v_options_3604_ = lean_ctor_get(v_toCold_3560_, 2);
v_hasTrace_3605_ = lean_ctor_get_uint8(v_options_3604_, sizeof(void*)*1);
if (v_hasTrace_3605_ == 0)
{
lean_dec(v_a_3596_);
goto v___jp_3557_;
}
else
{
lean_object* v_inheritedTraceOptions_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; 
v_inheritedTraceOptions_3606_ = lean_ctor_get(v_toCold_3560_, 11);
v___x_3607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3608_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3609_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3606_, v_options_3604_, v___x_3608_);
if (v___x_3609_ == 0)
{
lean_dec(v_a_3596_);
goto v___jp_3557_;
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3610_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3611_ = l_Lean_Exception_toMessageData(v_a_3596_);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3607_, v___x_3612_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
return v___x_3613_;
}
}
}
else
{
lean_dec(v_a_3596_);
return v___x_3601_;
}
}
v___jp_3614_:
{
if (v___y_3615_ == 0)
{
uint8_t v___x_3616_; 
v___x_3616_ = l_Lean_Exception_isInterrupt(v_a_3596_);
if (v___x_3616_ == 0)
{
uint8_t v___x_3617_; 
lean_inc(v_a_3596_);
v___x_3617_ = l_Lean_Exception_isMaxRecDepth(v_a_3596_);
v___y_3603_ = v___x_3617_;
goto v___jp_3602_;
}
else
{
v___y_3603_ = v___x_3616_;
goto v___jp_3602_;
}
}
else
{
lean_dec(v_a_3596_);
return v___x_3601_;
}
}
}
}
}
v___jp_3557_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_box(0);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
return v___x_3559_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3549_ = stack[0].m_obj;
lean_object* v_ref_3550_ = stack[1].m_obj;
lean_object* v_goal_3551_ = stack[2].m_obj;
lean_object* v___y_3552_ = stack[3].m_obj;
lean_object* v___y_3553_ = stack[4].m_obj;
lean_object* v___y_3554_ = stack[5].m_obj;
lean_object* v___y_3555_ = stack[6].m_obj;
lean_object* v_res_3622_;
v_res_3622_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3549_, v_ref_3550_, v_goal_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
stack->m_obj
 = v_res_3622_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3623_, lean_object* v_ref_3624_, lean_object* v_goal_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3623_, v_ref_3624_, v_goal_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v_ref_3624_);
return v_res_3631_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_mctx_3637_; lean_object* v_ref_3638_; lean_object* v_env_3639_; lean_object* v_opts_3640_; lean_object* v_namingCtx_3641_; lean_object* v_goal_3642_; lean_object* v_decls_3643_; lean_object* v___x_3644_; 
v_mctx_3637_ = lean_ctor_get(v_c_3633_, 3);
lean_inc_ref(v_mctx_3637_);
v_ref_3638_ = lean_ctor_get(v_c_3633_, 1);
lean_inc(v_ref_3638_);
v_env_3639_ = lean_ctor_get(v_c_3633_, 2);
lean_inc_ref(v_env_3639_);
v_opts_3640_ = lean_ctor_get(v_c_3633_, 4);
lean_inc_ref(v_opts_3640_);
v_namingCtx_3641_ = lean_ctor_get(v_c_3633_, 5);
lean_inc_ref(v_namingCtx_3641_);
v_goal_3642_ = lean_ctor_get(v_c_3633_, 6);
lean_inc(v_goal_3642_);
lean_dec_ref(v_c_3633_);
v_decls_3643_ = lean_ctor_get(v_mctx_3637_, 5);
v___x_3644_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3643_, v_goal_3642_);
if (lean_obj_tag(v___x_3644_) == 1)
{
lean_object* v_val_3645_; lean_object* v_lctx_3646_; lean_object* v___f_3647_; lean_object* v___f_3648_; lean_object* v___x_3649_; 
v_val_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_val_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v_lctx_3646_ = lean_ctor_get(v_val_3645_, 1);
lean_inc_ref(v_lctx_3646_);
lean_dec(v_val_3645_);
v___f_3647_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3648_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3648_, 0, v___f_3647_);
lean_closure_set(v___f_3648_, 1, v_ref_3638_);
lean_closure_set(v___f_3648_, 2, v_goal_3642_);
v___x_3649_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3639_, v_mctx_3637_, v_lctx_3646_, v_opts_3640_, v_namingCtx_3641_, v___f_3648_, v_a_3634_, v_a_3635_);
return v___x_3649_;
}
else
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec(v___x_3644_);
lean_dec(v_goal_3642_);
lean_dec_ref(v_namingCtx_3641_);
lean_dec_ref(v_opts_3640_);
lean_dec_ref(v_env_3639_);
lean_dec(v_ref_3638_);
lean_dec_ref(v_mctx_3637_);
v___x_3650_ = lean_box(0);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
return v___x_3651_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3633_ = stack[0].m_obj;
lean_object* v_a_3634_ = stack[1].m_obj;
lean_object* v_a_3635_ = stack[2].m_obj;
lean_object* v_res_3652_;
v_res_3652_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3633_, v_a_3634_, v_a_3635_);
stack->m_obj
 = v_res_3652_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3653_, v_a_3654_, v_a_3655_);
lean_dec(v_a_3655_);
lean_dec_ref(v_a_3654_);
return v_res_3657_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3658_, lean_object* v_val_3659_, lean_object* v_as_3660_, size_t v_i_3661_, size_t v_stop_3662_){
_start:
{
uint8_t v___x_3667_; 
v___x_3667_ = lean_usize_dec_eq(v_i_3661_, v_stop_3662_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; lean_object* v_pos_3669_; uint8_t v_severity_3670_; lean_object* v_data_3671_; lean_object* v___f_3672_; uint8_t v___x_3673_; uint8_t v___y_3675_; uint8_t v___y_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; uint8_t v___y_3680_; 
v___x_3668_ = lean_array_uget_borrowed(v_as_3660_, v_i_3661_);
v_pos_3669_ = lean_ctor_get(v___x_3668_, 1);
v_severity_3670_ = lean_ctor_get_uint8(v___x_3668_, sizeof(void*)*5 + 1);
v_data_3671_ = lean_ctor_get(v___x_3668_, 4);
v___f_3672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
v___x_3673_ = 1;
lean_inc_ref(v_pos_3669_);
v___x_3677_ = l_Lean_FileMap_ofPosition(v___x_3658_, v_pos_3669_);
v___x_3678_ = l_Lean_Syntax_Range_contains(v_val_3659_, v___x_3677_, v___x_3673_);
lean_dec(v___x_3677_);
if (v_severity_3670_ == 2)
{
v___y_3680_ = v___x_3673_;
goto v___jp_3679_;
}
else
{
v___y_3680_ = v___x_3667_;
goto v___jp_3679_;
}
v___jp_3674_:
{
if (v___y_3676_ == 0)
{
goto v___jp_3663_;
}
else
{
if (v___y_3675_ == 0)
{
return v___x_3673_;
}
else
{
goto v___jp_3663_;
}
}
}
v___jp_3679_:
{
uint8_t v___x_3681_; 
lean_inc(v_data_3671_);
v___x_3681_ = l_Lean_MessageData_hasTag(v___f_3672_, v_data_3671_);
if (v___x_3678_ == 0)
{
v___y_3675_ = v___x_3681_;
v___y_3676_ = v___x_3678_;
goto v___jp_3674_;
}
else
{
v___y_3675_ = v___x_3681_;
v___y_3676_ = v___y_3680_;
goto v___jp_3674_;
}
}
}
else
{
uint8_t v___x_3682_; 
v___x_3682_ = 0;
return v___x_3682_;
}
v___jp_3663_:
{
size_t v___x_3664_; size_t v___x_3665_; 
v___x_3664_ = ((size_t)1ULL);
v___x_3665_ = lean_usize_add(v_i_3661_, v___x_3664_);
v_i_3661_ = v___x_3665_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3658_ = stack[0].m_obj;
lean_object* v_val_3659_ = stack[1].m_obj;
lean_object* v_as_3660_ = stack[2].m_obj;
size_t v_i_3661_ = stack[3].m_num;
size_t v_stop_3662_ = stack[4].m_num;
uint8_t v_res_3683_;
v_res_3683_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3658_, v_val_3659_, v_as_3660_, v_i_3661_, v_stop_3662_);
stack->m_num = v_res_3683_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3684_, lean_object* v_val_3685_, lean_object* v_as_3686_, lean_object* v_i_3687_, lean_object* v_stop_3688_){
_start:
{
size_t v_i_boxed_3689_; size_t v_stop_boxed_3690_; uint8_t v_res_3691_; lean_object* v_r_3692_; 
v_i_boxed_3689_ = lean_unbox_usize(v_i_3687_);
lean_dec(v_i_3687_);
v_stop_boxed_3690_ = lean_unbox_usize(v_stop_3688_);
lean_dec(v_stop_3688_);
v_res_3691_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3684_, v_val_3685_, v_as_3686_, v_i_boxed_3689_, v_stop_boxed_3690_);
lean_dec_ref(v_as_3686_);
lean_dec_ref(v_val_3685_);
lean_dec_ref(v___x_3684_);
v_r_3692_ = lean_box(v_res_3691_);
return v_r_3692_;
}
}
uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3693_, lean_object* v_val_3694_, lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3695_) == 0)
{
lean_object* v_cs_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v_cs_3696_ = lean_ctor_get(v_x_3695_, 0);
v___x_3697_ = lean_unsigned_to_nat(0u);
v___x_3698_ = lean_array_get_size(v_cs_3696_);
v___x_3699_ = lean_nat_dec_lt(v___x_3697_, v___x_3698_);
if (v___x_3699_ == 0)
{
return v___x_3699_;
}
else
{
if (v___x_3699_ == 0)
{
return v___x_3699_;
}
else
{
size_t v___x_3700_; size_t v___x_3701_; uint8_t v___x_3702_; 
v___x_3700_ = ((size_t)0ULL);
v___x_3701_ = lean_usize_of_nat(v___x_3698_);
v___x_3702_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3693_, v_val_3694_, v_cs_3696_, v___x_3700_, v___x_3701_);
return v___x_3702_;
}
}
}
else
{
lean_object* v_vs_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v_vs_3703_ = lean_ctor_get(v_x_3695_, 0);
v___x_3704_ = lean_unsigned_to_nat(0u);
v___x_3705_ = lean_array_get_size(v_vs_3703_);
v___x_3706_ = lean_nat_dec_lt(v___x_3704_, v___x_3705_);
if (v___x_3706_ == 0)
{
return v___x_3706_;
}
else
{
if (v___x_3706_ == 0)
{
return v___x_3706_;
}
else
{
size_t v___x_3707_; size_t v___x_3708_; uint8_t v___x_3709_; 
v___x_3707_ = ((size_t)0ULL);
v___x_3708_ = lean_usize_of_nat(v___x_3705_);
v___x_3709_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3693_, v_val_3694_, v_vs_3703_, v___x_3707_, v___x_3708_);
return v___x_3709_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3693_ = stack[0].m_obj;
lean_object* v_val_3694_ = stack[1].m_obj;
lean_object* v_x_3695_ = stack[2].m_obj;
uint8_t v_res_3710_;
v_res_3710_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3693_, v_val_3694_, v_x_3695_);
stack->m_num = v_res_3710_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3711_, lean_object* v_val_3712_, lean_object* v_as_3713_, size_t v_i_3714_, size_t v_stop_3715_){
_start:
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_usize_dec_eq(v_i_3714_, v_stop_3715_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; uint8_t v___x_3718_; 
v___x_3717_ = lean_array_uget_borrowed(v_as_3713_, v_i_3714_);
v___x_3718_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3711_, v_val_3712_, v___x_3717_);
if (v___x_3718_ == 0)
{
size_t v___x_3719_; size_t v___x_3720_; 
v___x_3719_ = ((size_t)1ULL);
v___x_3720_ = lean_usize_add(v_i_3714_, v___x_3719_);
v_i_3714_ = v___x_3720_;
goto _start;
}
else
{
return v___x_3718_;
}
}
else
{
uint8_t v___x_3722_; 
v___x_3722_ = 0;
return v___x_3722_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3711_ = stack[0].m_obj;
lean_object* v_val_3712_ = stack[1].m_obj;
lean_object* v_as_3713_ = stack[2].m_obj;
size_t v_i_3714_ = stack[3].m_num;
size_t v_stop_3715_ = stack[4].m_num;
uint8_t v_res_3723_;
v_res_3723_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3711_, v_val_3712_, v_as_3713_, v_i_3714_, v_stop_3715_);
stack->m_num = v_res_3723_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3724_, lean_object* v_val_3725_, lean_object* v_as_3726_, lean_object* v_i_3727_, lean_object* v_stop_3728_){
_start:
{
size_t v_i_boxed_3729_; size_t v_stop_boxed_3730_; uint8_t v_res_3731_; lean_object* v_r_3732_; 
v_i_boxed_3729_ = lean_unbox_usize(v_i_3727_);
lean_dec(v_i_3727_);
v_stop_boxed_3730_ = lean_unbox_usize(v_stop_3728_);
lean_dec(v_stop_3728_);
v_res_3731_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3724_, v_val_3725_, v_as_3726_, v_i_boxed_3729_, v_stop_boxed_3730_);
lean_dec_ref(v_as_3726_);
lean_dec_ref(v_val_3725_);
lean_dec_ref(v___x_3724_);
v_r_3732_ = lean_box(v_res_3731_);
return v_r_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3733_, lean_object* v_val_3734_, lean_object* v_x_3735_){
_start:
{
uint8_t v_res_3736_; lean_object* v_r_3737_; 
v_res_3736_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3733_, v_val_3734_, v_x_3735_);
lean_dec_ref(v_x_3735_);
lean_dec_ref(v_val_3734_);
lean_dec_ref(v___x_3733_);
v_r_3737_ = lean_box(v_res_3736_);
return v_r_3737_;
}
}
uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3738_, lean_object* v_val_3739_, lean_object* v_t_3740_){
_start:
{
lean_object* v_root_3741_; lean_object* v_tail_3742_; uint8_t v___x_3743_; 
v_root_3741_ = lean_ctor_get(v_t_3740_, 0);
v_tail_3742_ = lean_ctor_get(v_t_3740_, 1);
v___x_3743_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3738_, v_val_3739_, v_root_3741_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v___x_3744_ = lean_unsigned_to_nat(0u);
v___x_3745_ = lean_array_get_size(v_tail_3742_);
v___x_3746_ = lean_nat_dec_lt(v___x_3744_, v___x_3745_);
if (v___x_3746_ == 0)
{
return v___x_3746_;
}
else
{
if (v___x_3746_ == 0)
{
return v___x_3746_;
}
else
{
size_t v___x_3747_; size_t v___x_3748_; uint8_t v___x_3749_; 
v___x_3747_ = ((size_t)0ULL);
v___x_3748_ = lean_usize_of_nat(v___x_3745_);
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3738_, v_val_3739_, v_tail_3742_, v___x_3747_, v___x_3748_);
return v___x_3749_;
}
}
}
else
{
return v___x_3743_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3738_ = stack[0].m_obj;
lean_object* v_val_3739_ = stack[1].m_obj;
lean_object* v_t_3740_ = stack[2].m_obj;
uint8_t v_res_3750_;
v_res_3750_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3738_, v_val_3739_, v_t_3740_);
stack->m_num = v_res_3750_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3751_, lean_object* v_val_3752_, lean_object* v_t_3753_){
_start:
{
uint8_t v_res_3754_; lean_object* v_r_3755_; 
v_res_3754_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3751_, v_val_3752_, v_t_3753_);
lean_dec_ref(v_t_3753_);
lean_dec_ref(v_val_3752_);
lean_dec_ref(v___x_3751_);
v_r_3755_ = lean_box(v_res_3754_);
return v_r_3755_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_){
_start:
{
uint8_t v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = 0;
v___x_3761_ = l_Lean_Syntax_getRange_x3f(v_stx_3756_, v___x_3760_);
if (lean_obj_tag(v___x_3761_) == 1)
{
lean_object* v_val_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3775_; 
v_val_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3775_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_val_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3775_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v_fileMap_3766_; lean_object* v___x_3767_; lean_object* v_messages_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
v_fileMap_3766_ = lean_ctor_get(v_a_3757_, 1);
v___x_3767_ = lean_st_ref_get(v_a_3758_);
v_messages_3768_ = lean_ctor_get(v___x_3767_, 1);
lean_inc_ref(v_messages_3768_);
lean_dec(v___x_3767_);
v___x_3769_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3768_);
v___x_3770_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3766_, v_val_3762_, v___x_3769_);
lean_dec_ref(v___x_3769_);
lean_dec(v_val_3762_);
v___x_3771_ = lean_box(v___x_3770_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set_tag(v___x_3764_, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3771_);
v___x_3773_ = v___x_3764_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_dec(v___x_3761_);
v___x_3776_ = lean_box(v___x_3760_);
v___x_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
return v___x_3777_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3756_ = stack[0].m_obj;
lean_object* v_a_3757_ = stack[1].m_obj;
lean_object* v_a_3758_ = stack[2].m_obj;
lean_object* v_res_3778_;
v_res_3778_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3756_, v_a_3757_, v_a_3758_);
stack->m_obj
 = v_res_3778_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3779_, v_a_3780_, v_a_3781_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_stx_3779_);
return v_res_3783_;
}
}
uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3784_, lean_object* v_fileMap_3785_, lean_object* v_c_3786_){
_start:
{
lean_object* v___y_3788_; lean_object* v_kind_3792_; lean_object* v_ref_3793_; lean_object* v___y_3795_; 
v_kind_3792_ = lean_ctor_get(v_c_3786_, 0);
lean_inc(v_kind_3792_);
v_ref_3793_ = lean_ctor_get(v_c_3786_, 1);
lean_inc(v_ref_3793_);
lean_dec_ref(v_c_3786_);
if (lean_obj_tag(v_kind_3792_) == 0)
{
lean_object* v_insertPos_3811_; 
lean_dec(v_ref_3793_);
v_insertPos_3811_ = lean_ctor_get(v_kind_3792_, 1);
lean_inc(v_insertPos_3811_);
v___y_3795_ = v_insertPos_3811_;
goto v___jp_3794_;
}
else
{
uint8_t v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = 0;
v___x_3813_ = l_Lean_Syntax_getPos_x3f(v_ref_3793_, v___x_3812_);
lean_dec(v_ref_3793_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v___x_3814_; 
v___x_3814_ = lean_unsigned_to_nat(0u);
v___y_3795_ = v___x_3814_;
goto v___jp_3794_;
}
else
{
lean_object* v_val_3815_; 
v_val_3815_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_val_3815_);
lean_dec_ref_known(v___x_3813_, 1);
v___y_3795_ = v_val_3815_;
goto v___jp_3794_;
}
}
v___jp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; uint8_t v___x_3791_; 
v___x_3789_ = l_List_lengthTR___redArg(v___y_3788_);
lean_dec(v___y_3788_);
v___x_3790_ = lean_unsigned_to_nat(1u);
v___x_3791_ = lean_nat_dec_eq(v___x_3789_, v___x_3790_);
lean_dec(v___x_3789_);
return v___x_3791_;
}
v___jp_3794_:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3785_, v_tree_3784_, v___y_3795_);
if (lean_obj_tag(v___x_3796_) == 1)
{
lean_object* v_tail_3797_; 
v_tail_3797_ = lean_ctor_get(v___x_3796_, 1);
if (lean_obj_tag(v_tail_3797_) == 0)
{
if (lean_obj_tag(v_kind_3792_) == 0)
{
lean_object* v_head_3798_; lean_object* v_tacticSeq_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; 
v_head_3798_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_head_3798_);
lean_dec_ref_known(v___x_3796_, 2);
v_tacticSeq_3799_ = lean_ctor_get(v_kind_3792_, 0);
lean_inc(v_tacticSeq_3799_);
lean_dec_ref_known(v_kind_3792_, 2);
v___x_3800_ = 0;
v___x_3801_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3799_, v___x_3800_);
lean_dec(v_tacticSeq_3799_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_tacticInfo_3802_; lean_object* v_goalsBefore_3803_; 
v_tacticInfo_3802_ = lean_ctor_get(v_head_3798_, 1);
lean_inc_ref(v_tacticInfo_3802_);
lean_dec(v_head_3798_);
v_goalsBefore_3803_ = lean_ctor_get(v_tacticInfo_3802_, 2);
lean_inc(v_goalsBefore_3803_);
lean_dec_ref(v_tacticInfo_3802_);
v___y_3788_ = v_goalsBefore_3803_;
goto v___jp_3787_;
}
else
{
lean_object* v_tacticInfo_3804_; lean_object* v_goalsAfter_3805_; 
lean_dec_ref_known(v___x_3801_, 1);
v_tacticInfo_3804_ = lean_ctor_get(v_head_3798_, 1);
lean_inc_ref(v_tacticInfo_3804_);
lean_dec(v_head_3798_);
v_goalsAfter_3805_ = lean_ctor_get(v_tacticInfo_3804_, 4);
lean_inc(v_goalsAfter_3805_);
lean_dec_ref(v_tacticInfo_3804_);
v___y_3788_ = v_goalsAfter_3805_;
goto v___jp_3787_;
}
}
else
{
lean_object* v_head_3806_; lean_object* v_tacticInfo_3807_; lean_object* v_goalsBefore_3808_; 
v_head_3806_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_head_3806_);
lean_dec_ref_known(v___x_3796_, 2);
v_tacticInfo_3807_ = lean_ctor_get(v_head_3806_, 1);
lean_inc_ref(v_tacticInfo_3807_);
lean_dec(v_head_3806_);
v_goalsBefore_3808_ = lean_ctor_get(v_tacticInfo_3807_, 2);
lean_inc(v_goalsBefore_3808_);
lean_dec_ref(v_tacticInfo_3807_);
v___y_3788_ = v_goalsBefore_3808_;
goto v___jp_3787_;
}
}
else
{
uint8_t v___x_3809_; 
lean_dec_ref_known(v___x_3796_, 2);
lean_dec(v_kind_3792_);
v___x_3809_ = 0;
return v___x_3809_;
}
}
else
{
uint8_t v___x_3810_; 
lean_dec(v___x_3796_);
lean_dec(v_kind_3792_);
v___x_3810_ = 0;
return v___x_3810_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_tree_3784_ = stack[0].m_obj;
lean_object* v_fileMap_3785_ = stack[1].m_obj;
lean_object* v_c_3786_ = stack[2].m_obj;
uint8_t v_res_3816_;
v_res_3816_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3784_, v_fileMap_3785_, v_c_3786_);
stack->m_num = v_res_3816_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3817_, lean_object* v_fileMap_3818_, lean_object* v_c_3819_){
_start:
{
uint8_t v_res_3820_; lean_object* v_r_3821_; 
v_res_3820_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3817_, v_fileMap_3818_, v_c_3819_);
v_r_3821_ = lean_box(v_res_3820_);
return v_r_3821_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3822_){
_start:
{
lean_object* v___x_3824_; lean_object* v_infoState_3825_; lean_object* v_trees_3826_; lean_object* v___x_3827_; 
v___x_3824_ = lean_st_ref_get(v___y_3822_);
v_infoState_3825_ = lean_ctor_get(v___x_3824_, 8);
lean_inc_ref(v_infoState_3825_);
lean_dec(v___x_3824_);
v_trees_3826_ = lean_ctor_get(v_infoState_3825_, 2);
lean_inc_ref(v_trees_3826_);
lean_dec_ref(v_infoState_3825_);
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v_trees_3826_);
return v___x_3827_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3822_ = stack[0].m_obj;
lean_object* v_res_3828_;
v_res_3828_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3822_);
stack->m_obj
 = v_res_3828_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3829_);
lean_dec(v___y_3829_);
return v_res_3831_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3833_);
return v___x_3835_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3832_ = stack[0].m_obj;
lean_object* v___y_3833_ = stack[1].m_obj;
lean_object* v_res_3836_;
v_res_3836_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3832_, v___y_3833_);
stack->m_obj
 = v_res_3836_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
return v_res_3840_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3843_ = l_Lean_stringToMessageData(v___x_3842_);
return v___x_3843_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3844_, lean_object* v___x_3845_, lean_object* v___x_3846_, lean_object* v_as_3847_, size_t v_sz_3848_, size_t v_i_3849_, lean_object* v_b_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v_a_3855_; uint8_t v___x_3859_; 
v___x_3859_ = lean_usize_dec_lt(v_i_3849_, v_sz_3848_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_tree_3844_);
v___x_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3860_, 0, v_b_3850_);
return v___x_3860_;
}
else
{
lean_object* v___x_3861_; lean_object* v_a_3862_; uint8_t v___x_3863_; 
v___x_3861_ = lean_box(0);
v_a_3862_ = lean_array_uget_borrowed(v_as_3847_, v_i_3849_);
lean_inc(v_a_3862_);
lean_inc_ref(v___x_3845_);
lean_inc_ref(v_tree_3844_);
v___x_3863_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3844_, v___x_3845_, v_a_3862_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v_scopes_3869_; lean_object* v___x_3870_; lean_object* v_opts_3871_; uint8_t v_hasTrace_3872_; 
v___x_3864_ = l_Lean_inheritedTraceOptions;
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3866_ = lean_st_ref_get(v___x_3864_);
v___x_3867_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3868_ = lean_st_ref_get(v___y_3852_);
v_scopes_3869_ = lean_ctor_get(v___x_3868_, 2);
lean_inc(v_scopes_3869_);
lean_dec(v___x_3868_);
v___x_3870_ = l_List_head_x21___redArg(v___x_3867_, v_scopes_3869_);
lean_dec(v_scopes_3869_);
v_opts_3871_ = lean_ctor_get(v___x_3870_, 1);
lean_inc_ref(v_opts_3871_);
lean_dec(v___x_3870_);
v_hasTrace_3872_ = lean_ctor_get_uint8(v_opts_3871_, sizeof(void*)*1);
if (v_hasTrace_3872_ == 0)
{
lean_dec_ref(v_opts_3871_);
lean_dec(v___x_3866_);
v_a_3855_ = v___x_3861_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3873_; uint8_t v___x_3874_; 
v___x_3873_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3874_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3866_, v_opts_3871_, v___x_3873_);
lean_dec_ref(v_opts_3871_);
lean_dec(v___x_3866_);
if (v___x_3874_ == 0)
{
v_a_3855_ = v___x_3861_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3876_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3865_, v___x_3875_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_dec_ref_known(v___x_3876_, 1);
v_a_3855_ = v___x_3861_;
goto v___jp_3854_;
}
else
{
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_tree_3844_);
return v___x_3876_;
}
}
}
}
else
{
lean_object* v_kind_3877_; 
v_kind_3877_ = lean_ctor_get(v_a_3862_, 0);
if (lean_obj_tag(v_kind_3877_) == 0)
{
lean_object* v_ref_3878_; lean_object* v_tacticSeq_3879_; lean_object* v_insertPos_3880_; lean_object* v___x_3881_; 
v_ref_3878_ = lean_ctor_get(v_a_3862_, 1);
v_tacticSeq_3879_ = lean_ctor_get(v_kind_3877_, 0);
v_insertPos_3880_ = lean_ctor_get(v_kind_3877_, 1);
lean_inc(v_a_3862_);
v___x_3881_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3862_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3883_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
lean_inc(v_insertPos_3880_);
lean_inc(v_ref_3878_);
v___x_3883_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3879_, v_ref_3878_, v_insertPos_3880_, v_a_3882_, v___x_3846_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_dec_ref_known(v___x_3883_, 1);
v_a_3855_ = v___x_3861_;
goto v___jp_3854_;
}
else
{
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_tree_3844_);
return v___x_3883_;
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_tree_3844_);
v_a_3884_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3881_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3881_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
else
{
lean_object* v___x_3892_; 
lean_inc(v_a_3862_);
v___x_3892_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3862_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_dec_ref_known(v___x_3892_, 1);
v_a_3855_ = v___x_3861_;
goto v___jp_3854_;
}
else
{
lean_dec_ref(v___x_3845_);
lean_dec_ref(v_tree_3844_);
return v___x_3892_;
}
}
}
}
v___jp_3854_:
{
size_t v___x_3856_; size_t v___x_3857_; 
v___x_3856_ = ((size_t)1ULL);
v___x_3857_ = lean_usize_add(v_i_3849_, v___x_3856_);
v_i_3849_ = v___x_3857_;
v_b_3850_ = v_a_3855_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_tree_3844_ = stack[0].m_obj;
lean_object* v___x_3845_ = stack[1].m_obj;
lean_object* v___x_3846_ = stack[2].m_obj;
lean_object* v_as_3847_ = stack[3].m_obj;
size_t v_sz_3848_ = stack[4].m_num;
size_t v_i_3849_ = stack[5].m_num;
lean_object* v_b_3850_ = stack[6].m_obj;
lean_object* v___y_3851_ = stack[7].m_obj;
lean_object* v___y_3852_ = stack[8].m_obj;
lean_object* v_res_3893_;
v_res_3893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3844_, v___x_3845_, v___x_3846_, v_as_3847_, v_sz_3848_, v_i_3849_, v_b_3850_, v___y_3851_, v___y_3852_);
stack->m_obj
 = v_res_3893_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v_as_3897_, lean_object* v_sz_3898_, lean_object* v_i_3899_, lean_object* v_b_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
size_t v_sz_boxed_3904_; size_t v_i_boxed_3905_; lean_object* v_res_3906_; 
v_sz_boxed_3904_ = lean_unbox_usize(v_sz_3898_);
lean_dec(v_sz_3898_);
v_i_boxed_3905_ = lean_unbox_usize(v_i_3899_);
lean_dec(v_i_3899_);
v_res_3906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3894_, v___x_3895_, v___x_3896_, v_as_3897_, v_sz_boxed_3904_, v_i_boxed_3905_, v_b_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec_ref(v_as_3897_);
lean_dec(v___x_3896_);
return v_res_3906_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3912_ = l_Lean_stringToMessageData(v___x_3911_);
return v___x_3912_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3913_, lean_object* v___x_3914_, lean_object* v___x_3915_, lean_object* v___x_3916_, lean_object* v___x_3917_, lean_object* v_as_3918_, size_t v_sz_3919_, size_t v_i_3920_, lean_object* v_b_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
uint8_t v___x_3925_; 
v___x_3925_ = lean_usize_dec_lt(v_i_3920_, v_sz_3919_);
if (v___x_3925_ == 0)
{
lean_object* v___x_3926_; 
lean_dec_ref(v___x_3916_);
lean_dec(v_stx_3913_);
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v_b_3921_);
return v___x_3926_;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v_a_3930_; lean_object* v___x_3931_; 
lean_dec_ref(v_b_3921_);
v___x_3927_ = lean_box(0);
v___x_3928_ = l_Lean_inheritedTraceOptions;
v___x_3929_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3930_ = lean_array_uget_borrowed(v_as_3918_, v_i_3920_);
lean_inc(v_a_3930_);
lean_inc(v_stx_3913_);
v___x_3931_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3913_, v___x_3914_, v_a_3930_, v___x_3915_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v_scopes_3954_; lean_object* v___x_3955_; lean_object* v_opts_3956_; uint8_t v_hasTrace_3957_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3951_ = lean_st_ref_get(v___x_3928_);
v___x_3952_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3953_ = lean_st_ref_get(v___y_3923_);
v_scopes_3954_ = lean_ctor_get(v___x_3953_, 2);
lean_inc(v_scopes_3954_);
lean_dec(v___x_3953_);
v___x_3955_ = l_List_head_x21___redArg(v___x_3952_, v_scopes_3954_);
lean_dec(v_scopes_3954_);
v_opts_3956_ = lean_ctor_get(v___x_3955_, 1);
lean_inc_ref(v_opts_3956_);
lean_dec(v___x_3955_);
v_hasTrace_3957_ = lean_ctor_get_uint8(v_opts_3956_, sizeof(void*)*1);
if (v_hasTrace_3957_ == 0)
{
lean_dec_ref(v_opts_3956_);
lean_dec(v___x_3951_);
v___y_3934_ = v___y_3922_;
v___y_3935_ = v___y_3923_;
goto v___jp_3933_;
}
else
{
lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3958_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3951_, v_opts_3956_, v___x_3958_);
lean_dec_ref(v_opts_3956_);
lean_dec(v___x_3951_);
if (v___x_3959_ == 0)
{
v___y_3934_ = v___y_3922_;
v___y_3935_ = v___y_3923_;
goto v___jp_3933_;
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3960_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3961_ = lean_array_get_size(v_a_3932_);
v___x_3962_ = l_Nat_reprFast(v___x_3961_);
v___x_3963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
v___x_3964_ = l_Lean_MessageData_ofFormat(v___x_3963_);
v___x_3965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3960_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3929_, v___x_3965_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_dec_ref_known(v___x_3966_, 1);
v___y_3934_ = v___y_3922_;
v___y_3935_ = v___y_3923_;
goto v___jp_3933_;
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v_a_3932_);
lean_dec_ref(v___x_3916_);
lean_dec(v_stx_3913_);
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3966_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
}
v___jp_3933_:
{
size_t v_sz_3936_; size_t v___x_3937_; lean_object* v___x_3938_; 
v_sz_3936_ = lean_array_size(v_a_3932_);
v___x_3937_ = ((size_t)0ULL);
lean_inc_ref(v___x_3916_);
lean_inc(v_a_3930_);
v___x_3938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3930_, v___x_3916_, v___x_3917_, v_a_3932_, v_sz_3936_, v___x_3937_, v___x_3927_, v___y_3934_, v___y_3935_);
lean_dec(v_a_3932_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v___x_3939_; size_t v___x_3940_; size_t v___x_3941_; 
lean_dec_ref_known(v___x_3938_, 1);
v___x_3939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3940_ = ((size_t)1ULL);
v___x_3941_ = lean_usize_add(v_i_3920_, v___x_3940_);
v_i_3920_ = v___x_3941_;
v_b_3921_ = v___x_3939_;
goto _start;
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v___x_3916_);
lean_dec(v_stx_3913_);
v_a_3943_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3938_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3938_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec_ref(v___x_3916_);
lean_dec(v_stx_3913_);
v_a_3975_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3931_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3931_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3913_ = stack[0].m_obj;
lean_object* v___x_3914_ = stack[1].m_obj;
lean_object* v___x_3915_ = stack[2].m_obj;
lean_object* v___x_3916_ = stack[3].m_obj;
lean_object* v___x_3917_ = stack[4].m_obj;
lean_object* v_as_3918_ = stack[5].m_obj;
size_t v_sz_3919_ = stack[6].m_num;
size_t v_i_3920_ = stack[7].m_num;
lean_object* v_b_3921_ = stack[8].m_obj;
lean_object* v___y_3922_ = stack[9].m_obj;
lean_object* v___y_3923_ = stack[10].m_obj;
lean_object* v_res_3983_;
v_res_3983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3913_, v___x_3914_, v___x_3915_, v___x_3916_, v___x_3917_, v_as_3918_, v_sz_3919_, v_i_3920_, v_b_3921_, v___y_3922_, v___y_3923_);
stack->m_obj
 = v_res_3983_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3984_, lean_object* v___x_3985_, lean_object* v___x_3986_, lean_object* v___x_3987_, lean_object* v___x_3988_, lean_object* v_as_3989_, lean_object* v_sz_3990_, lean_object* v_i_3991_, lean_object* v_b_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
size_t v_sz_boxed_3996_; size_t v_i_boxed_3997_; lean_object* v_res_3998_; 
v_sz_boxed_3996_ = lean_unbox_usize(v_sz_3990_);
lean_dec(v_sz_3990_);
v_i_boxed_3997_ = lean_unbox_usize(v_i_3991_);
lean_dec(v_i_3991_);
v_res_3998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3984_, v___x_3985_, v___x_3986_, v___x_3987_, v___x_3988_, v_as_3989_, v_sz_boxed_3996_, v_i_boxed_3997_, v_b_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec_ref(v_as_3989_);
lean_dec(v___x_3988_);
lean_dec_ref(v___x_3986_);
lean_dec_ref(v___x_3985_);
return v_res_3998_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3999_, lean_object* v___x_4000_, lean_object* v___x_4001_, lean_object* v___x_4002_, lean_object* v___x_4003_, lean_object* v_as_4004_, size_t v_sz_4005_, size_t v_i_4006_, lean_object* v_b_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
uint8_t v___x_4011_; 
v___x_4011_ = lean_usize_dec_lt(v_i_4006_, v_sz_4005_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
lean_dec_ref(v___x_4002_);
lean_dec(v_stx_3999_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_b_4007_);
return v___x_4012_;
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v_a_4016_; lean_object* v___x_4017_; 
lean_dec_ref(v_b_4007_);
v___x_4013_ = lean_box(0);
v___x_4014_ = l_Lean_inheritedTraceOptions;
v___x_4015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4016_ = lean_array_uget_borrowed(v_as_4004_, v_i_4006_);
lean_inc(v_a_4016_);
lean_inc(v_stx_3999_);
v___x_4017_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3999_, v___x_4000_, v_a_4016_, v___x_4001_, v___y_4008_, v___y_4009_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v_scopes_4040_; lean_object* v___x_4041_; lean_object* v_opts_4042_; uint8_t v_hasTrace_4043_; 
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___x_4017_, 1);
v___x_4037_ = lean_st_ref_get(v___x_4014_);
v___x_4038_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4039_ = lean_st_ref_get(v___y_4009_);
v_scopes_4040_ = lean_ctor_get(v___x_4039_, 2);
lean_inc(v_scopes_4040_);
lean_dec(v___x_4039_);
v___x_4041_ = l_List_head_x21___redArg(v___x_4038_, v_scopes_4040_);
lean_dec(v_scopes_4040_);
v_opts_4042_ = lean_ctor_get(v___x_4041_, 1);
lean_inc_ref(v_opts_4042_);
lean_dec(v___x_4041_);
v_hasTrace_4043_ = lean_ctor_get_uint8(v_opts_4042_, sizeof(void*)*1);
if (v_hasTrace_4043_ == 0)
{
lean_dec_ref(v_opts_4042_);
lean_dec(v___x_4037_);
v___y_4020_ = v___y_4008_;
v___y_4021_ = v___y_4009_;
goto v___jp_4019_;
}
else
{
lean_object* v___x_4044_; uint8_t v___x_4045_; 
v___x_4044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4045_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4037_, v_opts_4042_, v___x_4044_);
lean_dec_ref(v_opts_4042_);
lean_dec(v___x_4037_);
if (v___x_4045_ == 0)
{
v___y_4020_ = v___y_4008_;
v___y_4021_ = v___y_4009_;
goto v___jp_4019_;
}
else
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4046_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4047_ = lean_array_get_size(v_a_4018_);
v___x_4048_ = l_Nat_reprFast(v___x_4047_);
v___x_4049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
v___x_4050_ = l_Lean_MessageData_ofFormat(v___x_4049_);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4046_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4015_, v___x_4051_, v___y_4008_, v___y_4009_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_dec_ref_known(v___x_4052_, 1);
v___y_4020_ = v___y_4008_;
v___y_4021_ = v___y_4009_;
goto v___jp_4019_;
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec(v_a_4018_);
lean_dec_ref(v___x_4002_);
lean_dec(v_stx_3999_);
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
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
v___jp_4019_:
{
size_t v_sz_4022_; size_t v___x_4023_; lean_object* v___x_4024_; 
v_sz_4022_ = lean_array_size(v_a_4018_);
v___x_4023_ = ((size_t)0ULL);
lean_inc_ref(v___x_4002_);
lean_inc(v_a_4016_);
v___x_4024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4016_, v___x_4002_, v___x_4003_, v_a_4018_, v_sz_4022_, v___x_4023_, v___x_4013_, v___y_4020_, v___y_4021_);
lean_dec(v_a_4018_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v___x_4025_; size_t v___x_4026_; size_t v___x_4027_; lean_object* v___x_4028_; 
lean_dec_ref_known(v___x_4024_, 1);
v___x_4025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_4026_ = ((size_t)1ULL);
v___x_4027_ = lean_usize_add(v_i_4006_, v___x_4026_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3999_, v___x_4000_, v___x_4001_, v___x_4002_, v___x_4003_, v_as_4004_, v_sz_4005_, v___x_4027_, v___x_4025_, v___y_4008_, v___y_4009_);
return v___x_4028_;
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v___x_4002_);
lean_dec(v_stx_3999_);
v_a_4029_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4024_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4024_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v___x_4002_);
lean_dec(v_stx_3999_);
v_a_4061_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4017_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4017_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3999_ = stack[0].m_obj;
lean_object* v___x_4000_ = stack[1].m_obj;
lean_object* v___x_4001_ = stack[2].m_obj;
lean_object* v___x_4002_ = stack[3].m_obj;
lean_object* v___x_4003_ = stack[4].m_obj;
lean_object* v_as_4004_ = stack[5].m_obj;
size_t v_sz_4005_ = stack[6].m_num;
size_t v_i_4006_ = stack[7].m_num;
lean_object* v_b_4007_ = stack[8].m_obj;
lean_object* v___y_4008_ = stack[9].m_obj;
lean_object* v___y_4009_ = stack[10].m_obj;
lean_object* v_res_4069_;
v_res_4069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3999_, v___x_4000_, v___x_4001_, v___x_4002_, v___x_4003_, v_as_4004_, v_sz_4005_, v_i_4006_, v_b_4007_, v___y_4008_, v___y_4009_);
stack->m_obj
 = v_res_4069_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_4070_, lean_object* v___x_4071_, lean_object* v___x_4072_, lean_object* v___x_4073_, lean_object* v___x_4074_, lean_object* v_as_4075_, lean_object* v_sz_4076_, lean_object* v_i_4077_, lean_object* v_b_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
size_t v_sz_boxed_4082_; size_t v_i_boxed_4083_; lean_object* v_res_4084_; 
v_sz_boxed_4082_ = lean_unbox_usize(v_sz_4076_);
lean_dec(v_sz_4076_);
v_i_boxed_4083_ = lean_unbox_usize(v_i_4077_);
lean_dec(v_i_4077_);
v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4070_, v___x_4071_, v___x_4072_, v___x_4073_, v___x_4074_, v_as_4075_, v_sz_boxed_4082_, v_i_boxed_4083_, v_b_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec_ref(v_as_4075_);
lean_dec(v___x_4074_);
lean_dec_ref(v___x_4072_);
lean_dec_ref(v___x_4071_);
return v_res_4084_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_4088_, lean_object* v___x_4089_, lean_object* v___x_4090_, lean_object* v___x_4091_, lean_object* v___x_4092_, lean_object* v_as_4093_, size_t v_sz_4094_, size_t v_i_4095_, lean_object* v_b_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
uint8_t v___x_4100_; 
v___x_4100_ = lean_usize_dec_lt(v_i_4095_, v_sz_4094_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; 
lean_dec_ref(v___x_4091_);
lean_dec(v_stx_4088_);
v___x_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4101_, 0, v_b_4096_);
return v___x_4101_;
}
else
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v_a_4105_; lean_object* v___x_4106_; 
lean_dec_ref(v_b_4096_);
v___x_4102_ = lean_box(0);
v___x_4103_ = l_Lean_inheritedTraceOptions;
v___x_4104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4105_ = lean_array_uget_borrowed(v_as_4093_, v_i_4095_);
lean_inc(v_a_4105_);
lean_inc(v_stx_4088_);
v___x_4106_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4088_, v___x_4089_, v_a_4105_, v___x_4090_, v___y_4097_, v___y_4098_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v_scopes_4129_; lean_object* v___x_4130_; lean_object* v_opts_4131_; uint8_t v_hasTrace_4132_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4126_ = lean_st_ref_get(v___x_4103_);
v___x_4127_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4128_ = lean_st_ref_get(v___y_4098_);
v_scopes_4129_ = lean_ctor_get(v___x_4128_, 2);
lean_inc(v_scopes_4129_);
lean_dec(v___x_4128_);
v___x_4130_ = l_List_head_x21___redArg(v___x_4127_, v_scopes_4129_);
lean_dec(v_scopes_4129_);
v_opts_4131_ = lean_ctor_get(v___x_4130_, 1);
lean_inc_ref(v_opts_4131_);
lean_dec(v___x_4130_);
v_hasTrace_4132_ = lean_ctor_get_uint8(v_opts_4131_, sizeof(void*)*1);
if (v_hasTrace_4132_ == 0)
{
lean_dec_ref(v_opts_4131_);
lean_dec(v___x_4126_);
v___y_4109_ = v___y_4097_;
v___y_4110_ = v___y_4098_;
goto v___jp_4108_;
}
else
{
lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4133_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4126_, v_opts_4131_, v___x_4133_);
lean_dec_ref(v_opts_4131_);
lean_dec(v___x_4126_);
if (v___x_4134_ == 0)
{
v___y_4109_ = v___y_4097_;
v___y_4110_ = v___y_4098_;
goto v___jp_4108_;
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4135_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4136_ = lean_array_get_size(v_a_4107_);
v___x_4137_ = l_Nat_reprFast(v___x_4136_);
v___x_4138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
v___x_4139_ = l_Lean_MessageData_ofFormat(v___x_4138_);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4135_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4104_, v___x_4140_, v___y_4097_, v___y_4098_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_dec_ref_known(v___x_4141_, 1);
v___y_4109_ = v___y_4097_;
v___y_4110_ = v___y_4098_;
goto v___jp_4108_;
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_a_4107_);
lean_dec_ref(v___x_4091_);
lean_dec(v_stx_4088_);
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4141_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4141_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
v___jp_4108_:
{
size_t v_sz_4111_; size_t v___x_4112_; lean_object* v___x_4113_; 
v_sz_4111_ = lean_array_size(v_a_4107_);
v___x_4112_ = ((size_t)0ULL);
lean_inc_ref(v___x_4091_);
lean_inc(v_a_4105_);
v___x_4113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4105_, v___x_4091_, v___x_4092_, v_a_4107_, v_sz_4111_, v___x_4112_, v___x_4102_, v___y_4109_, v___y_4110_);
lean_dec(v_a_4107_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v___x_4114_; size_t v___x_4115_; size_t v___x_4116_; 
lean_dec_ref_known(v___x_4113_, 1);
v___x_4114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4115_ = ((size_t)1ULL);
v___x_4116_ = lean_usize_add(v_i_4095_, v___x_4115_);
v_i_4095_ = v___x_4116_;
v_b_4096_ = v___x_4114_;
goto _start;
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec_ref(v___x_4091_);
lean_dec(v_stx_4088_);
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
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref(v___x_4091_);
lean_dec(v_stx_4088_);
v_a_4150_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4106_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4106_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_4088_ = stack[0].m_obj;
lean_object* v___x_4089_ = stack[1].m_obj;
lean_object* v___x_4090_ = stack[2].m_obj;
lean_object* v___x_4091_ = stack[3].m_obj;
lean_object* v___x_4092_ = stack[4].m_obj;
lean_object* v_as_4093_ = stack[5].m_obj;
size_t v_sz_4094_ = stack[6].m_num;
size_t v_i_4095_ = stack[7].m_num;
lean_object* v_b_4096_ = stack[8].m_obj;
lean_object* v___y_4097_ = stack[9].m_obj;
lean_object* v___y_4098_ = stack[10].m_obj;
lean_object* v_res_4158_;
v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4088_, v___x_4089_, v___x_4090_, v___x_4091_, v___x_4092_, v_as_4093_, v_sz_4094_, v_i_4095_, v_b_4096_, v___y_4097_, v___y_4098_);
stack->m_obj
 = v_res_4158_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4159_, lean_object* v___x_4160_, lean_object* v___x_4161_, lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v_as_4164_, lean_object* v_sz_4165_, lean_object* v_i_4166_, lean_object* v_b_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
size_t v_sz_boxed_4171_; size_t v_i_boxed_4172_; lean_object* v_res_4173_; 
v_sz_boxed_4171_ = lean_unbox_usize(v_sz_4165_);
lean_dec(v_sz_4165_);
v_i_boxed_4172_ = lean_unbox_usize(v_i_4166_);
lean_dec(v_i_4166_);
v_res_4173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4159_, v___x_4160_, v___x_4161_, v___x_4162_, v___x_4163_, v_as_4164_, v_sz_boxed_4171_, v_i_boxed_4172_, v_b_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec_ref(v_as_4164_);
lean_dec(v___x_4163_);
lean_dec_ref(v___x_4161_);
lean_dec_ref(v___x_4160_);
return v_res_4173_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4174_, lean_object* v___x_4175_, lean_object* v___x_4176_, lean_object* v___x_4177_, lean_object* v___x_4178_, lean_object* v_as_4179_, size_t v_sz_4180_, size_t v_i_4181_, lean_object* v_b_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
uint8_t v___x_4186_; 
v___x_4186_ = lean_usize_dec_lt(v_i_4181_, v_sz_4180_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; 
lean_dec_ref(v___x_4177_);
lean_dec(v_stx_4174_);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_b_4182_);
return v___x_4187_;
}
else
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v_a_4191_; lean_object* v___x_4192_; 
lean_dec_ref(v_b_4182_);
v___x_4188_ = lean_box(0);
v___x_4189_ = l_Lean_inheritedTraceOptions;
v___x_4190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4191_ = lean_array_uget_borrowed(v_as_4179_, v_i_4181_);
lean_inc(v_a_4191_);
lean_inc(v_stx_4174_);
v___x_4192_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4174_, v___x_4175_, v_a_4191_, v___x_4176_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v_scopes_4215_; lean_object* v___x_4216_; lean_object* v_opts_4217_; uint8_t v_hasTrace_4218_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4212_ = lean_st_ref_get(v___x_4189_);
v___x_4213_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4214_ = lean_st_ref_get(v___y_4184_);
v_scopes_4215_ = lean_ctor_get(v___x_4214_, 2);
lean_inc(v_scopes_4215_);
lean_dec(v___x_4214_);
v___x_4216_ = l_List_head_x21___redArg(v___x_4213_, v_scopes_4215_);
lean_dec(v_scopes_4215_);
v_opts_4217_ = lean_ctor_get(v___x_4216_, 1);
lean_inc_ref(v_opts_4217_);
lean_dec(v___x_4216_);
v_hasTrace_4218_ = lean_ctor_get_uint8(v_opts_4217_, sizeof(void*)*1);
if (v_hasTrace_4218_ == 0)
{
lean_dec_ref(v_opts_4217_);
lean_dec(v___x_4212_);
v___y_4195_ = v___y_4183_;
v___y_4196_ = v___y_4184_;
goto v___jp_4194_;
}
else
{
lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4219_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4212_, v_opts_4217_, v___x_4219_);
lean_dec_ref(v_opts_4217_);
lean_dec(v___x_4212_);
if (v___x_4220_ == 0)
{
v___y_4195_ = v___y_4183_;
v___y_4196_ = v___y_4184_;
goto v___jp_4194_;
}
else
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4221_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4222_ = lean_array_get_size(v_a_4193_);
v___x_4223_ = l_Nat_reprFast(v___x_4222_);
v___x_4224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
v___x_4225_ = l_Lean_MessageData_ofFormat(v___x_4224_);
v___x_4226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4221_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4190_, v___x_4226_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_dec_ref_known(v___x_4227_, 1);
v___y_4195_ = v___y_4183_;
v___y_4196_ = v___y_4184_;
goto v___jp_4194_;
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec(v_a_4193_);
lean_dec_ref(v___x_4177_);
lean_dec(v_stx_4174_);
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4227_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4227_);
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
v___jp_4194_:
{
size_t v_sz_4197_; size_t v___x_4198_; lean_object* v___x_4199_; 
v_sz_4197_ = lean_array_size(v_a_4193_);
v___x_4198_ = ((size_t)0ULL);
lean_inc_ref(v___x_4177_);
lean_inc(v_a_4191_);
v___x_4199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4191_, v___x_4177_, v___x_4178_, v_a_4193_, v_sz_4197_, v___x_4198_, v___x_4188_, v___y_4195_, v___y_4196_);
lean_dec(v_a_4193_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v___x_4200_; size_t v___x_4201_; size_t v___x_4202_; lean_object* v___x_4203_; 
lean_dec_ref_known(v___x_4199_, 1);
v___x_4200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4201_ = ((size_t)1ULL);
v___x_4202_ = lean_usize_add(v_i_4181_, v___x_4201_);
v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4174_, v___x_4175_, v___x_4176_, v___x_4177_, v___x_4178_, v_as_4179_, v_sz_4180_, v___x_4202_, v___x_4200_, v___y_4183_, v___y_4184_);
return v___x_4203_;
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
lean_dec_ref(v___x_4177_);
lean_dec(v_stx_4174_);
v_a_4204_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4199_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4199_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec_ref(v___x_4177_);
lean_dec(v_stx_4174_);
v_a_4236_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4192_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4192_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_4174_ = stack[0].m_obj;
lean_object* v___x_4175_ = stack[1].m_obj;
lean_object* v___x_4176_ = stack[2].m_obj;
lean_object* v___x_4177_ = stack[3].m_obj;
lean_object* v___x_4178_ = stack[4].m_obj;
lean_object* v_as_4179_ = stack[5].m_obj;
size_t v_sz_4180_ = stack[6].m_num;
size_t v_i_4181_ = stack[7].m_num;
lean_object* v_b_4182_ = stack[8].m_obj;
lean_object* v___y_4183_ = stack[9].m_obj;
lean_object* v___y_4184_ = stack[10].m_obj;
lean_object* v_res_4244_;
v_res_4244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4174_, v___x_4175_, v___x_4176_, v___x_4177_, v___x_4178_, v_as_4179_, v_sz_4180_, v_i_4181_, v_b_4182_, v___y_4183_, v___y_4184_);
stack->m_obj
 = v_res_4244_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4245_, lean_object* v___x_4246_, lean_object* v___x_4247_, lean_object* v___x_4248_, lean_object* v___x_4249_, lean_object* v_as_4250_, lean_object* v_sz_4251_, lean_object* v_i_4252_, lean_object* v_b_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
size_t v_sz_boxed_4257_; size_t v_i_boxed_4258_; lean_object* v_res_4259_; 
v_sz_boxed_4257_ = lean_unbox_usize(v_sz_4251_);
lean_dec(v_sz_4251_);
v_i_boxed_4258_ = lean_unbox_usize(v_i_4252_);
lean_dec(v_i_4252_);
v_res_4259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4245_, v___x_4246_, v___x_4247_, v___x_4248_, v___x_4249_, v_as_4250_, v_sz_boxed_4257_, v_i_boxed_4258_, v_b_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec_ref(v_as_4250_);
lean_dec(v___x_4249_);
lean_dec_ref(v___x_4247_);
lean_dec_ref(v___x_4246_);
return v_res_4259_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4260_, lean_object* v_stx_4261_, lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v___x_4264_, lean_object* v___x_4265_, lean_object* v_n_4266_, lean_object* v_b_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
if (lean_obj_tag(v_n_4266_) == 0)
{
lean_object* v_cs_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; size_t v_sz_4274_; size_t v___x_4275_; lean_object* v___x_4276_; 
v_cs_4271_ = lean_ctor_get(v_n_4266_, 0);
v___x_4272_ = lean_box(0);
v___x_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
lean_ctor_set(v___x_4273_, 1, v_b_4267_);
v_sz_4274_ = lean_array_size(v_cs_4271_);
v___x_4275_ = ((size_t)0ULL);
v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4260_, v_stx_4261_, v___x_4262_, v___x_4263_, v___x_4264_, v___x_4265_, v_cs_4271_, v_sz_4274_, v___x_4275_, v___x_4273_, v___y_4268_, v___y_4269_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4291_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4279_ = v___x_4276_;
v_isShared_4280_ = v_isSharedCheck_4291_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4276_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4291_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v_fst_4281_; 
v_fst_4281_ = lean_ctor_get(v_a_4277_, 0);
if (lean_obj_tag(v_fst_4281_) == 0)
{
lean_object* v_snd_4282_; lean_object* v___x_4283_; lean_object* v___x_4285_; 
v_snd_4282_ = lean_ctor_get(v_a_4277_, 1);
lean_inc(v_snd_4282_);
lean_dec(v_a_4277_);
v___x_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4283_, 0, v_snd_4282_);
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 0, v___x_4283_);
v___x_4285_ = v___x_4279_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v___x_4283_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
else
{
lean_object* v_val_4287_; lean_object* v___x_4289_; 
lean_inc_ref(v_fst_4281_);
lean_dec(v_a_4277_);
v_val_4287_ = lean_ctor_get(v_fst_4281_, 0);
lean_inc(v_val_4287_);
lean_dec_ref_known(v_fst_4281_, 1);
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 0, v_val_4287_);
v___x_4289_ = v___x_4279_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_val_4287_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
v_a_4292_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4276_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4276_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
else
{
lean_object* v_vs_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; size_t v_sz_4303_; size_t v___x_4304_; lean_object* v___x_4305_; 
v_vs_4300_ = lean_ctor_get(v_n_4266_, 0);
v___x_4301_ = lean_box(0);
v___x_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
lean_ctor_set(v___x_4302_, 1, v_b_4267_);
v_sz_4303_ = lean_array_size(v_vs_4300_);
v___x_4304_ = ((size_t)0ULL);
v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4261_, v___x_4262_, v___x_4263_, v___x_4264_, v___x_4265_, v_vs_4300_, v_sz_4303_, v___x_4304_, v___x_4302_, v___y_4268_, v___y_4269_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4320_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4320_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4320_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v_fst_4310_; 
v_fst_4310_ = lean_ctor_get(v_a_4306_, 0);
if (lean_obj_tag(v_fst_4310_) == 0)
{
lean_object* v_snd_4311_; lean_object* v___x_4312_; lean_object* v___x_4314_; 
v_snd_4311_ = lean_ctor_get(v_a_4306_, 1);
lean_inc(v_snd_4311_);
lean_dec(v_a_4306_);
v___x_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4312_, 0, v_snd_4311_);
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v___x_4312_);
v___x_4314_ = v___x_4308_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
else
{
lean_object* v_val_4316_; lean_object* v___x_4318_; 
lean_inc_ref(v_fst_4310_);
lean_dec(v_a_4306_);
v_val_4316_ = lean_ctor_get(v_fst_4310_, 0);
lean_inc(v_val_4316_);
lean_dec_ref_known(v_fst_4310_, 1);
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v_val_4316_);
v___x_4318_ = v___x_4308_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_val_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
v_a_4321_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4305_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4305_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4260_ = stack[0].m_obj;
lean_object* v_stx_4261_ = stack[1].m_obj;
lean_object* v___x_4262_ = stack[2].m_obj;
lean_object* v___x_4263_ = stack[3].m_obj;
lean_object* v___x_4264_ = stack[4].m_obj;
lean_object* v___x_4265_ = stack[5].m_obj;
lean_object* v_n_4266_ = stack[6].m_obj;
lean_object* v_b_4267_ = stack[7].m_obj;
lean_object* v___y_4268_ = stack[8].m_obj;
lean_object* v___y_4269_ = stack[9].m_obj;
lean_object* v_res_4329_;
v_res_4329_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4260_, v_stx_4261_, v___x_4262_, v___x_4263_, v___x_4264_, v___x_4265_, v_n_4266_, v_b_4267_, v___y_4268_, v___y_4269_);
stack->m_obj
 = v_res_4329_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4330_, lean_object* v_stx_4331_, lean_object* v___x_4332_, lean_object* v___x_4333_, lean_object* v___x_4334_, lean_object* v___x_4335_, lean_object* v_as_4336_, size_t v_sz_4337_, size_t v_i_4338_, lean_object* v_b_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
uint8_t v___x_4343_; 
v___x_4343_ = lean_usize_dec_lt(v_i_4338_, v_sz_4337_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; 
lean_dec_ref(v___x_4334_);
lean_dec(v_stx_4331_);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_b_4339_);
return v___x_4344_;
}
else
{
lean_object* v_snd_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4379_; 
v_snd_4345_ = lean_ctor_get(v_b_4339_, 1);
v_isSharedCheck_4379_ = !lean_is_exclusive(v_b_4339_);
if (v_isSharedCheck_4379_ == 0)
{
lean_object* v_unused_4380_; 
v_unused_4380_ = lean_ctor_get(v_b_4339_, 0);
lean_dec(v_unused_4380_);
v___x_4347_ = v_b_4339_;
v_isShared_4348_ = v_isSharedCheck_4379_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_snd_4345_);
lean_dec(v_b_4339_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4379_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4349_; lean_object* v_a_4350_; lean_object* v___x_4351_; 
v___x_4349_ = lean_box(0);
v_a_4350_ = lean_array_uget_borrowed(v_as_4336_, v_i_4338_);
lean_inc(v_snd_4345_);
lean_inc_ref(v___x_4334_);
lean_inc(v_stx_4331_);
v___x_4351_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4330_, v_stx_4331_, v___x_4332_, v___x_4333_, v___x_4334_, v___x_4335_, v_a_4350_, v_snd_4345_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4370_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4370_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4370_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
if (lean_obj_tag(v_a_4352_) == 0)
{
lean_object* v___x_4356_; lean_object* v___x_4358_; 
lean_dec_ref(v___x_4334_);
lean_dec(v_stx_4331_);
v___x_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4356_, 0, v_a_4352_);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v___x_4356_);
v___x_4358_ = v___x_4347_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v_snd_4345_);
v___x_4358_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v___x_4360_; 
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v___x_4358_);
v___x_4360_ = v___x_4354_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; 
lean_del_object(v___x_4354_);
lean_dec(v_snd_4345_);
v_a_4363_ = lean_ctor_get(v_a_4352_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v_a_4352_, 1);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 1, v_a_4363_);
lean_ctor_set(v___x_4347_, 0, v___x_4349_);
v___x_4365_ = v___x_4347_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v_a_4363_);
v___x_4365_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
size_t v___x_4366_; size_t v___x_4367_; 
v___x_4366_ = ((size_t)1ULL);
v___x_4367_ = lean_usize_add(v_i_4338_, v___x_4366_);
v_i_4338_ = v___x_4367_;
v_b_4339_ = v___x_4365_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_del_object(v___x_4347_);
lean_dec(v_snd_4345_);
lean_dec_ref(v___x_4334_);
lean_dec(v_stx_4331_);
v_a_4371_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4351_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4351_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_4330_ = stack[0].m_obj;
lean_object* v_stx_4331_ = stack[1].m_obj;
lean_object* v___x_4332_ = stack[2].m_obj;
lean_object* v___x_4333_ = stack[3].m_obj;
lean_object* v___x_4334_ = stack[4].m_obj;
lean_object* v___x_4335_ = stack[5].m_obj;
lean_object* v_as_4336_ = stack[6].m_obj;
size_t v_sz_4337_ = stack[7].m_num;
size_t v_i_4338_ = stack[8].m_num;
lean_object* v_b_4339_ = stack[9].m_obj;
lean_object* v___y_4340_ = stack[10].m_obj;
lean_object* v___y_4341_ = stack[11].m_obj;
lean_object* v_res_4381_;
v_res_4381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4330_, v_stx_4331_, v___x_4332_, v___x_4333_, v___x_4334_, v___x_4335_, v_as_4336_, v_sz_4337_, v_i_4338_, v_b_4339_, v___y_4340_, v___y_4341_);
stack->m_obj
 = v_res_4381_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4382_, lean_object* v_stx_4383_, lean_object* v___x_4384_, lean_object* v___x_4385_, lean_object* v___x_4386_, lean_object* v___x_4387_, lean_object* v_as_4388_, lean_object* v_sz_4389_, lean_object* v_i_4390_, lean_object* v_b_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
size_t v_sz_boxed_4395_; size_t v_i_boxed_4396_; lean_object* v_res_4397_; 
v_sz_boxed_4395_ = lean_unbox_usize(v_sz_4389_);
lean_dec(v_sz_4389_);
v_i_boxed_4396_ = lean_unbox_usize(v_i_4390_);
lean_dec(v_i_4390_);
v_res_4397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4382_, v_stx_4383_, v___x_4384_, v___x_4385_, v___x_4386_, v___x_4387_, v_as_4388_, v_sz_boxed_4395_, v_i_boxed_4396_, v_b_4391_, v___y_4392_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec_ref(v_as_4388_);
lean_dec(v___x_4387_);
lean_dec_ref(v___x_4385_);
lean_dec_ref(v___x_4384_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4398_, lean_object* v_stx_4399_, lean_object* v___x_4400_, lean_object* v___x_4401_, lean_object* v___x_4402_, lean_object* v___x_4403_, lean_object* v_n_4404_, lean_object* v_b_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4398_, v_stx_4399_, v___x_4400_, v___x_4401_, v___x_4402_, v___x_4403_, v_n_4404_, v_b_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec_ref(v_n_4404_);
lean_dec(v___x_4403_);
lean_dec_ref(v___x_4401_);
lean_dec_ref(v___x_4400_);
return v_res_4409_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4410_, lean_object* v___x_4411_, lean_object* v_stx_4412_, lean_object* v___x_4413_, lean_object* v___x_4414_, lean_object* v_t_4415_, lean_object* v_init_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v_root_4420_; lean_object* v_tail_4421_; lean_object* v___x_4422_; 
v_root_4420_ = lean_ctor_get(v_t_4415_, 0);
v_tail_4421_ = lean_ctor_get(v_t_4415_, 1);
lean_inc_ref(v___x_4410_);
lean_inc(v_stx_4412_);
v___x_4422_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4416_, v_stx_4412_, v___x_4413_, v___x_4414_, v___x_4410_, v___x_4411_, v_root_4420_, v_init_4416_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4459_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4459_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4459_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
if (lean_obj_tag(v_a_4423_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4429_; 
lean_dec(v_stx_4412_);
lean_dec_ref(v___x_4410_);
v_a_4427_ = lean_ctor_get(v_a_4423_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v_a_4423_, 1);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v_a_4427_);
v___x_4429_ = v___x_4425_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4427_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; size_t v_sz_4434_; size_t v___x_4435_; lean_object* v___x_4436_; 
lean_del_object(v___x_4425_);
v_a_4431_ = lean_ctor_get(v_a_4423_, 0);
lean_inc(v_a_4431_);
lean_dec_ref_known(v_a_4423_, 1);
v___x_4432_ = lean_box(0);
v___x_4433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
lean_ctor_set(v___x_4433_, 1, v_a_4431_);
v_sz_4434_ = lean_array_size(v_tail_4421_);
v___x_4435_ = ((size_t)0ULL);
v___x_4436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4412_, v___x_4413_, v___x_4414_, v___x_4410_, v___x_4411_, v_tail_4421_, v_sz_4434_, v___x_4435_, v___x_4433_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4450_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4439_ = v___x_4436_;
v_isShared_4440_ = v_isSharedCheck_4450_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4450_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v_fst_4441_; 
v_fst_4441_ = lean_ctor_get(v_a_4437_, 0);
if (lean_obj_tag(v_fst_4441_) == 0)
{
lean_object* v_snd_4442_; lean_object* v___x_4444_; 
v_snd_4442_ = lean_ctor_get(v_a_4437_, 1);
lean_inc(v_snd_4442_);
lean_dec(v_a_4437_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v_snd_4442_);
v___x_4444_ = v___x_4439_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_snd_4442_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
else
{
lean_object* v_val_4446_; lean_object* v___x_4448_; 
lean_inc_ref(v_fst_4441_);
lean_dec(v_a_4437_);
v_val_4446_ = lean_ctor_get(v_fst_4441_, 0);
lean_inc(v_val_4446_);
lean_dec_ref_known(v_fst_4441_, 1);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v_val_4446_);
v___x_4448_ = v___x_4439_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_val_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
v_a_4451_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4436_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4436_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec(v_stx_4412_);
lean_dec_ref(v___x_4410_);
v_a_4460_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4422_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4422_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4410_ = stack[0].m_obj;
lean_object* v___x_4411_ = stack[1].m_obj;
lean_object* v_stx_4412_ = stack[2].m_obj;
lean_object* v___x_4413_ = stack[3].m_obj;
lean_object* v___x_4414_ = stack[4].m_obj;
lean_object* v_t_4415_ = stack[5].m_obj;
lean_object* v_init_4416_ = stack[6].m_obj;
lean_object* v___y_4417_ = stack[7].m_obj;
lean_object* v___y_4418_ = stack[8].m_obj;
lean_object* v_res_4468_;
v_res_4468_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4410_, v___x_4411_, v_stx_4412_, v___x_4413_, v___x_4414_, v_t_4415_, v_init_4416_, v___y_4417_, v___y_4418_);
stack->m_obj
 = v_res_4468_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4469_, lean_object* v___x_4470_, lean_object* v_stx_4471_, lean_object* v___x_4472_, lean_object* v___x_4473_, lean_object* v_t_4474_, lean_object* v_init_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4469_, v___x_4470_, v_stx_4471_, v___x_4472_, v___x_4473_, v_t_4474_, v_init_4475_, v___y_4476_, v___y_4477_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec_ref(v_t_4474_);
lean_dec_ref(v___x_4473_);
lean_dec_ref(v___x_4472_);
lean_dec(v___x_4470_);
return v_res_4479_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4482_ = l_Lean_stringToMessageData(v___x_4481_);
return v___x_4482_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4487_ = l_Lean_stringToMessageData(v___x_4486_);
return v___x_4487_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4490_ = l_Lean_stringToMessageData(v___x_4489_);
return v___x_4490_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4493_ = l_Lean_stringToMessageData(v___x_4492_);
return v___x_4493_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v_scopes_4503_; lean_object* v___x_4504_; lean_object* v_opts_4505_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; uint8_t v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; uint8_t v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; uint8_t v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; uint8_t v___y_4549_; lean_object* v___y_4550_; uint8_t v___y_4559_; lean_object* v___y_4560_; uint8_t v___y_4561_; lean_object* v___y_4562_; uint8_t v___y_4563_; lean_object* v___y_4564_; uint8_t v___y_4573_; uint8_t v___y_4574_; uint8_t v___y_4575_; uint8_t v___y_4609_; lean_object* v___x_4616_; uint8_t v___x_4617_; 
v___x_4501_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4502_ = lean_st_ref_get(v___y_4496_);
v_scopes_4503_ = lean_ctor_get(v___x_4502_, 2);
lean_inc(v_scopes_4503_);
lean_dec(v___x_4502_);
v___x_4504_ = l_List_head_x21___redArg(v___x_4501_, v_scopes_4503_);
lean_dec(v_scopes_4503_);
v_opts_4505_ = lean_ctor_get(v___x_4504_, 1);
lean_inc_ref(v_opts_4505_);
lean_dec(v___x_4504_);
v___x_4616_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4617_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4505_, v___x_4616_);
if (v___x_4617_ == 0)
{
lean_object* v___x_4618_; uint8_t v___x_4619_; 
v___x_4618_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4619_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4505_, v___x_4618_);
v___y_4609_ = v___x_4619_;
goto v___jp_4608_;
}
else
{
v___y_4609_ = v___x_4617_;
goto v___jp_4608_;
}
v___jp_4498_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4499_ = lean_box(0);
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
return v___x_4500_;
}
v___jp_4506_:
{
lean_object* v___x_4511_; lean_object* v_line_4512_; lean_object* v___x_4513_; lean_object* v_messages_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v_a_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_inc_ref_n(v___y_4508_, 2);
v___x_4511_ = l_Lean_FileMap_toPosition(v___y_4508_, v___y_4510_);
lean_dec(v___y_4510_);
v_line_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_line_4512_);
lean_dec_ref(v___x_4511_);
v___x_4513_ = lean_st_ref_get(v___y_4507_);
v_messages_4514_ = lean_ctor_get(v___x_4513_, 1);
lean_inc_ref(v_messages_4514_);
lean_dec(v___x_4513_);
v___x_4515_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4514_);
v___x_4516_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4507_);
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_a_4517_);
lean_dec_ref(v___x_4516_);
v___x_4518_ = lean_box(0);
v___x_4519_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4508_, v_line_4512_, v_stx_4494_, v_opts_4505_, v___x_4515_, v_a_4517_, v___x_4518_, v___y_4509_, v___y_4507_);
lean_dec(v_a_4517_);
lean_dec_ref(v___x_4515_);
lean_dec_ref(v_opts_4505_);
lean_dec(v_line_4512_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4526_ == 0)
{
lean_object* v_unused_4527_; 
v_unused_4527_ = lean_ctor_get(v___x_4519_, 0);
lean_dec(v_unused_4527_);
v___x_4521_ = v___x_4519_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_dec(v___x_4519_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 0, v___x_4518_);
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4518_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
else
{
return v___x_4519_;
}
}
v___jp_4528_:
{
lean_object* v_fileMap_4532_; lean_object* v___x_4533_; 
v_fileMap_4532_ = lean_ctor_get(v___y_4530_, 1);
v___x_4533_ = l_Lean_Syntax_getPos_x3f(v_stx_4494_, v___y_4529_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_unsigned_to_nat(0u);
v___y_4507_ = v___y_4531_;
v___y_4508_ = v_fileMap_4532_;
v___y_4509_ = v___y_4530_;
v___y_4510_ = v___x_4534_;
goto v___jp_4506_;
}
else
{
lean_object* v_val_4535_; 
v_val_4535_ = lean_ctor_get(v___x_4533_, 0);
lean_inc(v_val_4535_);
lean_dec_ref_known(v___x_4533_, 1);
v___y_4507_ = v___y_4531_;
v___y_4508_ = v_fileMap_4532_;
v___y_4509_ = v___y_4530_;
v___y_4510_ = v_val_4535_;
goto v___jp_4506_;
}
}
v___jp_4536_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
lean_inc_ref(v___y_4540_);
v___x_4541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___y_4540_);
v___x_4542_ = l_Lean_MessageData_ofFormat(v___x_4541_);
v___x_4543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___y_4539_);
lean_ctor_set(v___x_4543_, 1, v___x_4542_);
lean_inc(v___y_4538_);
v___x_4544_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___y_4538_, v___x_4543_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_dec_ref_known(v___x_4544_, 1);
v___y_4529_ = v___y_4537_;
v___y_4530_ = v___y_4495_;
v___y_4531_ = v___y_4496_;
goto v___jp_4528_;
}
else
{
lean_dec_ref(v_opts_4505_);
lean_dec(v_stx_4494_);
return v___x_4544_;
}
}
v___jp_4545_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
lean_inc_ref(v___y_4550_);
v___x_4551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4551_, 0, v___y_4550_);
v___x_4552_ = l_Lean_MessageData_ofFormat(v___x_4551_);
v___x_4553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___y_4547_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
v___x_4554_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4553_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
if (v___y_4546_ == 0)
{
lean_object* v___x_4556_; 
v___x_4556_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4537_ = v___y_4549_;
v___y_4538_ = v___y_4548_;
v___y_4539_ = v___x_4555_;
v___y_4540_ = v___x_4556_;
goto v___jp_4536_;
}
else
{
lean_object* v___x_4557_; 
v___x_4557_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4537_ = v___y_4549_;
v___y_4538_ = v___y_4548_;
v___y_4539_ = v___x_4555_;
v___y_4540_ = v___x_4557_;
goto v___jp_4536_;
}
}
v___jp_4558_:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
lean_inc_ref(v___y_4564_);
v___x_4565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4565_, 0, v___y_4564_);
v___x_4566_ = l_Lean_MessageData_ofFormat(v___x_4565_);
lean_inc_ref(v___y_4560_);
v___x_4567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___y_4560_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4567_);
lean_ctor_set(v___x_4569_, 1, v___x_4568_);
if (v___y_4563_ == 0)
{
lean_object* v___x_4570_; 
v___x_4570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4546_ = v___y_4559_;
v___y_4547_ = v___x_4569_;
v___y_4548_ = v___y_4562_;
v___y_4549_ = v___y_4561_;
v___y_4550_ = v___x_4570_;
goto v___jp_4545_;
}
else
{
lean_object* v___x_4571_; 
v___x_4571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4546_ = v___y_4559_;
v___y_4547_ = v___x_4569_;
v___y_4548_ = v___y_4562_;
v___y_4549_ = v___y_4561_;
v___y_4550_ = v___x_4571_;
goto v___jp_4545_;
}
}
v___jp_4572_:
{
lean_object* v___x_4576_; lean_object* v_a_4577_; uint8_t v___x_4578_; 
v___x_4576_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4494_, v___y_4495_, v___y_4496_);
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4577_);
lean_dec_ref(v___x_4576_);
v___x_4578_ = lean_unbox(v_a_4577_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v_scopes_4583_; lean_object* v___x_4584_; lean_object* v_opts_4585_; uint8_t v_hasTrace_4586_; 
v___x_4579_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4580_ = l_Lean_inheritedTraceOptions;
v___x_4581_ = lean_st_ref_get(v___x_4580_);
v___x_4582_ = lean_st_ref_get(v___y_4496_);
v_scopes_4583_ = lean_ctor_get(v___x_4582_, 2);
lean_inc(v_scopes_4583_);
lean_dec(v___x_4582_);
v___x_4584_ = l_List_head_x21___redArg(v___x_4501_, v_scopes_4583_);
lean_dec(v_scopes_4583_);
v_opts_4585_ = lean_ctor_get(v___x_4584_, 1);
lean_inc_ref(v_opts_4585_);
lean_dec(v___x_4584_);
v_hasTrace_4586_ = lean_ctor_get_uint8(v_opts_4585_, sizeof(void*)*1);
if (v_hasTrace_4586_ == 0)
{
uint8_t v___x_4587_; 
lean_dec_ref(v_opts_4585_);
lean_dec(v___x_4581_);
v___x_4587_ = lean_unbox(v_a_4577_);
lean_dec(v_a_4577_);
v___y_4529_ = v___x_4587_;
v___y_4530_ = v___y_4495_;
v___y_4531_ = v___y_4496_;
goto v___jp_4528_;
}
else
{
lean_object* v___x_4588_; uint8_t v___x_4589_; 
v___x_4588_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4589_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4581_, v_opts_4585_, v___x_4588_);
lean_dec_ref(v_opts_4585_);
lean_dec(v___x_4581_);
if (v___x_4589_ == 0)
{
uint8_t v___x_4590_; 
v___x_4590_ = lean_unbox(v_a_4577_);
lean_dec(v_a_4577_);
v___y_4529_ = v___x_4590_;
v___y_4530_ = v___y_4495_;
v___y_4531_ = v___y_4496_;
goto v___jp_4528_;
}
else
{
lean_object* v___x_4591_; 
v___x_4591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4574_ == 0)
{
lean_object* v___x_4592_; uint8_t v___x_4593_; 
v___x_4592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4593_ = lean_unbox(v_a_4577_);
lean_dec(v_a_4577_);
v___y_4559_ = v___y_4573_;
v___y_4560_ = v___x_4591_;
v___y_4561_ = v___x_4593_;
v___y_4562_ = v___x_4579_;
v___y_4563_ = v___y_4575_;
v___y_4564_ = v___x_4592_;
goto v___jp_4558_;
}
else
{
lean_object* v___x_4594_; uint8_t v___x_4595_; 
v___x_4594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4595_ = lean_unbox(v_a_4577_);
lean_dec(v_a_4577_);
v___y_4559_ = v___y_4573_;
v___y_4560_ = v___x_4591_;
v___y_4561_ = v___x_4595_;
v___y_4562_ = v___x_4579_;
v___y_4563_ = v___y_4575_;
v___y_4564_ = v___x_4594_;
goto v___jp_4558_;
}
}
}
}
else
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v_scopes_4600_; lean_object* v___x_4601_; lean_object* v_opts_4602_; uint8_t v_hasTrace_4603_; 
lean_dec(v_a_4577_);
lean_dec_ref(v_opts_4505_);
lean_dec(v_stx_4494_);
v___x_4596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4597_ = l_Lean_inheritedTraceOptions;
v___x_4598_ = lean_st_ref_get(v___x_4597_);
v___x_4599_ = lean_st_ref_get(v___y_4496_);
v_scopes_4600_ = lean_ctor_get(v___x_4599_, 2);
lean_inc(v_scopes_4600_);
lean_dec(v___x_4599_);
v___x_4601_ = l_List_head_x21___redArg(v___x_4501_, v_scopes_4600_);
lean_dec(v_scopes_4600_);
v_opts_4602_ = lean_ctor_get(v___x_4601_, 1);
lean_inc_ref(v_opts_4602_);
lean_dec(v___x_4601_);
v_hasTrace_4603_ = lean_ctor_get_uint8(v_opts_4602_, sizeof(void*)*1);
if (v_hasTrace_4603_ == 0)
{
lean_dec_ref(v_opts_4602_);
lean_dec(v___x_4598_);
goto v___jp_4498_;
}
else
{
lean_object* v___x_4604_; uint8_t v___x_4605_; 
v___x_4604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4605_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4598_, v_opts_4602_, v___x_4604_);
lean_dec_ref(v_opts_4602_);
lean_dec(v___x_4598_);
if (v___x_4605_ == 0)
{
goto v___jp_4498_;
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4607_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4596_, v___x_4606_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_dec_ref_known(v___x_4607_, 1);
goto v___jp_4498_;
}
else
{
return v___x_4607_;
}
}
}
}
}
v___jp_4608_:
{
lean_object* v___x_4610_; uint8_t v___x_4611_; lean_object* v___x_4612_; uint8_t v___x_4613_; 
v___x_4610_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4611_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4505_, v___x_4610_);
v___x_4612_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4613_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4505_, v___x_4612_);
if (v___y_4609_ == 0)
{
if (v___x_4611_ == 0)
{
if (v___x_4613_ == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
lean_dec_ref(v_opts_4505_);
lean_dec(v_stx_4494_);
v___x_4614_ = lean_box(0);
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
else
{
v___y_4573_ = v___x_4613_;
v___y_4574_ = v___y_4609_;
v___y_4575_ = v___x_4611_;
goto v___jp_4572_;
}
}
else
{
v___y_4573_ = v___x_4613_;
v___y_4574_ = v___y_4609_;
v___y_4575_ = v___x_4611_;
goto v___jp_4572_;
}
}
else
{
v___y_4573_ = v___x_4613_;
v___y_4574_ = v___y_4609_;
v___y_4575_ = v___x_4611_;
goto v___jp_4572_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_4494_ = stack[0].m_obj;
lean_object* v___y_4495_ = stack[1].m_obj;
lean_object* v___y_4496_ = stack[2].m_obj;
lean_object* v_res_4620_;
v_res_4620_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4494_, v___y_4495_, v___y_4496_);
stack->m_obj
 = v_res_4620_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4621_, v___y_4622_, v___y_4623_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
return v_res_4625_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4639_ = l_Lean_Elab_Command_addLinter(v___x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4640_;
v_res_4640_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4640_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4642_;
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
