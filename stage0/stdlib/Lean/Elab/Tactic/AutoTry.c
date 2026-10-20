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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(lean_object* v_opts_238_, lean_object* v_opt_239_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0___boxed(lean_object* v_opts_246_, lean_object* v_opt_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_246_, v_opt_247_);
lean_dec_ref(v_opt_247_);
lean_dec_ref(v_opts_246_);
return v_res_248_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1(void){
_start:
{
lean_object* v___x_255_; uint64_t v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0));
v___x_256_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2(void){
_start:
{
uint64_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__1);
v___x_258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__0));
v___x_259_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set_uint64(v___x_259_, sizeof(void*)*1, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4(void){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_262_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_266_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_ctor_set(v___x_266_, 2, v___x_265_);
lean_ctor_set(v___x_266_, 3, v___x_265_);
lean_ctor_set(v___x_266_, 4, v___x_265_);
lean_ctor_set(v___x_266_, 5, v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_unsigned_to_nat(32u);
v___x_268_ = lean_mk_empty_array_with_capacity(v___x_267_);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8(void){
_start:
{
size_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_270_ = ((size_t)5ULL);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_unsigned_to_nat(32u);
v___x_273_ = lean_mk_empty_array_with_capacity(v___x_272_);
v___x_274_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__7);
v___x_275_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
lean_ctor_set(v___x_275_, 2, v___x_271_);
lean_ctor_set(v___x_275_, 3, v___x_271_);
lean_ctor_set_usize(v___x_275_, 4, v___x_270_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
lean_ctor_set(v___x_277_, 3, v___x_276_);
lean_ctor_set(v___x_277_, 4, v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = l_Lean_Options_empty;
v___x_279_ = l_Lean_Core_getMaxHeartbeats(v___x_278_);
return v___x_279_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11(void){
_start:
{
lean_object* v___x_280_; uint16_t v___x_281_; 
v___x_280_ = l_Lean_Options_empty;
v___x_281_ = l_Lean_OptionFlags_ofOptions(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = l_Lean_firstFrontendMacroScope;
v___x_284_ = lean_nat_add(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17(void){
_start:
{
lean_object* v___x_295_; uint64_t v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_296_ = 0ULL;
v___x_297_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set_uint64(v___x_297_, sizeof(void*)*1, v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = l_Lean_Options_empty;
v___x_302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_303_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_301_);
lean_ctor_set(v___x_303_, 2, v___x_302_);
lean_ctor_set(v___x_303_, 3, v___x_300_);
lean_ctor_set(v___x_303_, 4, v___x_300_);
lean_ctor_set(v___x_303_, 5, v___x_300_);
return v___x_303_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = l_Lean_NameSet_empty;
v___x_305_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
lean_ctor_set(v___x_306_, 2, v___x_304_);
return v___x_306_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_308_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_309_ = 1;
v___x_310_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
lean_ctor_set(v___x_310_, 2, v___x_307_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*3, v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_maxRecDepth;
v___x_315_ = l_Lean_Options_empty;
v___x_316_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26(void){
_start:
{
uint16_t v___x_317_; uint16_t v___x_318_; uint16_t v___x_319_; 
v___x_317_ = 512;
v___x_318_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_319_ = lean_uint16_land(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static uint8_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27(void){
_start:
{
uint16_t v___x_320_; uint16_t v___x_321_; uint8_t v___x_322_; 
v___x_320_ = 0;
v___x_321_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26);
v___x_322_ = lean_uint16_dec_eq(v___x_321_, v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object* v_env_323_, lean_object* v_mctx_324_, lean_object* v_lctx_325_, lean_object* v_opts_326_, lean_object* v_namingCtx_327_, lean_object* v_x_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_fileName_344_; lean_object* v_fileMap_345_; lean_object* v_ref_346_; lean_object* v_cancelTk_x3f_347_; lean_object* v_a_349_; lean_object* v_a_356_; lean_object* v_currNamespace_358_; lean_object* v_openDecls_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint16_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint16_t v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint16_t v___y_481_; uint8_t v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v_fileName_521_; lean_object* v_fileMap_522_; lean_object* v_currNamespace_523_; lean_object* v_openDecls_524_; lean_object* v_initHeartbeats_525_; lean_object* v_maxHeartbeats_526_; lean_object* v_quotContext_527_; lean_object* v_currMacroScope_528_; lean_object* v_cancelTk_x3f_529_; lean_object* v_inheritedTraceOptions_530_; lean_object* v_currRecDepth_531_; lean_object* v_ref_532_; uint8_t v_suppressElabErrors_533_; uint8_t v_isRecordingDeps_534_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___y_543_; lean_object* v_env_564_; uint8_t v___x_565_; uint8_t v___x_566_; 
v___x_332_ = lean_box(1);
v___x_333_ = 0;
v___x_334_ = l_Lean_Environment_setExporting(v_env_323_, v___x_333_);
v___x_335_ = 1;
v___x_336_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_340_, 0, v___x_336_);
lean_ctor_set(v___x_340_, 1, v___x_332_);
lean_ctor_set(v___x_340_, 2, v_lctx_325_);
lean_ctor_set(v___x_340_, 3, v___x_338_);
lean_ctor_set(v___x_340_, 4, v___x_339_);
lean_ctor_set(v___x_340_, 5, v___x_337_);
lean_ctor_set(v___x_340_, 6, v___x_339_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*7, v___x_333_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*7 + 1, v___x_333_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*7 + 2, v___x_333_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*7 + 3, v___x_335_);
v___x_341_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6);
v___x_342_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_343_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9);
v_fileName_344_ = lean_ctor_get(v_a_329_, 0);
v_fileMap_345_ = lean_ctor_get(v_a_329_, 1);
v_ref_346_ = lean_ctor_get(v_a_329_, 7);
v_cancelTk_x3f_347_ = lean_ctor_get(v_a_329_, 9);
v_currNamespace_358_ = lean_ctor_get(v_namingCtx_327_, 0);
lean_inc(v_currNamespace_358_);
v_openDecls_359_ = lean_ctor_get(v_namingCtx_327_, 1);
lean_inc(v_openDecls_359_);
lean_dec_ref(v_namingCtx_327_);
v___x_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_360_, 0, v_mctx_324_);
lean_ctor_set(v___x_360_, 1, v___x_341_);
lean_ctor_set(v___x_360_, 2, v___x_332_);
lean_ctor_set(v___x_360_, 3, v___x_342_);
lean_ctor_set(v___x_360_, 4, v___x_343_);
v___x_361_ = l_Lean_Options_empty;
v___x_362_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_363_ = lean_box(0);
v___x_364_ = l_Lean_firstFrontendMacroScope;
v___x_365_ = lean_box(0);
v___x_366_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_367_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12);
v___x_368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15));
v___x_369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16));
v___x_370_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17);
v___x_371_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18);
v___x_372_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
v___x_373_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20);
v___x_374_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21);
v___x_375_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_375_, 0, v___x_334_);
lean_ctor_set(v___x_375_, 1, v___x_367_);
lean_ctor_set(v___x_375_, 2, v___x_368_);
lean_ctor_set(v___x_375_, 3, v___x_369_);
lean_ctor_set(v___x_375_, 4, v___x_370_);
lean_ctor_set(v___x_375_, 5, v___x_371_);
lean_ctor_set(v___x_375_, 6, v___x_372_);
lean_ctor_set(v___x_375_, 7, v___x_373_);
lean_ctor_set(v___x_375_, 8, v___x_374_);
lean_ctor_set(v___x_375_, 9, v___x_338_);
v___x_376_ = lean_io_get_num_heartbeats();
v___x_377_ = lean_st_mk_ref(v___x_375_);
v___x_539_ = l_Lean_inheritedTraceOptions;
v___x_540_ = lean_st_ref_get(v___x_539_);
v___x_541_ = lean_st_ref_get(v___x_377_);
v_env_564_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_env_564_);
lean_dec(v___x_541_);
v___x_565_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_564_);
lean_dec_ref(v_env_564_);
v___x_566_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27);
if (v___x_566_ == 0)
{
if (v___x_565_ == 0)
{
v___y_543_ = v___x_335_;
goto v___jp_542_;
}
else
{
v_fileName_521_ = v_fileName_344_;
v_fileMap_522_ = v_fileMap_345_;
v_currNamespace_523_ = v_currNamespace_358_;
v_openDecls_524_ = v_openDecls_359_;
v_initHeartbeats_525_ = v___x_376_;
v_maxHeartbeats_526_ = v___x_362_;
v_quotContext_527_ = v___x_363_;
v_currMacroScope_528_ = v___x_364_;
v_cancelTk_x3f_529_ = v_cancelTk_x3f_347_;
v_inheritedTraceOptions_530_ = v___x_540_;
v_currRecDepth_531_ = v___x_337_;
v_ref_532_ = v___x_365_;
v_suppressElabErrors_533_ = v___x_333_;
v_isRecordingDeps_534_ = v___x_333_;
goto v___jp_520_;
}
}
else
{
if (v___x_565_ == 0)
{
v_fileName_521_ = v_fileName_344_;
v_fileMap_522_ = v_fileMap_345_;
v_currNamespace_523_ = v_currNamespace_358_;
v_openDecls_524_ = v_openDecls_359_;
v_initHeartbeats_525_ = v___x_376_;
v_maxHeartbeats_526_ = v___x_362_;
v_quotContext_527_ = v___x_363_;
v_currMacroScope_528_ = v___x_364_;
v_cancelTk_x3f_529_ = v_cancelTk_x3f_347_;
v_inheritedTraceOptions_530_ = v___x_540_;
v_currRecDepth_531_ = v___x_337_;
v_ref_532_ = v___x_365_;
v_suppressElabErrors_533_ = v___x_333_;
v_isRecordingDeps_534_ = v___x_333_;
goto v___jp_520_;
}
else
{
v___y_543_ = v___x_333_;
goto v___jp_542_;
}
}
v___jp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_350_ = lean_io_error_to_string(v_a_349_);
v___x_351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
v___x_352_ = l_Lean_MessageData_ofFormat(v___x_351_);
lean_inc(v_ref_346_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_ref_346_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
v___jp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = lean_mk_io_user_error(v_a_356_);
v_a_349_ = v___x_357_;
goto v___jp_348_;
}
v___jp_378_:
{
lean_object* v_toCold_384_; lean_object* v_currRecDepth_385_; lean_object* v_ref_386_; uint8_t v_suppressElabErrors_387_; uint8_t v_isRecordingDeps_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_479_; 
v_toCold_384_ = lean_ctor_get(v___y_382_, 0);
v_currRecDepth_385_ = lean_ctor_get(v___y_382_, 1);
v_ref_386_ = lean_ctor_get(v___y_382_, 2);
v_suppressElabErrors_387_ = lean_ctor_get_uint8(v___y_382_, sizeof(void*)*3 + 2);
v_isRecordingDeps_388_ = lean_ctor_get_uint8(v___y_382_, sizeof(void*)*3 + 3);
v_isSharedCheck_479_ = !lean_is_exclusive(v___y_382_);
if (v_isSharedCheck_479_ == 0)
{
v___x_390_ = v___y_382_;
v_isShared_391_ = v_isSharedCheck_479_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_ref_386_);
lean_inc(v_currRecDepth_385_);
lean_inc(v_toCold_384_);
lean_dec(v___y_382_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_479_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_fileName_392_; lean_object* v_fileMap_393_; lean_object* v_currNamespace_394_; lean_object* v_openDecls_395_; lean_object* v_initHeartbeats_396_; lean_object* v_maxHeartbeats_397_; lean_object* v_quotContext_398_; lean_object* v_currMacroScope_399_; lean_object* v_cancelTk_x3f_400_; lean_object* v_inheritedTraceOptions_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_476_; 
v_fileName_392_ = lean_ctor_get(v_toCold_384_, 0);
v_fileMap_393_ = lean_ctor_get(v_toCold_384_, 1);
v_currNamespace_394_ = lean_ctor_get(v_toCold_384_, 4);
v_openDecls_395_ = lean_ctor_get(v_toCold_384_, 5);
v_initHeartbeats_396_ = lean_ctor_get(v_toCold_384_, 6);
v_maxHeartbeats_397_ = lean_ctor_get(v_toCold_384_, 7);
v_quotContext_398_ = lean_ctor_get(v_toCold_384_, 8);
v_currMacroScope_399_ = lean_ctor_get(v_toCold_384_, 9);
v_cancelTk_x3f_400_ = lean_ctor_get(v_toCold_384_, 10);
v_inheritedTraceOptions_401_ = lean_ctor_get(v_toCold_384_, 11);
v_isSharedCheck_476_ = !lean_is_exclusive(v_toCold_384_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_477_ = lean_ctor_get(v_toCold_384_, 3);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_toCold_384_, 2);
lean_dec(v_unused_478_);
v___x_403_ = v_toCold_384_;
v_isShared_404_ = v_isSharedCheck_476_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_inheritedTraceOptions_401_);
lean_inc(v_cancelTk_x3f_400_);
lean_inc(v_currMacroScope_399_);
lean_inc(v_quotContext_398_);
lean_inc(v_maxHeartbeats_397_);
lean_inc(v_initHeartbeats_396_);
lean_inc(v_openDecls_395_);
lean_inc(v_currNamespace_394_);
lean_inc(v_fileMap_393_);
lean_inc(v_fileName_392_);
lean_dec(v_toCold_384_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_476_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v___y_381_, v___y_380_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 3, v___x_405_);
lean_ctor_set(v___x_403_, 2, v___y_381_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_fileName_392_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_fileMap_393_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v___y_381_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v_currNamespace_394_);
lean_ctor_set(v_reuseFailAlloc_475_, 5, v_openDecls_395_);
lean_ctor_set(v_reuseFailAlloc_475_, 6, v_initHeartbeats_396_);
lean_ctor_set(v_reuseFailAlloc_475_, 7, v_maxHeartbeats_397_);
lean_ctor_set(v_reuseFailAlloc_475_, 8, v_quotContext_398_);
lean_ctor_set(v_reuseFailAlloc_475_, 9, v_currMacroScope_399_);
lean_ctor_set(v_reuseFailAlloc_475_, 10, v_cancelTk_x3f_400_);
lean_ctor_set(v_reuseFailAlloc_475_, 11, v_inheritedTraceOptions_401_);
v___x_407_ = v_reuseFailAlloc_475_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_409_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_407_);
v___x_409_ = v___x_390_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_currRecDepth_385_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_ref_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*3 + 2, v_suppressElabErrors_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*3 + 3, v_isRecordingDeps_388_);
v___x_409_ = v_reuseFailAlloc_474_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_ctor_set_uint16(v___x_409_, sizeof(void*)*3, v___y_379_);
v___x_410_ = lean_st_mk_ref(v___x_360_);
lean_inc(v___x_410_);
v___x_411_ = lean_apply_5(v_x_328_, v___x_340_, v___x_410_, v___x_409_, v___y_383_, lean_box(0));
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_458_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_458_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_458_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_458_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_traceState_419_; lean_object* v_traceState_420_; lean_object* v_env_421_; lean_object* v_messages_422_; lean_object* v_scopes_423_; lean_object* v_usedQuotCtxts_424_; lean_object* v_nextMacroScope_425_; lean_object* v_maxRecDepth_426_; lean_object* v_ngen_427_; lean_object* v_auxDeclNGen_428_; lean_object* v_infoState_429_; lean_object* v_snapshotTasks_430_; lean_object* v_prevLinterStates_431_; lean_object* v_codeQualityEntryTasks_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_456_; 
v___x_416_ = lean_st_ref_get(v___x_410_);
lean_dec(v___x_410_);
lean_dec(v___x_416_);
v___x_417_ = lean_st_ref_get(v___x_377_);
lean_dec(v___x_377_);
v___x_418_ = lean_st_ref_take(v_a_330_);
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
v_codeQualityEntryTasks_432_ = lean_ctor_get(v___x_418_, 12);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_418_, 9);
lean_dec(v_unused_457_);
v___x_434_ = v___x_418_;
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_codeQualityEntryTasks_432_);
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
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_messages_436_; uint64_t v_tid_437_; lean_object* v_traces_438_; lean_object* v_traces_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_455_; 
v_messages_436_ = lean_ctor_get(v___x_417_, 7);
lean_inc_ref(v_messages_436_);
lean_dec(v___x_417_);
v_tid_437_ = lean_ctor_get_uint64(v_traceState_419_, sizeof(void*)*1);
v_traces_438_ = lean_ctor_get(v_traceState_419_, 0);
lean_inc_ref(v_traces_438_);
lean_dec_ref(v_traceState_419_);
v_traces_439_ = lean_ctor_get(v_traceState_420_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_traceState_420_);
if (v_isSharedCheck_455_ == 0)
{
v___x_441_ = v_traceState_420_;
v_isShared_442_ = v_isSharedCheck_455_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_traces_439_);
lean_dec(v_traceState_420_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_455_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = l_Lean_MessageLog_append(v_messages_422_, v_messages_436_);
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
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_env_421_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_scopes_423_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_usedQuotCtxts_424_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_nextMacroScope_425_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v_maxRecDepth_426_);
lean_ctor_set(v_reuseFailAlloc_453_, 6, v_ngen_427_);
lean_ctor_set(v_reuseFailAlloc_453_, 7, v_auxDeclNGen_428_);
lean_ctor_set(v_reuseFailAlloc_453_, 8, v_infoState_429_);
lean_ctor_set(v_reuseFailAlloc_453_, 9, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_453_, 10, v_snapshotTasks_430_);
lean_ctor_set(v_reuseFailAlloc_453_, 11, v_prevLinterStates_431_);
lean_ctor_set(v_reuseFailAlloc_453_, 12, v_codeQualityEntryTasks_432_);
v___x_448_ = v_reuseFailAlloc_453_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_st_ref_put(v_a_330_, v___x_448_);
if (v_isShared_415_ == 0)
{
v___x_451_ = v___x_414_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_412_);
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
lean_dec(v___x_410_);
lean_dec(v___x_377_);
v_a_459_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_411_, 1);
if (lean_obj_tag(v_a_459_) == 0)
{
lean_object* v_msg_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_msg_460_ = lean_ctor_get(v_a_459_, 1);
lean_inc_ref(v_msg_460_);
lean_dec_ref_known(v_a_459_, 2);
v___x_461_ = l_Lean_MessageData_toString(v_msg_460_);
v___x_462_ = lean_mk_io_user_error(v___x_461_);
v_a_349_ = v___x_462_;
goto v___jp_348_;
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
v___x_466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_467_ = l_Lean_Name_toString(v_a_465_, v___x_335_);
v___x_468_ = lean_string_append(v___x_466_, v___x_467_);
lean_dec_ref(v___x_467_);
v_a_356_ = v___x_468_;
goto v___jp_355_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref_known(v___x_464_, 1);
v___x_469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23));
v___x_470_ = l_Nat_reprFast(v_id_463_);
v___x_471_ = lean_string_append(v___x_469_, v___x_470_);
lean_dec_ref(v___x_470_);
v___x_472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24));
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
v_a_356_ = v___x_473_;
goto v___jp_355_;
}
}
}
}
}
}
}
}
v___jp_480_:
{
lean_object* v___x_487_; lean_object* v_env_488_; lean_object* v_nextMacroScope_489_; lean_object* v_ngen_490_; lean_object* v_auxDeclNGen_491_; lean_object* v_traceState_492_; lean_object* v_recordedDeps_493_; lean_object* v_messages_494_; lean_object* v_infoState_495_; lean_object* v_snapshotTasks_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
v___x_487_ = lean_st_ref_take(v___y_486_);
v_env_488_ = lean_ctor_get(v___x_487_, 0);
v_nextMacroScope_489_ = lean_ctor_get(v___x_487_, 1);
v_ngen_490_ = lean_ctor_get(v___x_487_, 2);
v_auxDeclNGen_491_ = lean_ctor_get(v___x_487_, 3);
v_traceState_492_ = lean_ctor_get(v___x_487_, 4);
v_recordedDeps_493_ = lean_ctor_get(v___x_487_, 6);
v_messages_494_ = lean_ctor_get(v___x_487_, 7);
v_infoState_495_ = lean_ctor_get(v___x_487_, 8);
v_snapshotTasks_496_ = lean_ctor_get(v___x_487_, 9);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_487_, 5);
lean_dec(v_unused_506_);
v___x_498_ = v___x_487_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_snapshotTasks_496_);
lean_inc(v_infoState_495_);
lean_inc(v_messages_494_);
lean_inc(v_recordedDeps_493_);
lean_inc(v_traceState_492_);
lean_inc(v_auxDeclNGen_491_);
lean_inc(v_ngen_490_);
lean_inc(v_nextMacroScope_489_);
lean_inc(v_env_488_);
lean_dec(v___x_487_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = l_Lean_Kernel_enableDiag(v_env_488_, v___y_482_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 5, v___x_371_);
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_nextMacroScope_489_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_ngen_490_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_auxDeclNGen_491_);
lean_ctor_set(v_reuseFailAlloc_504_, 4, v_traceState_492_);
lean_ctor_set(v_reuseFailAlloc_504_, 5, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_504_, 6, v_recordedDeps_493_);
lean_ctor_set(v_reuseFailAlloc_504_, 7, v_messages_494_);
lean_ctor_set(v_reuseFailAlloc_504_, 8, v_infoState_495_);
lean_ctor_set(v_reuseFailAlloc_504_, 9, v_snapshotTasks_496_);
v___x_502_ = v_reuseFailAlloc_504_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = lean_st_ref_put(v___y_486_, v___x_502_);
v___y_379_ = v___y_481_;
v___y_380_ = v___y_483_;
v___y_381_ = v___y_484_;
v___y_382_ = v___y_485_;
v___y_383_ = v___y_486_;
goto v___jp_378_;
}
}
}
v___jp_507_:
{
uint16_t v___x_512_; lean_object* v___x_513_; lean_object* v_env_514_; uint8_t v___x_515_; uint16_t v___x_516_; uint16_t v___x_517_; uint16_t v___x_518_; uint8_t v___x_519_; 
v___x_512_ = l_Lean_OptionFlags_ofOptions(v___y_511_);
v___x_513_ = lean_st_ref_get(v___y_510_);
v_env_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_ref(v_env_514_);
lean_dec(v___x_513_);
v___x_515_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_514_);
lean_dec_ref(v_env_514_);
v___x_516_ = 512;
v___x_517_ = lean_uint16_land(v___x_512_, v___x_516_);
v___x_518_ = 0;
v___x_519_ = lean_uint16_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
if (v___x_515_ == 0)
{
v___y_481_ = v___x_512_;
v___y_482_ = v___x_335_;
v___y_483_ = v___y_508_;
v___y_484_ = v___y_511_;
v___y_485_ = v___y_509_;
v___y_486_ = v___y_510_;
goto v___jp_480_;
}
else
{
v___y_379_ = v___x_512_;
v___y_380_ = v___y_508_;
v___y_381_ = v___y_511_;
v___y_382_ = v___y_509_;
v___y_383_ = v___y_510_;
goto v___jp_378_;
}
}
else
{
if (v___x_515_ == 0)
{
v___y_379_ = v___x_512_;
v___y_380_ = v___y_508_;
v___y_381_ = v___y_511_;
v___y_382_ = v___y_509_;
v___y_383_ = v___y_510_;
goto v___jp_378_;
}
else
{
v___y_481_ = v___x_512_;
v___y_482_ = v___x_333_;
v___y_483_ = v___y_508_;
v___y_484_ = v___y_511_;
v___y_485_ = v___y_509_;
v___y_486_ = v___y_510_;
goto v___jp_480_;
}
}
}
v___jp_520_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_535_ = l_Lean_maxRecDepth;
v___x_536_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25);
lean_inc(v_cancelTk_x3f_529_);
lean_inc(v_currMacroScope_528_);
lean_inc(v_quotContext_527_);
lean_inc(v_maxHeartbeats_526_);
lean_inc_ref(v_fileMap_522_);
lean_inc_ref(v_fileName_521_);
v___x_537_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_537_, 0, v_fileName_521_);
lean_ctor_set(v___x_537_, 1, v_fileMap_522_);
lean_ctor_set(v___x_537_, 2, v___x_361_);
lean_ctor_set(v___x_537_, 3, v___x_536_);
lean_ctor_set(v___x_537_, 4, v_currNamespace_523_);
lean_ctor_set(v___x_537_, 5, v_openDecls_524_);
lean_ctor_set(v___x_537_, 6, v_initHeartbeats_525_);
lean_ctor_set(v___x_537_, 7, v_maxHeartbeats_526_);
lean_ctor_set(v___x_537_, 8, v_quotContext_527_);
lean_ctor_set(v___x_537_, 9, v_currMacroScope_528_);
lean_ctor_set(v___x_537_, 10, v_cancelTk_x3f_529_);
lean_ctor_set(v___x_537_, 11, v_inheritedTraceOptions_530_);
lean_inc(v_ref_532_);
v___x_538_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_currRecDepth_531_);
lean_ctor_set(v___x_538_, 2, v_ref_532_);
lean_ctor_set_uint16(v___x_538_, sizeof(void*)*3, v___x_366_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*3 + 2, v_suppressElabErrors_533_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*3 + 3, v_isRecordingDeps_534_);
lean_inc(v___x_377_);
v___y_508_ = v___x_535_;
v___y_509_ = v___x_538_;
v___y_510_ = v___x_377_;
v___y_511_ = v_opts_326_;
goto v___jp_507_;
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v_env_545_; lean_object* v_nextMacroScope_546_; lean_object* v_ngen_547_; lean_object* v_auxDeclNGen_548_; lean_object* v_traceState_549_; lean_object* v_recordedDeps_550_; lean_object* v_messages_551_; lean_object* v_infoState_552_; lean_object* v_snapshotTasks_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_562_; 
v___x_544_ = lean_st_ref_take(v___x_377_);
v_env_545_ = lean_ctor_get(v___x_544_, 0);
v_nextMacroScope_546_ = lean_ctor_get(v___x_544_, 1);
v_ngen_547_ = lean_ctor_get(v___x_544_, 2);
v_auxDeclNGen_548_ = lean_ctor_get(v___x_544_, 3);
v_traceState_549_ = lean_ctor_get(v___x_544_, 4);
v_recordedDeps_550_ = lean_ctor_get(v___x_544_, 6);
v_messages_551_ = lean_ctor_get(v___x_544_, 7);
v_infoState_552_ = lean_ctor_get(v___x_544_, 8);
v_snapshotTasks_553_ = lean_ctor_get(v___x_544_, 9);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v___x_544_, 5);
lean_dec(v_unused_563_);
v___x_555_ = v___x_544_;
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_snapshotTasks_553_);
lean_inc(v_infoState_552_);
lean_inc(v_messages_551_);
lean_inc(v_recordedDeps_550_);
lean_inc(v_traceState_549_);
lean_inc(v_auxDeclNGen_548_);
lean_inc(v_ngen_547_);
lean_inc(v_nextMacroScope_546_);
lean_inc(v_env_545_);
lean_dec(v___x_544_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_Lean_Kernel_enableDiag(v_env_545_, v___y_543_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 5, v___x_371_);
lean_ctor_set(v___x_555_, 0, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_nextMacroScope_546_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_ngen_547_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_auxDeclNGen_548_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_traceState_549_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_recordedDeps_550_);
lean_ctor_set(v_reuseFailAlloc_561_, 7, v_messages_551_);
lean_ctor_set(v_reuseFailAlloc_561_, 8, v_infoState_552_);
lean_ctor_set(v_reuseFailAlloc_561_, 9, v_snapshotTasks_553_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_st_ref_put(v___x_377_, v___x_559_);
v_fileName_521_ = v_fileName_344_;
v_fileMap_522_ = v_fileMap_345_;
v_currNamespace_523_ = v_currNamespace_358_;
v_openDecls_524_ = v_openDecls_359_;
v_initHeartbeats_525_ = v___x_376_;
v_maxHeartbeats_526_ = v___x_362_;
v_quotContext_527_ = v___x_363_;
v_currMacroScope_528_ = v___x_364_;
v_cancelTk_x3f_529_ = v_cancelTk_x3f_347_;
v_inheritedTraceOptions_530_ = v___x_540_;
v_currRecDepth_531_ = v___x_337_;
v_ref_532_ = v___x_365_;
v_suppressElabErrors_533_ = v___x_333_;
v_isRecordingDeps_534_ = v___x_333_;
goto v___jp_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_567_, lean_object* v_mctx_568_, lean_object* v_lctx_569_, lean_object* v_opts_570_, lean_object* v_namingCtx_571_, lean_object* v_x_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_567_, v_mctx_568_, v_lctx_569_, v_opts_570_, v_namingCtx_571_, v_x_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_577_, lean_object* v_env_578_, lean_object* v_mctx_579_, lean_object* v_lctx_580_, lean_object* v_opts_581_, lean_object* v_namingCtx_582_, lean_object* v_x_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_578_, v_mctx_579_, v_lctx_580_, v_opts_581_, v_namingCtx_582_, v_x_583_, v_a_584_, v_a_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_588_, lean_object* v_env_589_, lean_object* v_mctx_590_, lean_object* v_lctx_591_, lean_object* v_opts_592_, lean_object* v_namingCtx_593_, lean_object* v_x_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_588_, v_env_589_, v_mctx_590_, v_lctx_591_, v_opts_592_, v_namingCtx_593_, v_x_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
return v_res_598_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Syntax_getKind(v_stx_602_);
if (lean_obj_tag(v___x_603_) == 1)
{
lean_object* v_pre_604_; 
v_pre_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_pre_604_);
if (lean_obj_tag(v_pre_604_) == 1)
{
lean_object* v_pre_605_; 
v_pre_605_ = lean_ctor_get(v_pre_604_, 0);
lean_inc(v_pre_605_);
if (lean_obj_tag(v_pre_605_) == 1)
{
lean_object* v_pre_606_; 
v_pre_606_ = lean_ctor_get(v_pre_605_, 0);
lean_inc(v_pre_606_);
if (lean_obj_tag(v_pre_606_) == 1)
{
lean_object* v_pre_607_; 
v_pre_607_ = lean_ctor_get(v_pre_606_, 0);
if (lean_obj_tag(v_pre_607_) == 0)
{
lean_object* v_str_608_; lean_object* v_str_609_; lean_object* v_str_610_; lean_object* v_str_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_str_608_ = lean_ctor_get(v___x_603_, 1);
lean_inc_ref(v_str_608_);
lean_dec_ref_known(v___x_603_, 2);
v_str_609_ = lean_ctor_get(v_pre_604_, 1);
lean_inc_ref(v_str_609_);
lean_dec_ref_known(v_pre_604_, 2);
v_str_610_ = lean_ctor_get(v_pre_605_, 1);
lean_inc_ref(v_str_610_);
lean_dec_ref_known(v_pre_605_, 2);
v_str_611_ = lean_ctor_get(v_pre_606_, 1);
lean_inc_ref(v_str_611_);
lean_dec_ref_known(v_pre_606_, 2);
v___x_612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_613_ = lean_string_dec_eq(v_str_611_, v___x_612_);
lean_dec_ref(v_str_611_);
if (v___x_613_ == 0)
{
lean_dec_ref(v_str_610_);
lean_dec_ref(v_str_609_);
lean_dec_ref(v_str_608_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_615_ = lean_string_dec_eq(v_str_610_, v___x_614_);
lean_dec_ref(v_str_610_);
if (v___x_615_ == 0)
{
lean_dec_ref(v_str_609_);
lean_dec_ref(v_str_608_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_617_ = lean_string_dec_eq(v_str_609_, v___x_616_);
lean_dec_ref(v_str_609_);
if (v___x_617_ == 0)
{
lean_dec_ref(v_str_608_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_619_ = lean_string_dec_eq(v_str_608_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_621_ = lean_string_dec_eq(v_str_608_, v___x_620_);
lean_dec_ref(v_str_608_);
return v___x_621_;
}
else
{
lean_dec_ref(v_str_608_);
return v___x_619_;
}
}
}
}
}
else
{
uint8_t v___x_622_; 
lean_dec_ref_known(v_pre_606_, 2);
lean_dec_ref_known(v_pre_605_, 2);
lean_dec_ref_known(v_pre_604_, 2);
lean_dec_ref_known(v___x_603_, 2);
v___x_622_ = 0;
return v___x_622_;
}
}
else
{
uint8_t v___x_623_; 
lean_dec(v_pre_606_);
lean_dec_ref_known(v_pre_605_, 2);
lean_dec_ref_known(v_pre_604_, 2);
lean_dec_ref_known(v___x_603_, 2);
v___x_623_ = 0;
return v___x_623_;
}
}
else
{
uint8_t v___x_624_; 
lean_dec_ref_known(v_pre_604_, 2);
lean_dec(v_pre_605_);
lean_dec_ref_known(v___x_603_, 2);
v___x_624_ = 0;
return v___x_624_;
}
}
else
{
uint8_t v___x_625_; 
lean_dec_ref_known(v___x_603_, 2);
lean_dec(v_pre_604_);
v___x_625_ = 0;
return v___x_625_;
}
}
else
{
uint8_t v___x_626_; 
lean_dec(v___x_603_);
v___x_626_ = 0;
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_627_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(lean_object* v_x_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_obj_tag_nat(v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl___boxed(lean_object* v_x_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(v_x_632_);
lean_dec(v_x_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_634_, lean_object* v_k_635_){
_start:
{
if (lean_obj_tag(v_t_634_) == 0)
{
lean_object* v_tacticSeq_636_; lean_object* v_insertPos_637_; lean_object* v___x_638_; 
v_tacticSeq_636_ = lean_ctor_get(v_t_634_, 0);
lean_inc(v_tacticSeq_636_);
v_insertPos_637_ = lean_ctor_get(v_t_634_, 1);
lean_inc(v_insertPos_637_);
lean_dec_ref_known(v_t_634_, 2);
v___x_638_ = lean_apply_2(v_k_635_, v_tacticSeq_636_, v_insertPos_637_);
return v___x_638_;
}
else
{
return v_k_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_639_, lean_object* v_ctorIdx_640_, lean_object* v_t_641_, lean_object* v_h_642_, lean_object* v_k_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_641_, v_k_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_645_, lean_object* v_ctorIdx_646_, lean_object* v_t_647_, lean_object* v_h_648_, lean_object* v_k_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_645_, v_ctorIdx_646_, v_t_647_, v_h_648_, v_k_649_);
lean_dec(v_ctorIdx_646_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_651_, lean_object* v_unsolvedGoal_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_651_, v_unsolvedGoal_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_654_, lean_object* v_t_655_, lean_object* v_h_656_, lean_object* v_unsolvedGoal_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_655_, v_unsolvedGoal_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_659_, lean_object* v_sorryTactic_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_659_, v_sorryTactic_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_662_, lean_object* v_t_663_, lean_object* v_h_664_, lean_object* v_sorryTactic_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_663_, v_sorryTactic_665_);
return v___x_666_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_670_; lean_object* v___x_671_; 
v___x_670_ = 32;
v___x_671_ = lean_box_uint32(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_672_, lean_object* v_fileMap_673_){
_start:
{
uint8_t v___x_674_; lean_object* v___x_675_; 
v___x_674_ = 0;
v___x_675_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_672_, v___x_674_);
if (lean_obj_tag(v___x_675_) == 1)
{
lean_object* v_val_676_; lean_object* v___x_677_; 
v_val_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_672_, v___x_674_);
if (lean_obj_tag(v___x_677_) == 1)
{
lean_object* v_val_678_; lean_object* v_startPos_679_; lean_object* v_line_680_; lean_object* v_column_681_; lean_object* v_endPos_682_; lean_object* v_line_683_; uint8_t v___x_684_; 
v_val_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v___x_677_, 1);
lean_inc_ref(v_fileMap_673_);
v_startPos_679_ = l_Lean_FileMap_toPosition(v_fileMap_673_, v_val_676_);
lean_dec(v_val_676_);
v_line_680_ = lean_ctor_get(v_startPos_679_, 0);
lean_inc(v_line_680_);
v_column_681_ = lean_ctor_get(v_startPos_679_, 1);
lean_inc(v_column_681_);
lean_dec_ref(v_startPos_679_);
v_endPos_682_ = l_Lean_FileMap_toPosition(v_fileMap_673_, v_val_678_);
lean_dec(v_val_678_);
v_line_683_ = lean_ctor_get(v_endPos_682_, 0);
lean_inc(v_line_683_);
lean_dec_ref(v_endPos_682_);
v___x_684_ = lean_nat_dec_eq(v_line_680_, v_line_683_);
lean_dec(v_line_683_);
lean_dec(v_line_680_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_686_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_687_ = l_List_replicateTR___redArg(v_column_681_, v___x_686_);
v___x_688_ = lean_string_mk(v___x_687_);
v___x_689_ = lean_string_append(v___x_685_, v___x_688_);
lean_dec_ref(v___x_688_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; 
lean_dec(v_column_681_);
v___x_690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_690_;
}
}
else
{
lean_object* v___x_691_; 
lean_dec(v___x_677_);
lean_dec(v_val_676_);
lean_dec_ref(v_fileMap_673_);
v___x_691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_691_;
}
}
else
{
lean_object* v___x_692_; 
lean_dec(v___x_675_);
lean_dec_ref(v_fileMap_673_);
v___x_692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_693_, lean_object* v_fileMap_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_693_, v_fileMap_694_);
lean_dec(v_tacticSeq_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
lean_inc(v_p_700_);
v___x_703_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v_p_700_);
lean_ctor_set(v___x_703_, 2, v___x_702_);
lean_ctor_set(v___x_703_, 3, v_p_700_);
v___x_704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_701_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_start_708_; lean_object* v_stop_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v___x_706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
v_start_708_ = lean_ctor_get(v_range_705_, 0);
v_stop_709_ = lean_ctor_get(v_range_705_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_range_705_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v_range_705_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_stop_709_);
lean_inc(v_start_708_);
lean_dec(v_range_705_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_713_, 0, v___x_707_);
lean_ctor_set(v___x_713_, 1, v_start_708_);
lean_ctor_set(v___x_713_, 2, v___x_707_);
lean_ctor_set(v___x_713_, 3, v_stop_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 2);
lean_ctor_set(v___x_711_, 1, v___x_706_);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_706_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_718_, lean_object* v_nc_x3f_719_, lean_object* v_msg_720_, lean_object* v_acc_721_){
_start:
{
switch(lean_obj_tag(v_msg_720_))
{
case 3:
{
lean_object* v_a_722_; lean_object* v_a_723_; lean_object* v___x_724_; 
lean_dec(v_mc_x3f_718_);
v_a_722_ = lean_ctor_get(v_msg_720_, 0);
v_a_723_ = lean_ctor_get(v_msg_720_, 1);
lean_inc_ref(v_a_722_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_a_722_);
v_mc_x3f_718_ = v___x_724_;
v_msg_720_ = v_a_723_;
goto _start;
}
case 4:
{
lean_object* v_a_726_; lean_object* v_a_727_; lean_object* v___x_728_; 
lean_dec(v_nc_x3f_719_);
v_a_726_ = lean_ctor_get(v_msg_720_, 0);
v_a_727_ = lean_ctor_get(v_msg_720_, 1);
lean_inc_ref(v_a_726_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_a_726_);
v_nc_x3f_719_ = v___x_728_;
v_msg_720_ = v_a_727_;
goto _start;
}
case 5:
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v_msg_720_, 1);
v_msg_720_ = v_a_730_;
goto _start;
}
case 6:
{
lean_object* v_a_732_; 
v_a_732_ = lean_ctor_get(v_msg_720_, 0);
v_msg_720_ = v_a_732_;
goto _start;
}
case 8:
{
lean_object* v_a_734_; 
v_a_734_ = lean_ctor_get(v_msg_720_, 1);
v_msg_720_ = v_a_734_;
goto _start;
}
case 7:
{
lean_object* v_a_736_; lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_736_ = lean_ctor_get(v_msg_720_, 0);
v_a_737_ = lean_ctor_get(v_msg_720_, 1);
lean_inc(v_nc_x3f_719_);
lean_inc(v_mc_x3f_718_);
v___x_738_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_718_, v_nc_x3f_719_, v_a_736_, v_acc_721_);
v_msg_720_ = v_a_737_;
v_acc_721_ = v___x_738_;
goto _start;
}
case 2:
{
lean_object* v_a_740_; 
v_a_740_ = lean_ctor_get(v_msg_720_, 1);
v_msg_720_ = v_a_740_;
goto _start;
}
case 9:
{
lean_object* v_msg_742_; lean_object* v_children_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_msg_742_ = lean_ctor_get(v_msg_720_, 1);
v_children_743_ = lean_ctor_get(v_msg_720_, 2);
lean_inc(v_nc_x3f_719_);
lean_inc(v_mc_x3f_718_);
v___x_744_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_718_, v_nc_x3f_719_, v_msg_742_, v_acc_721_);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_array_get_size(v_children_743_);
v___x_747_ = lean_nat_dec_lt(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_dec(v_nc_x3f_719_);
lean_dec(v_mc_x3f_718_);
return v___x_744_;
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_746_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_718_, v_nc_x3f_719_, v_children_743_, v___x_748_, v___x_749_, v___x_744_);
return v___x_750_;
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_718_) == 1)
{
if (lean_obj_tag(v_nc_x3f_719_) == 1)
{
lean_object* v_a_751_; lean_object* v_val_752_; lean_object* v_val_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_a_751_ = lean_ctor_get(v_msg_720_, 0);
v_val_752_ = lean_ctor_get(v_mc_x3f_718_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v_mc_x3f_718_, 1);
v_val_753_ = lean_ctor_get(v_nc_x3f_719_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_nc_x3f_719_, 1);
lean_inc(v_a_751_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_val_753_);
lean_ctor_set(v___x_754_, 1, v_a_751_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_val_752_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = lean_array_push(v_acc_721_, v___x_755_);
return v___x_756_;
}
else
{
lean_dec_ref_known(v_mc_x3f_718_, 1);
lean_dec(v_nc_x3f_719_);
return v_acc_721_;
}
}
else
{
lean_dec(v_nc_x3f_719_);
lean_dec(v_mc_x3f_718_);
return v_acc_721_;
}
}
default: 
{
lean_dec(v_nc_x3f_719_);
lean_dec(v_mc_x3f_718_);
return v_acc_721_;
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
lean_dec_ref_known(v_pre_797_, 2);
lean_dec(v_pre_798_);
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
lean_dec_ref_known(v_pre_796_, 2);
lean_dec(v_pre_797_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_opts_925_, lean_object* v_opt_926_){
_start:
{
lean_object* v_name_927_; lean_object* v_defValue_928_; lean_object* v_map_929_; lean_object* v___x_930_; 
v_name_927_ = lean_ctor_get(v_opt_926_, 0);
v_defValue_928_ = lean_ctor_get(v_opt_926_, 1);
v_map_929_ = lean_ctor_get(v_opts_925_, 0);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_929_, v_name_927_);
if (lean_obj_tag(v___x_930_) == 0)
{
uint8_t v___x_931_; 
v___x_931_ = lean_unbox(v_defValue_928_);
return v___x_931_;
}
else
{
lean_object* v_val_932_; 
v_val_932_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v___x_930_, 1);
if (lean_obj_tag(v_val_932_) == 1)
{
uint8_t v_v_933_; 
v_v_933_ = lean_ctor_get_uint8(v_val_932_, 0);
lean_dec_ref_known(v_val_932_, 0);
return v_v_933_;
}
else
{
uint8_t v___x_934_; 
lean_dec(v_val_932_);
v___x_934_ = lean_unbox(v_defValue_928_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_opts_935_, lean_object* v_opt_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_935_, v_opt_936_);
lean_dec_ref(v_opt_936_);
lean_dec_ref(v_opts_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_939_, lean_object* v_info_940_, lean_object* v_acc_941_){
_start:
{
if (lean_obj_tag(v_info_940_) == 0)
{
lean_object* v_i_942_; lean_object* v_toElabInfo_943_; lean_object* v_mctxBefore_944_; lean_object* v_goalsBefore_945_; lean_object* v_stx_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_964_; 
v_i_942_ = lean_ctor_get(v_info_940_, 0);
lean_inc_ref(v_i_942_);
lean_dec_ref_known(v_info_940_, 1);
v_toElabInfo_943_ = lean_ctor_get(v_i_942_, 0);
lean_inc_ref(v_toElabInfo_943_);
v_mctxBefore_944_ = lean_ctor_get(v_i_942_, 1);
lean_inc_ref(v_mctxBefore_944_);
v_goalsBefore_945_ = lean_ctor_get(v_i_942_, 2);
lean_inc(v_goalsBefore_945_);
lean_dec_ref(v_i_942_);
v_stx_946_ = lean_ctor_get(v_toElabInfo_943_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_toElabInfo_943_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_toElabInfo_943_, 0);
lean_dec(v_unused_965_);
v___x_948_ = v_toElabInfo_943_;
v_isShared_949_ = v_isSharedCheck_964_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_stx_946_);
lean_dec(v_toElabInfo_943_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_964_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v___x_950_; 
lean_inc(v_stx_946_);
v___x_950_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_946_);
if (v___x_950_ == 0)
{
lean_del_object(v___x_948_);
lean_dec(v_stx_946_);
lean_dec(v_goalsBefore_945_);
lean_dec_ref(v_mctxBefore_944_);
return v_acc_941_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = l_List_head_x3f___redArg(v_goalsBefore_945_);
lean_dec(v_goalsBefore_945_);
if (lean_obj_tag(v___x_951_) == 1)
{
lean_object* v_toCommandContextInfo_952_; lean_object* v_val_953_; lean_object* v_env_954_; lean_object* v_options_955_; lean_object* v_currNamespace_956_; lean_object* v_openDecls_957_; lean_object* v_namingCtx_959_; 
v_toCommandContextInfo_952_ = lean_ctor_get(v_ctx_939_, 0);
v_val_953_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v___x_951_, 1);
v_env_954_ = lean_ctor_get(v_toCommandContextInfo_952_, 0);
v_options_955_ = lean_ctor_get(v_toCommandContextInfo_952_, 4);
v_currNamespace_956_ = lean_ctor_get(v_toCommandContextInfo_952_, 5);
v_openDecls_957_ = lean_ctor_get(v_toCommandContextInfo_952_, 6);
lean_inc(v_openDecls_957_);
lean_inc(v_currNamespace_956_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_openDecls_957_);
lean_ctor_set(v___x_948_, 0, v_currNamespace_956_);
v_namingCtx_959_ = v___x_948_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_currNamespace_956_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_openDecls_957_);
v_namingCtx_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_box(1);
lean_inc_ref(v_options_955_);
lean_inc_ref(v_env_954_);
v___x_961_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v_stx_946_);
lean_ctor_set(v___x_961_, 2, v_env_954_);
lean_ctor_set(v___x_961_, 3, v_mctxBefore_944_);
lean_ctor_set(v___x_961_, 4, v_options_955_);
lean_ctor_set(v___x_961_, 5, v_namingCtx_959_);
lean_ctor_set(v___x_961_, 6, v_val_953_);
v___x_962_ = lean_array_push(v_acc_941_, v___x_961_);
return v___x_962_;
}
}
else
{
lean_dec(v___x_951_);
lean_del_object(v___x_948_);
lean_dec(v_stx_946_);
lean_dec_ref(v_mctxBefore_944_);
return v_acc_941_;
}
}
}
}
else
{
lean_dec_ref(v_info_940_);
return v_acc_941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_966_, lean_object* v_info_967_, lean_object* v_acc_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_966_, v_info_967_, v_acc_968_);
lean_dec_ref(v_ctx_966_);
return v_res_969_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(lean_object* v_x_974_){
_start:
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1));
v___x_976_ = lean_name_eq(v_x_974_, v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___boxed(lean_object* v_x_977_){
_start:
{
uint8_t v_res_978_; lean_object* v_r_979_; 
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(v_x_977_);
lean_dec(v_x_977_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(lean_object* v_a_980_, lean_object* v_x_981_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
uint8_t v___x_982_; 
v___x_982_ = 0;
return v___x_982_;
}
else
{
lean_object* v_key_983_; lean_object* v_tail_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v_fst_987_; lean_object* v_snd_988_; uint8_t v___x_989_; 
v_key_983_ = lean_ctor_get(v_x_981_, 0);
v_tail_984_ = lean_ctor_get(v_x_981_, 2);
v_fst_985_ = lean_ctor_get(v_key_983_, 0);
v_snd_986_ = lean_ctor_get(v_key_983_, 1);
v_fst_987_ = lean_ctor_get(v_a_980_, 0);
v_snd_988_ = lean_ctor_get(v_a_980_, 1);
v___x_989_ = l_Lean_Syntax_instBEqRange_beq(v_fst_985_, v_fst_987_);
if (v___x_989_ == 0)
{
v_x_981_ = v_tail_984_;
goto _start;
}
else
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_instBEqMVarId_beq(v_snd_986_, v_snd_988_);
if (v___x_991_ == 0)
{
v_x_981_ = v_tail_984_;
goto _start;
}
else
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg___boxed(lean_object* v_a_993_, lean_object* v_x_994_){
_start:
{
uint8_t v_res_995_; lean_object* v_r_996_; 
v_res_995_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_993_, v_x_994_);
lean_dec(v_x_994_);
lean_dec_ref(v_a_993_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
if (lean_obj_tag(v_x_998_) == 0)
{
return v_x_997_;
}
else
{
lean_object* v_key_999_; lean_object* v_value_1000_; lean_object* v_tail_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1028_; 
v_key_999_ = lean_ctor_get(v_x_998_, 0);
v_value_1000_ = lean_ctor_get(v_x_998_, 1);
v_tail_1001_ = lean_ctor_get(v_x_998_, 2);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_x_998_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1003_ = v_x_998_;
v_isShared_1004_ = v_isSharedCheck_1028_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_tail_1001_);
lean_inc(v_value_1000_);
lean_inc(v_key_999_);
lean_dec(v_x_998_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1028_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_fst_1005_; lean_object* v_snd_1006_; lean_object* v___x_1007_; uint64_t v___x_1008_; uint64_t v___x_1009_; uint64_t v___x_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; uint64_t v_fold_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; uint64_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v_fst_1005_ = lean_ctor_get(v_key_999_, 0);
v_snd_1006_ = lean_ctor_get(v_key_999_, 1);
v___x_1007_ = lean_array_get_size(v_x_997_);
v___x_1008_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1005_);
v___x_1009_ = l_Lean_instHashableMVarId_hash(v_snd_1006_);
v___x_1010_ = lean_uint64_mix_hash(v___x_1008_, v___x_1009_);
v___x_1011_ = 32ULL;
v___x_1012_ = lean_uint64_shift_right(v___x_1010_, v___x_1011_);
v_fold_1013_ = lean_uint64_xor(v___x_1010_, v___x_1012_);
v___x_1014_ = 16ULL;
v___x_1015_ = lean_uint64_shift_right(v_fold_1013_, v___x_1014_);
v___x_1016_ = lean_uint64_xor(v_fold_1013_, v___x_1015_);
v___x_1017_ = lean_uint64_to_usize(v___x_1016_);
v___x_1018_ = lean_usize_of_nat(v___x_1007_);
v___x_1019_ = ((size_t)1ULL);
v___x_1020_ = lean_usize_sub(v___x_1018_, v___x_1019_);
v___x_1021_ = lean_usize_land(v___x_1017_, v___x_1020_);
v___x_1022_ = lean_array_uget_borrowed(v_x_997_, v___x_1021_);
lean_inc(v___x_1022_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 2, v___x_1022_);
v___x_1024_ = v___x_1003_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_key_999_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_value_1000_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_array_uset(v_x_997_, v___x_1021_, v___x_1024_);
v_x_997_ = v___x_1025_;
v_x_998_ = v_tail_1001_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1029_, lean_object* v_source_1030_, lean_object* v_target_1031_){
_start:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = lean_array_get_size(v_source_1030_);
v___x_1033_ = lean_nat_dec_lt(v_i_1029_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_dec_ref(v_source_1030_);
lean_dec(v_i_1029_);
return v_target_1031_;
}
else
{
lean_object* v_es_1034_; lean_object* v___x_1035_; lean_object* v_source_1036_; lean_object* v_target_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_es_1034_ = lean_array_fget(v_source_1030_, v_i_1029_);
v___x_1035_ = lean_box(0);
v_source_1036_ = lean_array_fset(v_source_1030_, v_i_1029_, v___x_1035_);
v_target_1037_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1031_, v_es_1034_);
v___x_1038_ = lean_unsigned_to_nat(1u);
v___x_1039_ = lean_nat_add(v_i_1029_, v___x_1038_);
lean_dec(v_i_1029_);
v_i_1029_ = v___x_1039_;
v_source_1030_ = v_source_1036_;
v_target_1031_ = v_target_1037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(lean_object* v_data_1041_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_nbuckets_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1042_ = lean_array_get_size(v_data_1041_);
v___x_1043_ = lean_unsigned_to_nat(2u);
v_nbuckets_1044_ = lean_nat_mul(v___x_1042_, v___x_1043_);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_mk_array(v_nbuckets_1044_, v___x_1046_);
v___x_1048_ = lean_array_propagate_mark(v_data_1041_, v___x_1047_);
v___x_1049_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v___x_1045_, v_data_1041_, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v_m_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_){
_start:
{
lean_object* v_size_1053_; lean_object* v_buckets_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; lean_object* v___x_1057_; uint64_t v___x_1058_; uint64_t v___x_1059_; uint64_t v___x_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; uint64_t v_fold_1063_; uint64_t v___x_1064_; uint64_t v___x_1065_; uint64_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v_bkt_1072_; uint8_t v___x_1073_; 
v_size_1053_ = lean_ctor_get(v_m_1050_, 0);
v_buckets_1054_ = lean_ctor_get(v_m_1050_, 1);
v_fst_1055_ = lean_ctor_get(v_a_1051_, 0);
v_snd_1056_ = lean_ctor_get(v_a_1051_, 1);
v___x_1057_ = lean_array_get_size(v_buckets_1054_);
v___x_1058_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1055_);
v___x_1059_ = l_Lean_instHashableMVarId_hash(v_snd_1056_);
v___x_1060_ = lean_uint64_mix_hash(v___x_1058_, v___x_1059_);
v___x_1061_ = 32ULL;
v___x_1062_ = lean_uint64_shift_right(v___x_1060_, v___x_1061_);
v_fold_1063_ = lean_uint64_xor(v___x_1060_, v___x_1062_);
v___x_1064_ = 16ULL;
v___x_1065_ = lean_uint64_shift_right(v_fold_1063_, v___x_1064_);
v___x_1066_ = lean_uint64_xor(v_fold_1063_, v___x_1065_);
v___x_1067_ = lean_uint64_to_usize(v___x_1066_);
v___x_1068_ = lean_usize_of_nat(v___x_1057_);
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_sub(v___x_1068_, v___x_1069_);
v___x_1071_ = lean_usize_land(v___x_1067_, v___x_1070_);
v_bkt_1072_ = lean_array_uget_borrowed(v_buckets_1054_, v___x_1071_);
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1051_, v_bkt_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1094_; 
lean_inc_ref(v_buckets_1054_);
lean_inc(v_size_1053_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_m_1050_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1095_ = lean_ctor_get(v_m_1050_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_m_1050_, 0);
lean_dec(v_unused_1096_);
v___x_1075_ = v_m_1050_;
v_isShared_1076_ = v_isSharedCheck_1094_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v_m_1050_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1094_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v_size_x27_1078_; lean_object* v___x_1079_; lean_object* v_buckets_x27_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1077_ = lean_unsigned_to_nat(1u);
v_size_x27_1078_ = lean_nat_add(v_size_1053_, v___x_1077_);
lean_dec(v_size_1053_);
lean_inc(v_bkt_1072_);
v___x_1079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1079_, 0, v_a_1051_);
lean_ctor_set(v___x_1079_, 1, v_b_1052_);
lean_ctor_set(v___x_1079_, 2, v_bkt_1072_);
v_buckets_x27_1080_ = lean_array_uset(v_buckets_1054_, v___x_1071_, v___x_1079_);
v___x_1081_ = lean_unsigned_to_nat(4u);
v___x_1082_ = lean_nat_mul(v_size_x27_1078_, v___x_1081_);
v___x_1083_ = lean_unsigned_to_nat(3u);
v___x_1084_ = lean_nat_div(v___x_1082_, v___x_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_array_get_size(v_buckets_x27_1080_);
v___x_1086_ = lean_nat_dec_le(v___x_1084_, v___x_1085_);
lean_dec(v___x_1084_);
if (v___x_1086_ == 0)
{
lean_object* v_val_1087_; lean_object* v___x_1089_; 
v_val_1087_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_buckets_x27_1080_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v_val_1087_);
lean_ctor_set(v___x_1075_, 0, v_size_x27_1078_);
v___x_1089_ = v___x_1075_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_size_x27_1078_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_val_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_object* v___x_1092_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v_buckets_x27_1080_);
lean_ctor_set(v___x_1075_, 0, v_size_x27_1078_);
v___x_1092_ = v___x_1075_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_size_x27_1078_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_buckets_x27_1080_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_dec(v_b_1052_);
lean_dec_ref(v_a_1051_);
return v_m_1050_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1097_, lean_object* v_a_1098_){
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
v___x_1118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1098_, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object* v_m_1119_, lean_object* v_a_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1119_, v_a_1120_);
lean_dec_ref(v_a_1120_);
lean_dec_ref(v_m_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object* v___x_1123_, lean_object* v_fst_1124_, lean_object* v_snd_1125_, lean_object* v___x_1126_, lean_object* v_as_1127_, size_t v_sz_1128_, size_t v_i_1129_, lean_object* v_b_1130_){
_start:
{
lean_object* v_a_1133_; uint8_t v___x_1137_; 
v___x_1137_ = lean_usize_dec_lt(v_i_1129_, v_sz_1128_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec(v___x_1126_);
lean_dec(v_snd_1125_);
lean_dec(v_fst_1124_);
lean_dec_ref(v___x_1123_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_b_1130_);
return v___x_1138_;
}
else
{
lean_object* v_a_1139_; lean_object* v_snd_1140_; lean_object* v_fst_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1177_; 
v_a_1139_ = lean_array_uget(v_as_1127_, v_i_1129_);
v_snd_1140_ = lean_ctor_get(v_a_1139_, 1);
v_fst_1141_ = lean_ctor_get(v_a_1139_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_a_1139_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1143_ = v_a_1139_;
v_isShared_1144_ = v_isSharedCheck_1177_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1140_);
lean_inc(v_fst_1141_);
lean_dec(v_a_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1177_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_fst_1145_; lean_object* v_snd_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1176_; 
v_fst_1145_ = lean_ctor_get(v_snd_1140_, 0);
v_snd_1146_ = lean_ctor_get(v_snd_1140_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_snd_1140_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1148_ = v_snd_1140_;
v_isShared_1149_ = v_isSharedCheck_1176_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_snd_1146_);
lean_inc(v_fst_1145_);
lean_dec(v_snd_1140_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1176_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1175_; 
v_fst_1150_ = lean_ctor_get(v_b_1130_, 0);
v_snd_1151_ = lean_ctor_get(v_b_1130_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_b_1130_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1153_ = v_b_1130_;
v_isShared_1154_ = v_isSharedCheck_1175_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snd_1151_);
lean_inc(v_fst_1150_);
lean_dec(v_b_1130_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1175_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
lean_inc(v_snd_1146_);
lean_inc_ref(v___x_1123_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_snd_1146_);
lean_ctor_set(v___x_1153_, 0, v___x_1123_);
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_snd_1146_);
v___x_1156_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
uint8_t v___x_1157_; 
v___x_1157_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1151_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v_env_1158_; lean_object* v_mctx_1159_; lean_object* v_opts_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v_env_1158_ = lean_ctor_get(v_fst_1141_, 0);
lean_inc_ref(v_env_1158_);
v_mctx_1159_ = lean_ctor_get(v_fst_1141_, 1);
lean_inc_ref(v_mctx_1159_);
v_opts_1160_ = lean_ctor_get(v_fst_1141_, 3);
lean_inc_ref(v_opts_1160_);
lean_dec(v_fst_1141_);
v___x_1161_ = lean_box(0);
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1151_, v___x_1156_, v___x_1161_);
lean_inc(v_snd_1125_);
lean_inc(v_fst_1124_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_snd_1125_);
lean_ctor_set(v___x_1143_, 0, v_fst_1124_);
v___x_1164_ = v___x_1143_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_fst_1124_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_snd_1125_);
v___x_1164_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_inc(v___x_1126_);
v___x_1165_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1126_);
lean_ctor_set(v___x_1165_, 2, v_env_1158_);
lean_ctor_set(v___x_1165_, 3, v_mctx_1159_);
lean_ctor_set(v___x_1165_, 4, v_opts_1160_);
lean_ctor_set(v___x_1165_, 5, v_fst_1145_);
lean_ctor_set(v___x_1165_, 6, v_snd_1146_);
v___x_1166_ = lean_array_push(v_fst_1150_, v___x_1165_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1162_);
lean_ctor_set(v___x_1148_, 0, v___x_1166_);
v___x_1168_ = v___x_1148_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1162_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v_a_1133_ = v___x_1168_;
goto v___jp_1132_;
}
}
}
else
{
lean_object* v___x_1172_; 
lean_dec_ref(v___x_1156_);
lean_dec(v_snd_1146_);
lean_dec(v_fst_1145_);
lean_del_object(v___x_1143_);
lean_dec(v_fst_1141_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_snd_1151_);
lean_ctor_set(v___x_1148_, 0, v_fst_1150_);
v___x_1172_ = v___x_1148_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_fst_1150_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_snd_1151_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
v_a_1133_ = v___x_1172_;
goto v___jp_1132_;
}
}
}
}
}
}
}
v___jp_1132_:
{
size_t v___x_1134_; size_t v___x_1135_; 
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_add(v_i_1129_, v___x_1134_);
v_i_1129_ = v___x_1135_;
v_b_1130_ = v_a_1133_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object* v___x_1178_, lean_object* v_fst_1179_, lean_object* v_snd_1180_, lean_object* v___x_1181_, lean_object* v_as_1182_, lean_object* v_sz_1183_, lean_object* v_i_1184_, lean_object* v_b_1185_, lean_object* v___y_1186_){
_start:
{
size_t v_sz_boxed_1187_; size_t v_i_boxed_1188_; lean_object* v_res_1189_; 
v_sz_boxed_1187_ = lean_unbox_usize(v_sz_1183_);
lean_dec(v_sz_1183_);
v_i_boxed_1188_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1178_, v_fst_1179_, v_snd_1180_, v___x_1181_, v_as_1182_, v_sz_boxed_1187_, v_i_boxed_1188_, v_b_1185_);
lean_dec_ref(v_as_1182_);
return v_res_1189_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1192_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1193_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
lean_ctor_set(v___x_1195_, 2, v___x_1194_);
lean_ctor_set(v___x_1195_, 3, v___x_1194_);
lean_ctor_set(v___x_1195_, 4, v___x_1193_);
lean_ctor_set(v___x_1195_, 5, v___x_1193_);
lean_ctor_set(v___x_1195_, 6, v___x_1193_);
lean_ctor_set(v___x_1195_, 7, v___x_1193_);
lean_ctor_set(v___x_1195_, 8, v___x_1193_);
lean_ctor_set(v___x_1195_, 9, v___x_1193_);
lean_ctor_set(v___x_1195_, 10, v___x_1193_);
lean_ctor_set(v___x_1195_, 11, v___x_1192_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_unsigned_to_nat(32u);
v___x_1197_ = lean_mk_empty_array_with_capacity(v___x_1196_);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1199_ = ((size_t)5ULL);
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_unsigned_to_nat(32u);
v___x_1202_ = lean_mk_empty_array_with_capacity(v___x_1201_);
v___x_1203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2);
v___x_1204_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v___x_1202_);
lean_ctor_set(v___x_1204_, 2, v___x_1200_);
lean_ctor_set(v___x_1204_, 3, v___x_1200_);
lean_ctor_set_usize(v___x_1204_, 4, v___x_1199_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1205_ = lean_box(1);
v___x_1206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3);
v___x_1207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1206_);
lean_ctor_set(v___x_1208_, 2, v___x_1205_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(lean_object* v_msgData_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v_env_1213_; uint8_t v___x_1214_; lean_object* v_env_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_scopes_1218_; lean_object* v___x_1219_; lean_object* v_opts_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1212_ = lean_st_ref_get(v___y_1210_);
v_env_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_ref(v_env_1213_);
lean_dec(v___x_1212_);
v___x_1214_ = 0;
v_env_1215_ = l_Lean_Environment_setRecordingDeps(v_env_1213_, v___x_1214_);
v___x_1216_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1217_ = lean_st_ref_get(v___y_1210_);
v_scopes_1218_ = lean_ctor_get(v___x_1217_, 2);
lean_inc(v_scopes_1218_);
lean_dec(v___x_1217_);
v___x_1219_ = l_List_head_x21___redArg(v___x_1216_, v_scopes_1218_);
lean_dec(v_scopes_1218_);
v_opts_1220_ = lean_ctor_get(v___x_1219_, 1);
lean_inc_ref(v_opts_1220_);
lean_dec(v___x_1219_);
v___x_1221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1);
v___x_1222_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4);
v___x_1223_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1223_, 0, v_env_1215_);
lean_ctor_set(v___x_1223_, 1, v___x_1221_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
lean_ctor_set(v___x_1223_, 3, v_opts_1220_);
v___x_1224_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v_msgData_1209_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_1226_, v___y_1227_);
lean_dec(v___y_1227_);
return v_res_1229_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1230_; double v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_float_of_nat(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v_cls_1234_, lean_object* v_msg_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Elab_Command_getRef___redArg(v___y_1236_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1290_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msg_1235_, v___y_1237_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1290_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1290_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v_traceState_1247_; lean_object* v_env_1248_; lean_object* v_messages_1249_; lean_object* v_scopes_1250_; lean_object* v_usedQuotCtxts_1251_; lean_object* v_nextMacroScope_1252_; lean_object* v_maxRecDepth_1253_; lean_object* v_ngen_1254_; lean_object* v_auxDeclNGen_1255_; lean_object* v_infoState_1256_; lean_object* v_snapshotTasks_1257_; lean_object* v_prevLinterStates_1258_; lean_object* v_codeQualityEntryTasks_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1289_; 
v___x_1246_ = lean_st_ref_take(v___y_1237_);
v_traceState_1247_ = lean_ctor_get(v___x_1246_, 9);
v_env_1248_ = lean_ctor_get(v___x_1246_, 0);
v_messages_1249_ = lean_ctor_get(v___x_1246_, 1);
v_scopes_1250_ = lean_ctor_get(v___x_1246_, 2);
v_usedQuotCtxts_1251_ = lean_ctor_get(v___x_1246_, 3);
v_nextMacroScope_1252_ = lean_ctor_get(v___x_1246_, 4);
v_maxRecDepth_1253_ = lean_ctor_get(v___x_1246_, 5);
v_ngen_1254_ = lean_ctor_get(v___x_1246_, 6);
v_auxDeclNGen_1255_ = lean_ctor_get(v___x_1246_, 7);
v_infoState_1256_ = lean_ctor_get(v___x_1246_, 8);
v_snapshotTasks_1257_ = lean_ctor_get(v___x_1246_, 10);
v_prevLinterStates_1258_ = lean_ctor_get(v___x_1246_, 11);
v_codeQualityEntryTasks_1259_ = lean_ctor_get(v___x_1246_, 12);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1261_ = v___x_1246_;
v_isShared_1262_ = v_isSharedCheck_1289_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1259_);
lean_inc(v_prevLinterStates_1258_);
lean_inc(v_snapshotTasks_1257_);
lean_inc(v_traceState_1247_);
lean_inc(v_infoState_1256_);
lean_inc(v_auxDeclNGen_1255_);
lean_inc(v_ngen_1254_);
lean_inc(v_maxRecDepth_1253_);
lean_inc(v_nextMacroScope_1252_);
lean_inc(v_usedQuotCtxts_1251_);
lean_inc(v_scopes_1250_);
lean_inc(v_messages_1249_);
lean_inc(v_env_1248_);
lean_dec(v___x_1246_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1289_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
uint64_t v_tid_1263_; lean_object* v_traces_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1288_; 
v_tid_1263_ = lean_ctor_get_uint64(v_traceState_1247_, sizeof(void*)*1);
v_traces_1264_ = lean_ctor_get(v_traceState_1247_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_traceState_1247_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1266_ = v_traceState_1247_;
v_isShared_1267_ = v_isSharedCheck_1288_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_traces_1264_);
lean_dec(v_traceState_1247_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1288_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; double v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_1271_ = 0;
v___x_1272_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1273_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1273_, 0, v_cls_1234_);
lean_ctor_set(v___x_1273_, 1, v___x_1269_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
lean_ctor_set_float(v___x_1273_, sizeof(void*)*3, v___x_1270_);
lean_ctor_set_float(v___x_1273_, sizeof(void*)*3 + 8, v___x_1270_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*3 + 16, v___x_1271_);
v___x_1274_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_1275_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v_a_1242_);
lean_ctor_set(v___x_1275_, 2, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1240_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l_Lean_PersistentArray_push___redArg(v_traces_1264_, v___x_1276_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1277_);
v___x_1279_ = v___x_1266_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1277_);
lean_ctor_set_uint64(v_reuseFailAlloc_1287_, sizeof(void*)*1, v_tid_1263_);
v___x_1279_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1281_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 9, v___x_1279_);
v___x_1281_ = v___x_1261_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_env_1248_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_messages_1249_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_scopes_1250_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_usedQuotCtxts_1251_);
lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_nextMacroScope_1252_);
lean_ctor_set(v_reuseFailAlloc_1286_, 5, v_maxRecDepth_1253_);
lean_ctor_set(v_reuseFailAlloc_1286_, 6, v_ngen_1254_);
lean_ctor_set(v_reuseFailAlloc_1286_, 7, v_auxDeclNGen_1255_);
lean_ctor_set(v_reuseFailAlloc_1286_, 8, v_infoState_1256_);
lean_ctor_set(v_reuseFailAlloc_1286_, 9, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1286_, 10, v_snapshotTasks_1257_);
lean_ctor_set(v_reuseFailAlloc_1286_, 11, v_prevLinterStates_1258_);
lean_ctor_set(v_reuseFailAlloc_1286_, 12, v_codeQualityEntryTasks_1259_);
v___x_1281_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_st_ref_put(v___y_1237_, v___x_1281_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1268_);
v___x_1284_ = v___x_1244_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1268_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_msg_1235_);
lean_dec(v_cls_1234_);
v_a_1291_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1239_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1239_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v_cls_1299_, lean_object* v_msg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_cls_1299_, v_msg_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1304_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2));
v___x_1311_ = l_Lean_Name_append(v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4));
v___x_1314_ = l_Lean_stringToMessageData(v___x_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8));
v___x_1320_ = l_Lean_stringToMessageData(v___x_1319_);
return v___x_1320_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10));
v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(lean_object* v___x_1324_, lean_object* v_val_1325_, lean_object* v_cmd_1326_, uint8_t v_onUnsolved_1327_, uint8_t v___y_1328_, lean_object* v_as_1329_, size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec(v_cmd_1326_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_b_1332_);
return v___x_1337_;
}
else
{
lean_object* v_snd_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1486_; 
v_snd_1338_ = lean_ctor_get(v_b_1332_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_b_1332_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_b_1332_, 0);
lean_dec(v_unused_1487_);
v___x_1340_ = v_b_1332_;
v_isShared_1341_ = v_isSharedCheck_1486_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_snd_1338_);
lean_dec(v_b_1332_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1486_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1485_; 
v_fst_1342_ = lean_ctor_get(v_snd_1338_, 0);
v_snd_1343_ = lean_ctor_get(v_snd_1338_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_snd_1338_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1345_ = v_snd_1338_;
v_isShared_1346_ = v_isSharedCheck_1485_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snd_1343_);
lean_inc(v_fst_1342_);
lean_dec(v_snd_1338_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1485_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_a_1347_; lean_object* v_pos_1348_; lean_object* v_endPos_1349_; uint8_t v_severity_1350_; lean_object* v_data_1351_; lean_object* v___x_1352_; lean_object* v_a_1354_; 
v_a_1347_ = lean_array_uget_borrowed(v_as_1329_, v_i_1331_);
v_pos_1348_ = lean_ctor_get(v_a_1347_, 1);
v_endPos_1349_ = lean_ctor_get(v_a_1347_, 2);
lean_inc(v_endPos_1349_);
v_severity_1350_ = lean_ctor_get_uint8(v_a_1347_, sizeof(void*)*5 + 1);
v_data_1351_ = lean_ctor_get(v_a_1347_, 4);
v___x_1352_ = lean_box(0);
if (v_severity_1350_ == 2)
{
lean_object* v___f_1367_; uint8_t v___x_1368_; 
v___f_1367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1351_);
v___x_1368_ = l_Lean_MessageData_hasTag(v___f_1367_, v_data_1351_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_dec(v_endPos_1349_);
lean_del_object(v___x_1340_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_fst_1342_);
lean_ctor_set(v___x_1369_, 1, v_snd_1343_);
v_a_1354_ = v___x_1369_;
goto v___jp_1353_;
}
else
{
if (lean_obj_tag(v_endPos_1349_) == 1)
{
lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1482_; 
v_val_1370_ = lean_ctor_get(v_endPos_1349_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_endPos_1349_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1372_ = v_endPos_1349_;
v_isShared_1373_ = v_isSharedCheck_1482_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v_endPos_1349_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1482_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; uint8_t v___x_1378_; 
lean_inc_ref(v_pos_1348_);
v___x_1374_ = l_Lean_FileMap_ofPosition(v___x_1324_, v_pos_1348_);
v___x_1375_ = l_Lean_FileMap_ofPosition(v___x_1324_, v_val_1370_);
lean_inc(v___x_1375_);
lean_inc(v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = 0;
v___x_1378_ = l_Lean_Syntax_Range_includes(v_val_1325_, v___x_1376_, v___x_1377_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref_known(v___x_1376_, 2);
lean_dec(v___x_1375_);
lean_dec(v___x_1374_);
lean_del_object(v___x_1372_);
lean_del_object(v___x_1340_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_fst_1342_);
lean_ctor_set(v___x_1379_, 1, v_snd_1343_);
v_a_1354_ = v___x_1379_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1380_; 
lean_inc(v_cmd_1326_);
lean_inc_ref(v___x_1376_);
v___x_1380_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1376_, v_cmd_1326_);
if (lean_obj_tag(v___x_1380_) == 1)
{
lean_object* v_val_1381_; lean_object* v_fst_1382_; lean_object* v_snd_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v___x_1375_);
lean_dec(v___x_1374_);
lean_del_object(v___x_1372_);
v_val_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_fst_1382_ = lean_ctor_get(v_val_1381_, 0);
v_snd_1383_ = lean_ctor_get(v_val_1381_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_val_1381_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1385_ = v_val_1381_;
v_isShared_1386_ = v_isSharedCheck_1446_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_snd_1383_);
lean_inc(v_fst_1382_);
lean_dec(v_val_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1446_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; uint8_t v___y_1444_; lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Syntax_getPos_x3f(v_fst_1382_, v___x_1377_);
if (lean_obj_tag(v___x_1445_) == 0)
{
v___y_1444_ = v___x_1378_;
goto v___jp_1443_;
}
else
{
lean_dec_ref_known(v___x_1445_, 1);
v___y_1444_ = v___x_1377_;
goto v___jp_1443_;
}
v___jp_1387_:
{
lean_object* v___x_1393_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v_snd_1343_);
lean_ctor_set(v___x_1385_, 0, v_fst_1342_);
v___x_1393_ = v___x_1385_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_fst_1342_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_snd_1343_);
v___x_1393_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
size_t v_sz_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
v_sz_1394_ = lean_array_size(v___y_1389_);
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1376_, v_fst_1382_, v_snd_1383_, v___y_1388_, v___y_1389_, v_sz_1394_, v___x_1395_, v___x_1393_);
lean_dec_ref(v___y_1389_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v_fst_1398_; lean_object* v_snd_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v_fst_1398_ = lean_ctor_get(v_a_1397_, 0);
v_snd_1399_ = lean_ctor_get(v_a_1397_, 1);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_a_1397_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v_a_1397_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_snd_1399_);
lean_inc(v_fst_1398_);
lean_dec(v_a_1397_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_fst_1398_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_snd_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
v_a_1354_ = v___x_1404_;
goto v___jp_1353_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_del_object(v___x_1345_);
lean_dec(v_cmd_1326_);
v_a_1407_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1396_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1396_);
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
v___jp_1416_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
lean_inc_ref(v___x_1376_);
v___x_1417_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1376_);
v___x_1418_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1351_);
v___x_1419_ = lean_array_get_size(v___x_1418_);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_nat_dec_eq(v___x_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
v___y_1388_ = v___x_1417_;
v___y_1389_ = v___x_1418_;
v___y_1390_ = v___y_1333_;
v___y_1391_ = v___y_1334_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v_scopes_1427_; lean_object* v___x_1428_; lean_object* v_opts_1429_; uint8_t v_hasTrace_1430_; 
v___x_1422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1423_ = l_Lean_inheritedTraceOptions;
v___x_1424_ = lean_st_ref_get(v___x_1423_);
v___x_1425_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1426_ = lean_st_ref_get(v___y_1334_);
v_scopes_1427_ = lean_ctor_get(v___x_1426_, 2);
lean_inc(v_scopes_1427_);
lean_dec(v___x_1426_);
v___x_1428_ = l_List_head_x21___redArg(v___x_1425_, v_scopes_1427_);
lean_dec(v_scopes_1427_);
v_opts_1429_ = lean_ctor_get(v___x_1428_, 1);
lean_inc_ref(v_opts_1429_);
lean_dec(v___x_1428_);
v_hasTrace_1430_ = lean_ctor_get_uint8(v_opts_1429_, sizeof(void*)*1);
if (v_hasTrace_1430_ == 0)
{
lean_dec_ref(v_opts_1429_);
lean_dec(v___x_1424_);
v___y_1388_ = v___x_1417_;
v___y_1389_ = v___x_1418_;
v___y_1390_ = v___y_1333_;
v___y_1391_ = v___y_1334_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1432_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1424_, v_opts_1429_, v___x_1431_);
lean_dec_ref(v_opts_1429_);
lean_dec(v___x_1424_);
if (v___x_1432_ == 0)
{
v___y_1388_ = v___x_1417_;
v___y_1389_ = v___x_1418_;
v___y_1390_ = v___y_1333_;
v___y_1391_ = v___y_1334_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1434_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1422_, v___x_1433_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref_known(v___x_1434_, 1);
v___y_1388_ = v___x_1417_;
v___y_1389_ = v___x_1418_;
v___y_1390_ = v___y_1333_;
v___y_1391_ = v___y_1334_;
goto v___jp_1387_;
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v___x_1418_);
lean_dec(v___x_1417_);
lean_del_object(v___x_1385_);
lean_dec(v_snd_1383_);
lean_dec(v_fst_1382_);
lean_dec_ref_known(v___x_1376_, 2);
lean_del_object(v___x_1345_);
lean_dec(v_snd_1343_);
lean_dec(v_fst_1342_);
lean_dec(v_cmd_1326_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
}
}
v___jp_1443_:
{
if (v_onUnsolved_1327_ == 0)
{
if (v___y_1328_ == 0)
{
lean_del_object(v___x_1385_);
lean_dec(v_snd_1383_);
lean_dec(v_fst_1382_);
lean_dec_ref_known(v___x_1376_, 2);
goto v___jp_1361_;
}
else
{
if (v___y_1444_ == 0)
{
lean_del_object(v___x_1385_);
lean_dec(v_snd_1383_);
lean_dec(v_fst_1382_);
lean_dec_ref_known(v___x_1376_, 2);
goto v___jp_1361_;
}
else
{
lean_del_object(v___x_1340_);
goto v___jp_1416_;
}
}
}
else
{
lean_del_object(v___x_1340_);
goto v___jp_1416_;
}
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_scopes_1452_; lean_object* v___x_1453_; lean_object* v_opts_1454_; uint8_t v_hasTrace_1455_; 
lean_dec(v___x_1380_);
lean_dec_ref_known(v___x_1376_, 2);
lean_del_object(v___x_1340_);
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1448_ = l_Lean_inheritedTraceOptions;
v___x_1449_ = lean_st_ref_get(v___x_1448_);
v___x_1450_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1451_ = lean_st_ref_get(v___y_1334_);
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
lean_dec(v___x_1375_);
lean_dec(v___x_1374_);
lean_del_object(v___x_1372_);
goto v___jp_1365_;
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
lean_dec(v___x_1375_);
lean_dec(v___x_1374_);
lean_del_object(v___x_1372_);
goto v___jp_1365_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1459_ = l_Nat_reprFast(v___x_1374_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 3);
lean_ctor_set(v___x_1372_, 0, v___x_1459_);
v___x_1461_ = v___x_1372_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1462_ = l_Lean_MessageData_ofFormat(v___x_1461_);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1458_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Nat_reprFast(v___x_1375_);
v___x_1467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
v___x_1468_ = l_Lean_MessageData_ofFormat(v___x_1467_);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1465_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1447_, v___x_1471_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_dec_ref_known(v___x_1472_, 1);
goto v___jp_1365_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_del_object(v___x_1345_);
lean_dec(v_snd_1343_);
lean_dec(v_fst_1342_);
lean_dec(v_cmd_1326_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
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
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
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
lean_object* v___x_1483_; 
lean_dec(v_endPos_1349_);
lean_del_object(v___x_1340_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_fst_1342_);
lean_ctor_set(v___x_1483_, 1, v_snd_1343_);
v_a_1354_ = v___x_1483_;
goto v___jp_1353_;
}
}
}
else
{
lean_object* v___x_1484_; 
lean_dec(v_endPos_1349_);
lean_del_object(v___x_1340_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_fst_1342_);
lean_ctor_set(v___x_1484_, 1, v_snd_1343_);
v_a_1354_ = v___x_1484_;
goto v___jp_1353_;
}
v___jp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v_a_1354_);
lean_ctor_set(v___x_1345_, 0, v___x_1352_);
v___x_1356_ = v___x_1345_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_a_1354_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
size_t v___x_1357_; size_t v___x_1358_; 
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = lean_usize_add(v_i_1331_, v___x_1357_);
v_i_1331_ = v___x_1358_;
v_b_1332_ = v___x_1356_;
goto _start;
}
}
v___jp_1361_:
{
lean_object* v___x_1363_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v_snd_1343_);
lean_ctor_set(v___x_1340_, 0, v_fst_1342_);
v___x_1363_ = v___x_1340_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_fst_1342_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_snd_1343_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v_a_1354_ = v___x_1363_;
goto v___jp_1353_;
}
}
v___jp_1365_:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_fst_1342_);
lean_ctor_set(v___x_1366_, 1, v_snd_1343_);
v_a_1354_ = v___x_1366_;
goto v___jp_1353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___boxed(lean_object* v___x_1488_, lean_object* v_val_1489_, lean_object* v_cmd_1490_, lean_object* v_onUnsolved_1491_, lean_object* v___y_1492_, lean_object* v_as_1493_, lean_object* v_sz_1494_, lean_object* v_i_1495_, lean_object* v_b_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v_onUnsolved_boxed_1500_; uint8_t v___y_12283__boxed_1501_; size_t v_sz_boxed_1502_; size_t v_i_boxed_1503_; lean_object* v_res_1504_; 
v_onUnsolved_boxed_1500_ = lean_unbox(v_onUnsolved_1491_);
v___y_12283__boxed_1501_ = lean_unbox(v___y_1492_);
v_sz_boxed_1502_ = lean_unbox_usize(v_sz_1494_);
lean_dec(v_sz_1494_);
v_i_boxed_1503_ = lean_unbox_usize(v_i_1495_);
lean_dec(v_i_1495_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1488_, v_val_1489_, v_cmd_1490_, v_onUnsolved_boxed_1500_, v___y_12283__boxed_1501_, v_as_1493_, v_sz_boxed_1502_, v_i_boxed_1503_, v_b_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec_ref(v_as_1493_);
lean_dec_ref(v_val_1489_);
lean_dec_ref(v___x_1488_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object* v___x_1505_, lean_object* v_val_1506_, lean_object* v_cmd_1507_, uint8_t v_onUnsolved_1508_, uint8_t v___y_1509_, lean_object* v_as_1510_, size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_usize_dec_lt(v_i_1512_, v_sz_1511_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
lean_dec(v_cmd_1507_);
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_b_1513_);
return v___x_1518_;
}
else
{
lean_object* v_snd_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1667_; 
v_snd_1519_ = lean_ctor_get(v_b_1513_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_b_1513_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v_b_1513_, 0);
lean_dec(v_unused_1668_);
v___x_1521_ = v_b_1513_;
v_isShared_1522_ = v_isSharedCheck_1667_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snd_1519_);
lean_dec(v_b_1513_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1667_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v_fst_1523_; lean_object* v_snd_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1666_; 
v_fst_1523_ = lean_ctor_get(v_snd_1519_, 0);
v_snd_1524_ = lean_ctor_get(v_snd_1519_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_snd_1519_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1526_ = v_snd_1519_;
v_isShared_1527_ = v_isSharedCheck_1666_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snd_1524_);
lean_inc(v_fst_1523_);
lean_dec(v_snd_1519_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1666_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_a_1528_; lean_object* v_pos_1529_; lean_object* v_endPos_1530_; uint8_t v_severity_1531_; lean_object* v_data_1532_; lean_object* v___x_1533_; lean_object* v_a_1535_; 
v_a_1528_ = lean_array_uget_borrowed(v_as_1510_, v_i_1512_);
v_pos_1529_ = lean_ctor_get(v_a_1528_, 1);
v_endPos_1530_ = lean_ctor_get(v_a_1528_, 2);
lean_inc(v_endPos_1530_);
v_severity_1531_ = lean_ctor_get_uint8(v_a_1528_, sizeof(void*)*5 + 1);
v_data_1532_ = lean_ctor_get(v_a_1528_, 4);
v___x_1533_ = lean_box(0);
if (v_severity_1531_ == 2)
{
lean_object* v___f_1548_; uint8_t v___x_1549_; 
v___f_1548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1532_);
v___x_1549_ = l_Lean_MessageData_hasTag(v___f_1548_, v_data_1532_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
lean_dec(v_endPos_1530_);
lean_del_object(v___x_1521_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_fst_1523_);
lean_ctor_set(v___x_1550_, 1, v_snd_1524_);
v_a_1535_ = v___x_1550_;
goto v___jp_1534_;
}
else
{
if (lean_obj_tag(v_endPos_1530_) == 1)
{
lean_object* v_val_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1663_; 
v_val_1551_ = lean_ctor_get(v_endPos_1530_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_endPos_1530_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1553_ = v_endPos_1530_;
v_isShared_1554_ = v_isSharedCheck_1663_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_val_1551_);
lean_dec(v_endPos_1530_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1663_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; uint8_t v___x_1559_; 
lean_inc_ref(v_pos_1529_);
v___x_1555_ = l_Lean_FileMap_ofPosition(v___x_1505_, v_pos_1529_);
v___x_1556_ = l_Lean_FileMap_ofPosition(v___x_1505_, v_val_1551_);
lean_inc(v___x_1556_);
lean_inc(v___x_1555_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = 0;
v___x_1559_ = l_Lean_Syntax_Range_includes(v_val_1506_, v___x_1557_, v___x_1558_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_dec_ref_known(v___x_1557_, 2);
lean_dec(v___x_1556_);
lean_dec(v___x_1555_);
lean_del_object(v___x_1553_);
lean_del_object(v___x_1521_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_fst_1523_);
lean_ctor_set(v___x_1560_, 1, v_snd_1524_);
v_a_1535_ = v___x_1560_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1561_; 
lean_inc(v_cmd_1507_);
lean_inc_ref(v___x_1557_);
v___x_1561_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1557_, v_cmd_1507_);
if (lean_obj_tag(v___x_1561_) == 1)
{
lean_object* v_val_1562_; lean_object* v_fst_1563_; lean_object* v_snd_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1627_; 
lean_dec(v___x_1556_);
lean_dec(v___x_1555_);
lean_del_object(v___x_1553_);
v_val_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_val_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v_fst_1563_ = lean_ctor_get(v_val_1562_, 0);
v_snd_1564_ = lean_ctor_get(v_val_1562_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_val_1562_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1566_ = v_val_1562_;
v_isShared_1567_ = v_isSharedCheck_1627_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_snd_1564_);
lean_inc(v_fst_1563_);
lean_dec(v_val_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1627_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; uint8_t v___y_1625_; lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Syntax_getPos_x3f(v_fst_1563_, v___x_1558_);
if (lean_obj_tag(v___x_1626_) == 0)
{
v___y_1625_ = v___x_1559_;
goto v___jp_1624_;
}
else
{
lean_dec_ref_known(v___x_1626_, 1);
v___y_1625_ = v___x_1558_;
goto v___jp_1624_;
}
v___jp_1568_:
{
lean_object* v___x_1574_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 1, v_snd_1524_);
lean_ctor_set(v___x_1566_, 0, v_fst_1523_);
v___x_1574_ = v___x_1566_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_fst_1523_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_snd_1524_);
v___x_1574_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
size_t v_sz_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v_sz_1575_ = lean_array_size(v___y_1569_);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1557_, v_fst_1563_, v_snd_1564_, v___y_1570_, v___y_1569_, v_sz_1575_, v___x_1576_, v___x_1574_);
lean_dec_ref(v___y_1569_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v_fst_1579_; lean_object* v_snd_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v_fst_1579_ = lean_ctor_get(v_a_1578_, 0);
v_snd_1580_ = lean_ctor_get(v_a_1578_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_a_1578_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v_a_1578_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_snd_1580_);
lean_inc(v_fst_1579_);
lean_dec(v_a_1578_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_fst_1579_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_snd_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
v_a_1535_ = v___x_1585_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_del_object(v___x_1526_);
lean_dec(v_cmd_1507_);
v_a_1588_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1577_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1577_);
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
v___jp_1597_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
lean_inc_ref(v___x_1557_);
v___x_1598_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1557_);
v___x_1599_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1532_);
v___x_1600_ = lean_array_get_size(v___x_1599_);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_nat_dec_eq(v___x_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
v___y_1569_ = v___x_1599_;
v___y_1570_ = v___x_1598_;
v___y_1571_ = v___y_1514_;
v___y_1572_ = v___y_1515_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_scopes_1608_; lean_object* v___x_1609_; lean_object* v_opts_1610_; uint8_t v_hasTrace_1611_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1604_ = l_Lean_inheritedTraceOptions;
v___x_1605_ = lean_st_ref_get(v___x_1604_);
v___x_1606_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1607_ = lean_st_ref_get(v___y_1515_);
v_scopes_1608_ = lean_ctor_get(v___x_1607_, 2);
lean_inc(v_scopes_1608_);
lean_dec(v___x_1607_);
v___x_1609_ = l_List_head_x21___redArg(v___x_1606_, v_scopes_1608_);
lean_dec(v_scopes_1608_);
v_opts_1610_ = lean_ctor_get(v___x_1609_, 1);
lean_inc_ref(v_opts_1610_);
lean_dec(v___x_1609_);
v_hasTrace_1611_ = lean_ctor_get_uint8(v_opts_1610_, sizeof(void*)*1);
if (v_hasTrace_1611_ == 0)
{
lean_dec_ref(v_opts_1610_);
lean_dec(v___x_1605_);
v___y_1569_ = v___x_1599_;
v___y_1570_ = v___x_1598_;
v___y_1571_ = v___y_1514_;
v___y_1572_ = v___y_1515_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1613_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1605_, v_opts_1610_, v___x_1612_);
lean_dec_ref(v_opts_1610_);
lean_dec(v___x_1605_);
if (v___x_1613_ == 0)
{
v___y_1569_ = v___x_1599_;
v___y_1570_ = v___x_1598_;
v___y_1571_ = v___y_1514_;
v___y_1572_ = v___y_1515_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1615_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1603_, v___x_1614_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_dec_ref_known(v___x_1615_, 1);
v___y_1569_ = v___x_1599_;
v___y_1570_ = v___x_1598_;
v___y_1571_ = v___y_1514_;
v___y_1572_ = v___y_1515_;
goto v___jp_1568_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v___x_1599_);
lean_dec(v___x_1598_);
lean_del_object(v___x_1566_);
lean_dec(v_snd_1564_);
lean_dec(v_fst_1563_);
lean_dec_ref_known(v___x_1557_, 2);
lean_del_object(v___x_1526_);
lean_dec(v_snd_1524_);
lean_dec(v_fst_1523_);
lean_dec(v_cmd_1507_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
}
v___jp_1624_:
{
if (v_onUnsolved_1508_ == 0)
{
if (v___y_1509_ == 0)
{
lean_del_object(v___x_1566_);
lean_dec(v_snd_1564_);
lean_dec(v_fst_1563_);
lean_dec_ref_known(v___x_1557_, 2);
goto v___jp_1542_;
}
else
{
if (v___y_1625_ == 0)
{
lean_del_object(v___x_1566_);
lean_dec(v_snd_1564_);
lean_dec(v_fst_1563_);
lean_dec_ref_known(v___x_1557_, 2);
goto v___jp_1542_;
}
else
{
lean_del_object(v___x_1521_);
goto v___jp_1597_;
}
}
}
else
{
lean_del_object(v___x_1521_);
goto v___jp_1597_;
}
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_scopes_1633_; lean_object* v___x_1634_; lean_object* v_opts_1635_; uint8_t v_hasTrace_1636_; 
lean_dec(v___x_1561_);
lean_dec_ref_known(v___x_1557_, 2);
lean_del_object(v___x_1521_);
v___x_1628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1629_ = l_Lean_inheritedTraceOptions;
v___x_1630_ = lean_st_ref_get(v___x_1629_);
v___x_1631_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1632_ = lean_st_ref_get(v___y_1515_);
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
lean_dec(v___x_1556_);
lean_dec(v___x_1555_);
lean_del_object(v___x_1553_);
goto v___jp_1546_;
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
lean_dec(v___x_1556_);
lean_dec(v___x_1555_);
lean_del_object(v___x_1553_);
goto v___jp_1546_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1640_ = l_Nat_reprFast(v___x_1555_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set_tag(v___x_1553_, 3);
lean_ctor_set(v___x_1553_, 0, v___x_1640_);
v___x_1642_ = v___x_1553_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1643_ = l_Lean_MessageData_ofFormat(v___x_1642_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1639_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = l_Nat_reprFast(v___x_1556_);
v___x_1648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
v___x_1649_ = l_Lean_MessageData_ofFormat(v___x_1648_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1646_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1628_, v___x_1652_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_dec_ref_known(v___x_1653_, 1);
goto v___jp_1546_;
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_del_object(v___x_1526_);
lean_dec(v_snd_1524_);
lean_dec(v_fst_1523_);
lean_dec(v_cmd_1507_);
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
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
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
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
lean_object* v___x_1664_; 
lean_dec(v_endPos_1530_);
lean_del_object(v___x_1521_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_fst_1523_);
lean_ctor_set(v___x_1664_, 1, v_snd_1524_);
v_a_1535_ = v___x_1664_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1665_; 
lean_dec(v_endPos_1530_);
lean_del_object(v___x_1521_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v_fst_1523_);
lean_ctor_set(v___x_1665_, 1, v_snd_1524_);
v_a_1535_ = v___x_1665_;
goto v___jp_1534_;
}
v___jp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v_a_1535_);
lean_ctor_set(v___x_1526_, 0, v___x_1533_);
v___x_1537_ = v___x_1526_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_a_1535_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1512_, v___x_1538_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1505_, v_val_1506_, v_cmd_1507_, v_onUnsolved_1508_, v___y_1509_, v_as_1510_, v_sz_1511_, v___x_1539_, v___x_1537_, v___y_1514_, v___y_1515_);
return v___x_1540_;
}
}
v___jp_1542_:
{
lean_object* v___x_1544_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v_snd_1524_);
lean_ctor_set(v___x_1521_, 0, v_fst_1523_);
v___x_1544_ = v___x_1521_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_fst_1523_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_snd_1524_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
v_a_1535_ = v___x_1544_;
goto v___jp_1534_;
}
}
v___jp_1546_:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_fst_1523_);
lean_ctor_set(v___x_1547_, 1, v_snd_1524_);
v_a_1535_ = v___x_1547_;
goto v___jp_1534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object* v___x_1669_, lean_object* v_val_1670_, lean_object* v_cmd_1671_, lean_object* v_onUnsolved_1672_, lean_object* v___y_1673_, lean_object* v_as_1674_, lean_object* v_sz_1675_, lean_object* v_i_1676_, lean_object* v_b_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
uint8_t v_onUnsolved_boxed_1681_; uint8_t v___y_12624__boxed_1682_; size_t v_sz_boxed_1683_; size_t v_i_boxed_1684_; lean_object* v_res_1685_; 
v_onUnsolved_boxed_1681_ = lean_unbox(v_onUnsolved_1672_);
v___y_12624__boxed_1682_ = lean_unbox(v___y_1673_);
v_sz_boxed_1683_ = lean_unbox_usize(v_sz_1675_);
lean_dec(v_sz_1675_);
v_i_boxed_1684_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_res_1685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_1669_, v_val_1670_, v_cmd_1671_, v_onUnsolved_boxed_1681_, v___y_12624__boxed_1682_, v_as_1674_, v_sz_boxed_1683_, v_i_boxed_1684_, v_b_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v_as_1674_);
lean_dec_ref(v_val_1670_);
lean_dec_ref(v___x_1669_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(lean_object* v___x_1686_, lean_object* v_val_1687_, lean_object* v_cmd_1688_, uint8_t v_onUnsolved_1689_, uint8_t v___y_1690_, lean_object* v_as_1691_, size_t v_sz_1692_, size_t v_i_1693_, lean_object* v_b_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_usize_dec_lt(v_i_1693_, v_sz_1692_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
lean_dec(v_cmd_1688_);
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_b_1694_);
return v___x_1699_;
}
else
{
lean_object* v_snd_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1848_; 
v_snd_1700_ = lean_ctor_get(v_b_1694_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_b_1694_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v_b_1694_, 0);
lean_dec(v_unused_1849_);
v___x_1702_ = v_b_1694_;
v_isShared_1703_ = v_isSharedCheck_1848_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_snd_1700_);
lean_dec(v_b_1694_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1848_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_fst_1704_; lean_object* v_snd_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1847_; 
v_fst_1704_ = lean_ctor_get(v_snd_1700_, 0);
v_snd_1705_ = lean_ctor_get(v_snd_1700_, 1);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_snd_1700_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1707_ = v_snd_1700_;
v_isShared_1708_ = v_isSharedCheck_1847_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snd_1705_);
lean_inc(v_fst_1704_);
lean_dec(v_snd_1700_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1847_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_a_1709_; lean_object* v_pos_1710_; lean_object* v_endPos_1711_; uint8_t v_severity_1712_; lean_object* v_data_1713_; lean_object* v___x_1714_; lean_object* v_a_1716_; 
v_a_1709_ = lean_array_uget_borrowed(v_as_1691_, v_i_1693_);
v_pos_1710_ = lean_ctor_get(v_a_1709_, 1);
v_endPos_1711_ = lean_ctor_get(v_a_1709_, 2);
lean_inc(v_endPos_1711_);
v_severity_1712_ = lean_ctor_get_uint8(v_a_1709_, sizeof(void*)*5 + 1);
v_data_1713_ = lean_ctor_get(v_a_1709_, 4);
v___x_1714_ = lean_box(0);
if (v_severity_1712_ == 2)
{
lean_object* v___f_1729_; uint8_t v___x_1730_; 
v___f_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1713_);
v___x_1730_ = l_Lean_MessageData_hasTag(v___f_1729_, v_data_1713_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
lean_dec(v_endPos_1711_);
lean_del_object(v___x_1702_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_fst_1704_);
lean_ctor_set(v___x_1731_, 1, v_snd_1705_);
v_a_1716_ = v___x_1731_;
goto v___jp_1715_;
}
else
{
if (lean_obj_tag(v_endPos_1711_) == 1)
{
lean_object* v_val_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1844_; 
v_val_1732_ = lean_ctor_get(v_endPos_1711_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_endPos_1711_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1734_ = v_endPos_1711_;
v_isShared_1735_ = v_isSharedCheck_1844_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_val_1732_);
lean_dec(v_endPos_1711_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1844_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; uint8_t v___x_1740_; 
lean_inc_ref(v_pos_1710_);
v___x_1736_ = l_Lean_FileMap_ofPosition(v___x_1686_, v_pos_1710_);
v___x_1737_ = l_Lean_FileMap_ofPosition(v___x_1686_, v_val_1732_);
lean_inc(v___x_1737_);
lean_inc(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = 0;
v___x_1740_ = l_Lean_Syntax_Range_includes(v_val_1687_, v___x_1738_, v___x_1739_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref_known(v___x_1738_, 2);
lean_dec(v___x_1737_);
lean_dec(v___x_1736_);
lean_del_object(v___x_1734_);
lean_del_object(v___x_1702_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v_fst_1704_);
lean_ctor_set(v___x_1741_, 1, v_snd_1705_);
v_a_1716_ = v___x_1741_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1742_; 
lean_inc(v_cmd_1688_);
lean_inc_ref(v___x_1738_);
v___x_1742_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1738_, v_cmd_1688_);
if (lean_obj_tag(v___x_1742_) == 1)
{
lean_object* v_val_1743_; lean_object* v_fst_1744_; lean_object* v_snd_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v___x_1737_);
lean_dec(v___x_1736_);
lean_del_object(v___x_1734_);
v_val_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v_fst_1744_ = lean_ctor_get(v_val_1743_, 0);
v_snd_1745_ = lean_ctor_get(v_val_1743_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_val_1743_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1747_ = v_val_1743_;
v_isShared_1748_ = v_isSharedCheck_1808_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_snd_1745_);
lean_inc(v_fst_1744_);
lean_dec(v_val_1743_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1808_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; uint8_t v___y_1806_; lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_Syntax_getPos_x3f(v_fst_1744_, v___x_1739_);
if (lean_obj_tag(v___x_1807_) == 0)
{
v___y_1806_ = v___x_1740_;
goto v___jp_1805_;
}
else
{
lean_dec_ref_known(v___x_1807_, 1);
v___y_1806_ = v___x_1739_;
goto v___jp_1805_;
}
v___jp_1749_:
{
lean_object* v___x_1755_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v_snd_1705_);
lean_ctor_set(v___x_1747_, 0, v_fst_1704_);
v___x_1755_ = v___x_1747_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_fst_1704_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_snd_1705_);
v___x_1755_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
size_t v_sz_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v_sz_1756_ = lean_array_size(v___y_1751_);
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1738_, v_fst_1744_, v_snd_1745_, v___y_1750_, v___y_1751_, v_sz_1756_, v___x_1757_, v___x_1755_);
lean_dec_ref(v___y_1751_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v_fst_1760_ = lean_ctor_get(v_a_1759_, 0);
v_snd_1761_ = lean_ctor_get(v_a_1759_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_a_1759_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v_a_1759_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snd_1761_);
lean_inc(v_fst_1760_);
lean_dec(v_a_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_fst_1760_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_snd_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
v_a_1716_ = v___x_1766_;
goto v___jp_1715_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_del_object(v___x_1707_);
lean_dec(v_cmd_1688_);
v_a_1769_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1758_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1758_);
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
v___jp_1778_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
lean_inc_ref(v___x_1738_);
v___x_1779_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1738_);
v___x_1780_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1713_);
v___x_1781_ = lean_array_get_size(v___x_1780_);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_nat_dec_eq(v___x_1781_, v___x_1782_);
if (v___x_1783_ == 0)
{
v___y_1750_ = v___x_1779_;
v___y_1751_ = v___x_1780_;
v___y_1752_ = v___y_1695_;
v___y_1753_ = v___y_1696_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_scopes_1789_; lean_object* v___x_1790_; lean_object* v_opts_1791_; uint8_t v_hasTrace_1792_; 
v___x_1784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1785_ = l_Lean_inheritedTraceOptions;
v___x_1786_ = lean_st_ref_get(v___x_1785_);
v___x_1787_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1788_ = lean_st_ref_get(v___y_1696_);
v_scopes_1789_ = lean_ctor_get(v___x_1788_, 2);
lean_inc(v_scopes_1789_);
lean_dec(v___x_1788_);
v___x_1790_ = l_List_head_x21___redArg(v___x_1787_, v_scopes_1789_);
lean_dec(v_scopes_1789_);
v_opts_1791_ = lean_ctor_get(v___x_1790_, 1);
lean_inc_ref(v_opts_1791_);
lean_dec(v___x_1790_);
v_hasTrace_1792_ = lean_ctor_get_uint8(v_opts_1791_, sizeof(void*)*1);
if (v_hasTrace_1792_ == 0)
{
lean_dec_ref(v_opts_1791_);
lean_dec(v___x_1786_);
v___y_1750_ = v___x_1779_;
v___y_1751_ = v___x_1780_;
v___y_1752_ = v___y_1695_;
v___y_1753_ = v___y_1696_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1794_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1786_, v_opts_1791_, v___x_1793_);
lean_dec_ref(v_opts_1791_);
lean_dec(v___x_1786_);
if (v___x_1794_ == 0)
{
v___y_1750_ = v___x_1779_;
v___y_1751_ = v___x_1780_;
v___y_1752_ = v___y_1695_;
v___y_1753_ = v___y_1696_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1796_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1784_, v___x_1795_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_dec_ref_known(v___x_1796_, 1);
v___y_1750_ = v___x_1779_;
v___y_1751_ = v___x_1780_;
v___y_1752_ = v___y_1695_;
v___y_1753_ = v___y_1696_;
goto v___jp_1749_;
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v___x_1780_);
lean_dec(v___x_1779_);
lean_del_object(v___x_1747_);
lean_dec(v_snd_1745_);
lean_dec(v_fst_1744_);
lean_dec_ref_known(v___x_1738_, 2);
lean_del_object(v___x_1707_);
lean_dec(v_snd_1705_);
lean_dec(v_fst_1704_);
lean_dec(v_cmd_1688_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
}
}
v___jp_1805_:
{
if (v_onUnsolved_1689_ == 0)
{
if (v___y_1690_ == 0)
{
lean_del_object(v___x_1747_);
lean_dec(v_snd_1745_);
lean_dec(v_fst_1744_);
lean_dec_ref_known(v___x_1738_, 2);
goto v___jp_1723_;
}
else
{
if (v___y_1806_ == 0)
{
lean_del_object(v___x_1747_);
lean_dec(v_snd_1745_);
lean_dec(v_fst_1744_);
lean_dec_ref_known(v___x_1738_, 2);
goto v___jp_1723_;
}
else
{
lean_del_object(v___x_1702_);
goto v___jp_1778_;
}
}
}
else
{
lean_del_object(v___x_1702_);
goto v___jp_1778_;
}
}
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_scopes_1814_; lean_object* v___x_1815_; lean_object* v_opts_1816_; uint8_t v_hasTrace_1817_; 
lean_dec(v___x_1742_);
lean_dec_ref_known(v___x_1738_, 2);
lean_del_object(v___x_1702_);
v___x_1809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1810_ = l_Lean_inheritedTraceOptions;
v___x_1811_ = lean_st_ref_get(v___x_1810_);
v___x_1812_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1813_ = lean_st_ref_get(v___y_1696_);
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
lean_dec(v___x_1737_);
lean_dec(v___x_1736_);
lean_del_object(v___x_1734_);
goto v___jp_1727_;
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
lean_dec(v___x_1737_);
lean_dec(v___x_1736_);
lean_del_object(v___x_1734_);
goto v___jp_1727_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1821_ = l_Nat_reprFast(v___x_1736_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 3);
lean_ctor_set(v___x_1734_, 0, v___x_1821_);
v___x_1823_ = v___x_1734_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1824_ = l_Lean_MessageData_ofFormat(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1820_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Nat_reprFast(v___x_1737_);
v___x_1829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
v___x_1830_ = l_Lean_MessageData_ofFormat(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1827_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1809_, v___x_1833_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_dec_ref_known(v___x_1834_, 1);
goto v___jp_1727_;
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_del_object(v___x_1707_);
lean_dec(v_snd_1705_);
lean_dec(v_fst_1704_);
lean_dec(v_cmd_1688_);
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
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
lean_object* v___x_1845_; 
lean_dec(v_endPos_1711_);
lean_del_object(v___x_1702_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_fst_1704_);
lean_ctor_set(v___x_1845_, 1, v_snd_1705_);
v_a_1716_ = v___x_1845_;
goto v___jp_1715_;
}
}
}
else
{
lean_object* v___x_1846_; 
lean_dec(v_endPos_1711_);
lean_del_object(v___x_1702_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v_fst_1704_);
lean_ctor_set(v___x_1846_, 1, v_snd_1705_);
v_a_1716_ = v___x_1846_;
goto v___jp_1715_;
}
v___jp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v_a_1716_);
lean_ctor_set(v___x_1707_, 0, v___x_1714_);
v___x_1718_ = v___x_1707_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_a_1716_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
size_t v___x_1719_; size_t v___x_1720_; 
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1693_, v___x_1719_);
v_i_1693_ = v___x_1720_;
v_b_1694_ = v___x_1718_;
goto _start;
}
}
v___jp_1723_:
{
lean_object* v___x_1725_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_snd_1705_);
lean_ctor_set(v___x_1702_, 0, v_fst_1704_);
v___x_1725_ = v___x_1702_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_fst_1704_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_snd_1705_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v_a_1716_ = v___x_1725_;
goto v___jp_1715_;
}
}
v___jp_1727_:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_fst_1704_);
lean_ctor_set(v___x_1728_, 1, v_snd_1705_);
v_a_1716_ = v___x_1728_;
goto v___jp_1715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v___x_1850_, lean_object* v_val_1851_, lean_object* v_cmd_1852_, lean_object* v_onUnsolved_1853_, lean_object* v___y_1854_, lean_object* v_as_1855_, lean_object* v_sz_1856_, lean_object* v_i_1857_, lean_object* v_b_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v_onUnsolved_boxed_1862_; uint8_t v___y_12956__boxed_1863_; size_t v_sz_boxed_1864_; size_t v_i_boxed_1865_; lean_object* v_res_1866_; 
v_onUnsolved_boxed_1862_ = lean_unbox(v_onUnsolved_1853_);
v___y_12956__boxed_1863_ = lean_unbox(v___y_1854_);
v_sz_boxed_1864_ = lean_unbox_usize(v_sz_1856_);
lean_dec(v_sz_1856_);
v_i_boxed_1865_ = lean_unbox_usize(v_i_1857_);
lean_dec(v_i_1857_);
v_res_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1850_, v_val_1851_, v_cmd_1852_, v_onUnsolved_boxed_1862_, v___y_12956__boxed_1863_, v_as_1855_, v_sz_boxed_1864_, v_i_boxed_1865_, v_b_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec_ref(v_as_1855_);
lean_dec_ref(v_val_1851_);
lean_dec_ref(v___x_1850_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(lean_object* v___x_1867_, lean_object* v_val_1868_, lean_object* v_cmd_1869_, uint8_t v_onUnsolved_1870_, uint8_t v___y_1871_, lean_object* v_as_1872_, size_t v_sz_1873_, size_t v_i_1874_, lean_object* v_b_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v___x_1879_; 
v___x_1879_ = lean_usize_dec_lt(v_i_1874_, v_sz_1873_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec(v_cmd_1869_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_b_1875_);
return v___x_1880_;
}
else
{
lean_object* v_snd_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_2029_; 
v_snd_1881_ = lean_ctor_get(v_b_1875_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_b_1875_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_b_1875_, 0);
lean_dec(v_unused_2030_);
v___x_1883_ = v_b_1875_;
v_isShared_1884_ = v_isSharedCheck_2029_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_snd_1881_);
lean_dec(v_b_1875_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_2029_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v_fst_1885_; lean_object* v_snd_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_2028_; 
v_fst_1885_ = lean_ctor_get(v_snd_1881_, 0);
v_snd_1886_ = lean_ctor_get(v_snd_1881_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_snd_1881_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1888_ = v_snd_1881_;
v_isShared_1889_ = v_isSharedCheck_2028_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snd_1886_);
lean_inc(v_fst_1885_);
lean_dec(v_snd_1881_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_2028_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_a_1890_; lean_object* v_pos_1891_; lean_object* v_endPos_1892_; uint8_t v_severity_1893_; lean_object* v_data_1894_; lean_object* v___x_1895_; lean_object* v_a_1897_; 
v_a_1890_ = lean_array_uget_borrowed(v_as_1872_, v_i_1874_);
v_pos_1891_ = lean_ctor_get(v_a_1890_, 1);
v_endPos_1892_ = lean_ctor_get(v_a_1890_, 2);
lean_inc(v_endPos_1892_);
v_severity_1893_ = lean_ctor_get_uint8(v_a_1890_, sizeof(void*)*5 + 1);
v_data_1894_ = lean_ctor_get(v_a_1890_, 4);
v___x_1895_ = lean_box(0);
if (v_severity_1893_ == 2)
{
lean_object* v___f_1910_; uint8_t v___x_1911_; 
v___f_1910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1894_);
v___x_1911_ = l_Lean_MessageData_hasTag(v___f_1910_, v_data_1894_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
lean_dec(v_endPos_1892_);
lean_del_object(v___x_1883_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v_fst_1885_);
lean_ctor_set(v___x_1912_, 1, v_snd_1886_);
v_a_1897_ = v___x_1912_;
goto v___jp_1896_;
}
else
{
if (lean_obj_tag(v_endPos_1892_) == 1)
{
lean_object* v_val_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_2025_; 
v_val_1913_ = lean_ctor_get(v_endPos_1892_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_endPos_1892_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_1915_ = v_endPos_1892_;
v_isShared_1916_ = v_isSharedCheck_2025_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_val_1913_);
lean_dec(v_endPos_1892_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_2025_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; uint8_t v___x_1921_; 
lean_inc_ref(v_pos_1891_);
v___x_1917_ = l_Lean_FileMap_ofPosition(v___x_1867_, v_pos_1891_);
v___x_1918_ = l_Lean_FileMap_ofPosition(v___x_1867_, v_val_1913_);
lean_inc(v___x_1918_);
lean_inc(v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = 0;
v___x_1921_ = l_Lean_Syntax_Range_includes(v_val_1868_, v___x_1919_, v___x_1920_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; 
lean_dec_ref_known(v___x_1919_, 2);
lean_dec(v___x_1918_);
lean_dec(v___x_1917_);
lean_del_object(v___x_1915_);
lean_del_object(v___x_1883_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_fst_1885_);
lean_ctor_set(v___x_1922_, 1, v_snd_1886_);
v_a_1897_ = v___x_1922_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1923_; 
lean_inc(v_cmd_1869_);
lean_inc_ref(v___x_1919_);
v___x_1923_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1919_, v_cmd_1869_);
if (lean_obj_tag(v___x_1923_) == 1)
{
lean_object* v_val_1924_; lean_object* v_fst_1925_; lean_object* v_snd_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1989_; 
lean_dec(v___x_1918_);
lean_dec(v___x_1917_);
lean_del_object(v___x_1915_);
v_val_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_val_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v_fst_1925_ = lean_ctor_get(v_val_1924_, 0);
v_snd_1926_ = lean_ctor_get(v_val_1924_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_val_1924_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1928_ = v_val_1924_;
v_isShared_1929_ = v_isSharedCheck_1989_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_snd_1926_);
lean_inc(v_fst_1925_);
lean_dec(v_val_1924_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1989_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1987_; lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Syntax_getPos_x3f(v_fst_1925_, v___x_1920_);
if (lean_obj_tag(v___x_1988_) == 0)
{
v___y_1987_ = v___x_1921_;
goto v___jp_1986_;
}
else
{
lean_dec_ref_known(v___x_1988_, 1);
v___y_1987_ = v___x_1920_;
goto v___jp_1986_;
}
v___jp_1930_:
{
lean_object* v___x_1936_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v_snd_1886_);
lean_ctor_set(v___x_1928_, 0, v_fst_1885_);
v___x_1936_ = v___x_1928_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_fst_1885_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1886_);
v___x_1936_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
size_t v_sz_1937_; size_t v___x_1938_; lean_object* v___x_1939_; 
v_sz_1937_ = lean_array_size(v___y_1932_);
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1919_, v_fst_1925_, v_snd_1926_, v___y_1931_, v___y_1932_, v_sz_1937_, v___x_1938_, v___x_1936_);
lean_dec_ref(v___y_1932_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v_fst_1941_; lean_object* v_snd_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v_fst_1941_ = lean_ctor_get(v_a_1940_, 0);
v_snd_1942_ = lean_ctor_get(v_a_1940_, 1);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_a_1940_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v_a_1940_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_snd_1942_);
lean_inc(v_fst_1941_);
lean_dec(v_a_1940_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_fst_1941_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_snd_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v_a_1897_ = v___x_1947_;
goto v___jp_1896_;
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_del_object(v___x_1888_);
lean_dec(v_cmd_1869_);
v_a_1950_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1939_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1939_);
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
v___jp_1959_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
lean_inc_ref(v___x_1919_);
v___x_1960_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1919_);
v___x_1961_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1894_);
v___x_1962_ = lean_array_get_size(v___x_1961_);
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = lean_nat_dec_eq(v___x_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
v___y_1931_ = v___x_1960_;
v___y_1932_ = v___x_1961_;
v___y_1933_ = v___y_1876_;
v___y_1934_ = v___y_1877_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_scopes_1970_; lean_object* v___x_1971_; lean_object* v_opts_1972_; uint8_t v_hasTrace_1973_; 
v___x_1965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1966_ = l_Lean_inheritedTraceOptions;
v___x_1967_ = lean_st_ref_get(v___x_1966_);
v___x_1968_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1969_ = lean_st_ref_get(v___y_1877_);
v_scopes_1970_ = lean_ctor_get(v___x_1969_, 2);
lean_inc(v_scopes_1970_);
lean_dec(v___x_1969_);
v___x_1971_ = l_List_head_x21___redArg(v___x_1968_, v_scopes_1970_);
lean_dec(v_scopes_1970_);
v_opts_1972_ = lean_ctor_get(v___x_1971_, 1);
lean_inc_ref(v_opts_1972_);
lean_dec(v___x_1971_);
v_hasTrace_1973_ = lean_ctor_get_uint8(v_opts_1972_, sizeof(void*)*1);
if (v_hasTrace_1973_ == 0)
{
lean_dec_ref(v_opts_1972_);
lean_dec(v___x_1967_);
v___y_1931_ = v___x_1960_;
v___y_1932_ = v___x_1961_;
v___y_1933_ = v___y_1876_;
v___y_1934_ = v___y_1877_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1974_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1975_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1967_, v_opts_1972_, v___x_1974_);
lean_dec_ref(v_opts_1972_);
lean_dec(v___x_1967_);
if (v___x_1975_ == 0)
{
v___y_1931_ = v___x_1960_;
v___y_1932_ = v___x_1961_;
v___y_1933_ = v___y_1876_;
v___y_1934_ = v___y_1877_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1977_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1965_, v___x_1976_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_dec_ref_known(v___x_1977_, 1);
v___y_1931_ = v___x_1960_;
v___y_1932_ = v___x_1961_;
v___y_1933_ = v___y_1876_;
v___y_1934_ = v___y_1877_;
goto v___jp_1930_;
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v___x_1961_);
lean_dec(v___x_1960_);
lean_del_object(v___x_1928_);
lean_dec(v_snd_1926_);
lean_dec(v_fst_1925_);
lean_dec_ref_known(v___x_1919_, 2);
lean_del_object(v___x_1888_);
lean_dec(v_snd_1886_);
lean_dec(v_fst_1885_);
lean_dec(v_cmd_1869_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
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
}
}
v___jp_1986_:
{
if (v_onUnsolved_1870_ == 0)
{
if (v___y_1871_ == 0)
{
lean_del_object(v___x_1928_);
lean_dec(v_snd_1926_);
lean_dec(v_fst_1925_);
lean_dec_ref_known(v___x_1919_, 2);
goto v___jp_1904_;
}
else
{
if (v___y_1987_ == 0)
{
lean_del_object(v___x_1928_);
lean_dec(v_snd_1926_);
lean_dec(v_fst_1925_);
lean_dec_ref_known(v___x_1919_, 2);
goto v___jp_1904_;
}
else
{
lean_del_object(v___x_1883_);
goto v___jp_1959_;
}
}
}
else
{
lean_del_object(v___x_1883_);
goto v___jp_1959_;
}
}
}
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v_scopes_1995_; lean_object* v___x_1996_; lean_object* v_opts_1997_; uint8_t v_hasTrace_1998_; 
lean_dec(v___x_1923_);
lean_dec_ref_known(v___x_1919_, 2);
lean_del_object(v___x_1883_);
v___x_1990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1991_ = l_Lean_inheritedTraceOptions;
v___x_1992_ = lean_st_ref_get(v___x_1991_);
v___x_1993_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1994_ = lean_st_ref_get(v___y_1877_);
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
lean_dec(v___x_1918_);
lean_dec(v___x_1917_);
lean_del_object(v___x_1915_);
goto v___jp_1908_;
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
lean_dec(v___x_1918_);
lean_dec(v___x_1917_);
lean_del_object(v___x_1915_);
goto v___jp_1908_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2001_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_2002_ = l_Nat_reprFast(v___x_1917_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set_tag(v___x_1915_, 3);
lean_ctor_set(v___x_1915_, 0, v___x_2002_);
v___x_2004_ = v___x_1915_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2005_ = l_Lean_MessageData_ofFormat(v___x_2004_);
v___x_2006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2001_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l_Nat_reprFast(v___x_1918_);
v___x_2010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
v___x_2011_ = l_Lean_MessageData_ofFormat(v___x_2010_);
v___x_2012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2008_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1990_, v___x_2014_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_dec_ref_known(v___x_2015_, 1);
goto v___jp_1908_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_del_object(v___x_1888_);
lean_dec(v_snd_1886_);
lean_dec(v_fst_1885_);
lean_dec(v_cmd_1869_);
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
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
lean_object* v___x_2026_; 
lean_dec(v_endPos_1892_);
lean_del_object(v___x_1883_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_fst_1885_);
lean_ctor_set(v___x_2026_, 1, v_snd_1886_);
v_a_1897_ = v___x_2026_;
goto v___jp_1896_;
}
}
}
else
{
lean_object* v___x_2027_; 
lean_dec(v_endPos_1892_);
lean_del_object(v___x_1883_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_fst_1885_);
lean_ctor_set(v___x_2027_, 1, v_snd_1886_);
v_a_1897_ = v___x_2027_;
goto v___jp_1896_;
}
v___jp_1896_:
{
lean_object* v___x_1899_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v_a_1897_);
lean_ctor_set(v___x_1888_, 0, v___x_1895_);
v___x_1899_ = v___x_1888_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_a_1897_);
v___x_1899_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = ((size_t)1ULL);
v___x_1901_ = lean_usize_add(v_i_1874_, v___x_1900_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1867_, v_val_1868_, v_cmd_1869_, v_onUnsolved_1870_, v___y_1871_, v_as_1872_, v_sz_1873_, v___x_1901_, v___x_1899_, v___y_1876_, v___y_1877_);
return v___x_1902_;
}
}
v___jp_1904_:
{
lean_object* v___x_1906_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v_snd_1886_);
lean_ctor_set(v___x_1883_, 0, v_fst_1885_);
v___x_1906_ = v___x_1883_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_fst_1885_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_snd_1886_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v_a_1897_ = v___x_1906_;
goto v___jp_1896_;
}
}
v___jp_1908_:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_fst_1885_);
lean_ctor_set(v___x_1909_, 1, v_snd_1886_);
v_a_1897_ = v___x_1909_;
goto v___jp_1896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11___boxed(lean_object* v___x_2031_, lean_object* v_val_2032_, lean_object* v_cmd_2033_, lean_object* v_onUnsolved_2034_, lean_object* v___y_2035_, lean_object* v_as_2036_, lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_b_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v_onUnsolved_boxed_2043_; uint8_t v___y_13288__boxed_2044_; size_t v_sz_boxed_2045_; size_t v_i_boxed_2046_; lean_object* v_res_2047_; 
v_onUnsolved_boxed_2043_ = lean_unbox(v_onUnsolved_2034_);
v___y_13288__boxed_2044_ = lean_unbox(v___y_2035_);
v_sz_boxed_2045_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2046_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2031_, v_val_2032_, v_cmd_2033_, v_onUnsolved_boxed_2043_, v___y_13288__boxed_2044_, v_as_2036_, v_sz_boxed_2045_, v_i_boxed_2046_, v_b_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v_as_2036_);
lean_dec_ref(v_val_2032_);
lean_dec_ref(v___x_2031_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(lean_object* v_init_2048_, lean_object* v___x_2049_, lean_object* v_val_2050_, lean_object* v_cmd_2051_, uint8_t v_onUnsolved_2052_, uint8_t v___y_2053_, lean_object* v_n_2054_, lean_object* v_b_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
if (lean_obj_tag(v_n_2054_) == 0)
{
lean_object* v_cs_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; size_t v_sz_2062_; size_t v___x_2063_; lean_object* v___x_2064_; 
v_cs_2059_ = lean_ctor_get(v_n_2054_, 0);
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v_b_2055_);
v_sz_2062_ = lean_array_size(v_cs_2059_);
v___x_2063_ = ((size_t)0ULL);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2048_, v___x_2049_, v_val_2050_, v_cmd_2051_, v_onUnsolved_2052_, v___y_2053_, v_cs_2059_, v_sz_2062_, v___x_2063_, v___x_2061_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2079_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2079_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2079_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_fst_2069_; 
v_fst_2069_ = lean_ctor_get(v_a_2065_, 0);
if (lean_obj_tag(v_fst_2069_) == 0)
{
lean_object* v_snd_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v_snd_2070_ = lean_ctor_get(v_a_2065_, 1);
lean_inc(v_snd_2070_);
lean_dec(v_a_2065_);
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_snd_2070_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2071_);
v___x_2073_ = v___x_2067_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
else
{
lean_object* v_val_2075_; lean_object* v___x_2077_; 
lean_inc_ref(v_fst_2069_);
lean_dec(v_a_2065_);
v_val_2075_ = lean_ctor_get(v_fst_2069_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v_fst_2069_, 1);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v_val_2075_);
v___x_2077_ = v___x_2067_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_val_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2064_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2064_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
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
lean_object* v_vs_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; size_t v_sz_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v_vs_2088_ = lean_ctor_get(v_n_2054_, 0);
v___x_2089_ = lean_box(0);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_b_2055_);
v_sz_2091_ = lean_array_size(v_vs_2088_);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2049_, v_val_2050_, v_cmd_2051_, v_onUnsolved_2052_, v___y_2053_, v_vs_2088_, v_sz_2091_, v___x_2092_, v___x_2090_, v___y_2056_, v___y_2057_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(lean_object* v_init_2117_, lean_object* v___x_2118_, lean_object* v_val_2119_, lean_object* v_cmd_2120_, uint8_t v_onUnsolved_2121_, uint8_t v___y_2122_, lean_object* v_as_2123_, size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v___x_2130_; 
v___x_2130_ = lean_usize_dec_lt(v_i_2125_, v_sz_2124_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
lean_dec(v_cmd_2120_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_b_2126_);
return v___x_2131_;
}
else
{
lean_object* v_snd_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2166_; 
v_snd_2132_ = lean_ctor_get(v_b_2126_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_b_2126_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; 
v_unused_2167_ = lean_ctor_get(v_b_2126_, 0);
lean_dec(v_unused_2167_);
v___x_2134_ = v_b_2126_;
v_isShared_2135_ = v_isSharedCheck_2166_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_snd_2132_);
lean_dec(v_b_2126_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2166_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v_a_2137_; lean_object* v___x_2138_; 
v___x_2136_ = lean_box(0);
v_a_2137_ = lean_array_uget_borrowed(v_as_2123_, v_i_2125_);
lean_inc(v_snd_2132_);
lean_inc(v_cmd_2120_);
v___x_2138_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2117_, v___x_2118_, v_val_2119_, v_cmd_2120_, v_onUnsolved_2121_, v___y_2122_, v_a_2137_, v_snd_2132_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2157_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2157_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2157_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
if (lean_obj_tag(v_a_2139_) == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
lean_dec(v_cmd_2120_);
v___x_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_a_2139_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2143_);
v___x_2145_ = v___x_2134_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_snd_2132_);
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
lean_object* v_a_2150_; lean_object* v___x_2152_; 
lean_del_object(v___x_2141_);
lean_dec(v_snd_2132_);
v_a_2150_ = lean_ctor_get(v_a_2139_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v_a_2139_, 1);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 1, v_a_2150_);
lean_ctor_set(v___x_2134_, 0, v___x_2136_);
v___x_2152_ = v___x_2134_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_a_2150_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
size_t v___x_2153_; size_t v___x_2154_; 
v___x_2153_ = ((size_t)1ULL);
v___x_2154_ = lean_usize_add(v_i_2125_, v___x_2153_);
v_i_2125_ = v___x_2154_;
v_b_2126_ = v___x_2152_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_del_object(v___x_2134_);
lean_dec(v_snd_2132_);
lean_dec(v_cmd_2120_);
v_a_2158_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2138_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2138_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10___boxed(lean_object* v_init_2168_, lean_object* v___x_2169_, lean_object* v_val_2170_, lean_object* v_cmd_2171_, lean_object* v_onUnsolved_2172_, lean_object* v___y_2173_, lean_object* v_as_2174_, lean_object* v_sz_2175_, lean_object* v_i_2176_, lean_object* v_b_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v_onUnsolved_boxed_2181_; uint8_t v___y_13589__boxed_2182_; size_t v_sz_boxed_2183_; size_t v_i_boxed_2184_; lean_object* v_res_2185_; 
v_onUnsolved_boxed_2181_ = lean_unbox(v_onUnsolved_2172_);
v___y_13589__boxed_2182_ = lean_unbox(v___y_2173_);
v_sz_boxed_2183_ = lean_unbox_usize(v_sz_2175_);
lean_dec(v_sz_2175_);
v_i_boxed_2184_ = lean_unbox_usize(v_i_2176_);
lean_dec(v_i_2176_);
v_res_2185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2168_, v___x_2169_, v_val_2170_, v_cmd_2171_, v_onUnsolved_boxed_2181_, v___y_13589__boxed_2182_, v_as_2174_, v_sz_boxed_2183_, v_i_boxed_2184_, v_b_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec_ref(v_as_2174_);
lean_dec_ref(v_val_2170_);
lean_dec_ref(v___x_2169_);
lean_dec_ref(v_init_2168_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8___boxed(lean_object* v_init_2186_, lean_object* v___x_2187_, lean_object* v_val_2188_, lean_object* v_cmd_2189_, lean_object* v_onUnsolved_2190_, lean_object* v___y_2191_, lean_object* v_n_2192_, lean_object* v_b_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
uint8_t v_onUnsolved_boxed_2197_; uint8_t v___y_13611__boxed_2198_; lean_object* v_res_2199_; 
v_onUnsolved_boxed_2197_ = lean_unbox(v_onUnsolved_2190_);
v___y_13611__boxed_2198_ = lean_unbox(v___y_2191_);
v_res_2199_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2186_, v___x_2187_, v_val_2188_, v_cmd_2189_, v_onUnsolved_boxed_2197_, v___y_13611__boxed_2198_, v_n_2192_, v_b_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v_n_2192_);
lean_dec_ref(v_val_2188_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v_init_2186_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object* v___x_2200_, lean_object* v_val_2201_, lean_object* v_cmd_2202_, uint8_t v_onUnsolved_2203_, uint8_t v___y_2204_, lean_object* v_t_2205_, lean_object* v_init_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_root_2210_; lean_object* v_tail_2211_; lean_object* v___x_2212_; 
v_root_2210_ = lean_ctor_get(v_t_2205_, 0);
v_tail_2211_ = lean_ctor_get(v_t_2205_, 1);
lean_inc(v_cmd_2202_);
lean_inc_ref(v_init_2206_);
v___x_2212_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2206_, v___x_2200_, v_val_2201_, v_cmd_2202_, v_onUnsolved_2203_, v___y_2204_, v_root_2210_, v_init_2206_, v___y_2207_, v___y_2208_);
lean_dec_ref(v_init_2206_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2249_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2249_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2249_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
if (lean_obj_tag(v_a_2213_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2219_; 
lean_dec(v_cmd_2202_);
v_a_2217_ = lean_ctor_get(v_a_2213_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v_a_2213_, 1);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v_a_2217_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; size_t v_sz_2224_; size_t v___x_2225_; lean_object* v___x_2226_; 
lean_del_object(v___x_2215_);
v_a_2221_ = lean_ctor_get(v_a_2213_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v_a_2213_, 1);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v_a_2221_);
v_sz_2224_ = lean_array_size(v_tail_2211_);
v___x_2225_ = ((size_t)0ULL);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_2200_, v_val_2201_, v_cmd_2202_, v_onUnsolved_2203_, v___y_2204_, v_tail_2211_, v_sz_2224_, v___x_2225_, v___x_2223_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2240_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2240_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2240_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_fst_2231_; 
v_fst_2231_ = lean_ctor_get(v_a_2227_, 0);
if (lean_obj_tag(v_fst_2231_) == 0)
{
lean_object* v_snd_2232_; lean_object* v___x_2234_; 
v_snd_2232_ = lean_ctor_get(v_a_2227_, 1);
lean_inc(v_snd_2232_);
lean_dec(v_a_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v_snd_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_snd_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2238_; 
lean_inc_ref(v_fst_2231_);
lean_dec(v_a_2227_);
v_val_2236_ = lean_ctor_get(v_fst_2231_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v_fst_2231_, 1);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v_val_2236_);
v___x_2238_ = v___x_2229_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_val_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_a_2241_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2226_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2226_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_cmd_2202_);
v_a_2250_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2212_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2212_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object* v___x_2258_, lean_object* v_val_2259_, lean_object* v_cmd_2260_, lean_object* v_onUnsolved_2261_, lean_object* v___y_2262_, lean_object* v_t_2263_, lean_object* v_init_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
uint8_t v_onUnsolved_boxed_2268_; uint8_t v___y_13802__boxed_2269_; lean_object* v_res_2270_; 
v_onUnsolved_boxed_2268_ = lean_unbox(v_onUnsolved_2261_);
v___y_13802__boxed_2269_ = lean_unbox(v___y_2262_);
v_res_2270_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2258_, v_val_2259_, v_cmd_2260_, v_onUnsolved_boxed_2268_, v___y_13802__boxed_2269_, v_t_2263_, v_init_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_t_2263_);
lean_dec_ref(v_val_2259_);
lean_dec_ref(v___x_2258_);
return v_res_2270_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_unsigned_to_nat(16u);
v___x_2273_ = lean_mk_array(v___x_2272_, v___x_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v___x_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2280_, lean_object* v_opts_2281_, lean_object* v_tree_2282_, lean_object* v_msgs_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; uint8_t v___y_2291_; uint8_t v___y_2292_; uint8_t v___y_2319_; uint8_t v___y_2320_; lean_object* v_acc_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___f_2325_; uint8_t v___y_2327_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___f_2325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2334_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2335_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2281_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2337_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2281_, v___x_2336_);
v___y_2327_ = v___x_2337_;
goto v___jp_2326_;
}
else
{
v___y_2327_ = v___x_2335_;
goto v___jp_2326_;
}
v___jp_2287_:
{
uint8_t v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = 1;
v___x_2294_ = l_Lean_Syntax_getRange_x3f(v_cmd_2280_, v___x_2293_);
if (lean_obj_tag(v___x_2294_) == 1)
{
lean_object* v_val_2295_; lean_object* v_fileMap_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_val_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v_fileMap_2296_ = lean_ctor_get(v___y_2290_, 1);
v___x_2297_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___y_2288_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v_fileMap_2296_, v_val_2295_, v_cmd_2280_, v___y_2291_, v___y_2292_, v_msgs_2283_, v___x_2298_, v___y_2290_, v___y_2289_);
lean_dec(v_val_2295_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_fst_2304_; lean_object* v___x_2306_; 
v_fst_2304_ = lean_ctor_get(v_a_2300_, 0);
lean_inc(v_fst_2304_);
lean_dec(v_a_2300_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v_fst_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_fst_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
v_a_2309_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2299_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2299_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
else
{
lean_object* v___x_2317_; 
lean_dec(v___x_2294_);
lean_dec(v_cmd_2280_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___y_2288_);
return v___x_2317_;
}
}
v___jp_2318_:
{
if (v___y_2319_ == 0)
{
if (v___y_2320_ == 0)
{
lean_object* v___x_2324_; 
lean_dec(v_cmd_2280_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_acc_2321_);
return v___x_2324_;
}
else
{
v___y_2288_ = v_acc_2321_;
v___y_2289_ = v___y_2323_;
v___y_2290_ = v___y_2322_;
v___y_2291_ = v___y_2319_;
v___y_2292_ = v___y_2320_;
goto v___jp_2287_;
}
}
else
{
v___y_2288_ = v_acc_2321_;
v___y_2289_ = v___y_2323_;
v___y_2290_ = v___y_2322_;
v___y_2291_ = v___y_2319_;
v___y_2292_ = v___y_2320_;
goto v___jp_2287_;
}
}
v___jp_2326_:
{
lean_object* v___x_2328_; uint8_t v_onUnsolved_2329_; lean_object* v___x_2330_; uint8_t v_onSorry_2331_; lean_object* v_acc_2332_; 
v___x_2328_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2329_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2281_, v___x_2328_);
v___x_2330_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2331_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2281_, v___x_2330_);
v_acc_2332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2331_ == 0)
{
lean_dec_ref(v_tree_2282_);
v___y_2319_ = v_onUnsolved_2329_;
v___y_2320_ = v___y_2327_;
v_acc_2321_ = v_acc_2332_;
v___y_2322_ = v_a_2284_;
v___y_2323_ = v_a_2285_;
goto v___jp_2318_;
}
else
{
lean_object* v_acc_2333_; 
v_acc_2333_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2325_, v_acc_2332_, v_tree_2282_);
v___y_2319_ = v_onUnsolved_2329_;
v___y_2320_ = v___y_2327_;
v_acc_2321_ = v_acc_2333_;
v___y_2322_ = v_a_2284_;
v___y_2323_ = v_a_2285_;
goto v___jp_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2338_, lean_object* v_opts_2339_, lean_object* v_tree_2340_, lean_object* v_msgs_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2338_, v_opts_2339_, v_tree_2340_, v_msgs_2341_, v_a_2342_, v_a_2343_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec_ref(v_msgs_2341_);
lean_dec_ref(v_opts_2339_);
return v_res_2345_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2346_, lean_object* v_m_2347_, lean_object* v_a_2348_){
_start:
{
uint8_t v___x_2349_; 
v___x_2349_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2347_, v_a_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object* v_00_u03b2_2350_, lean_object* v_m_2351_, lean_object* v_a_2352_){
_start:
{
uint8_t v_res_2353_; lean_object* v_r_2354_; 
v_res_2353_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(v_00_u03b2_2350_, v_m_2351_, v_a_2352_);
lean_dec_ref(v_a_2352_);
lean_dec_ref(v_m_2351_);
v_r_2354_ = lean_box(v_res_2353_);
return v_r_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v_00_u03b2_2355_, lean_object* v_m_2356_, lean_object* v_a_2357_, lean_object* v_b_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_2356_, v_a_2357_, v_b_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v___x_2360_, lean_object* v_fst_2361_, lean_object* v_snd_2362_, lean_object* v___x_2363_, lean_object* v_as_2364_, size_t v_sz_2365_, size_t v_i_2366_, lean_object* v_b_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_2360_, v_fst_2361_, v_snd_2362_, v___x_2363_, v_as_2364_, v_sz_2365_, v_i_2366_, v_b_2367_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v___x_2372_, lean_object* v_fst_2373_, lean_object* v_snd_2374_, lean_object* v___x_2375_, lean_object* v_as_2376_, lean_object* v_sz_2377_, lean_object* v_i_2378_, lean_object* v_b_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
size_t v_sz_boxed_2383_; size_t v_i_boxed_2384_; lean_object* v_res_2385_; 
v_sz_boxed_2383_ = lean_unbox_usize(v_sz_2377_);
lean_dec(v_sz_2377_);
v_i_boxed_2384_ = lean_unbox_usize(v_i_2378_);
lean_dec(v_i_2378_);
v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2372_, v_fst_2373_, v_snd_2374_, v___x_2375_, v_as_2376_, v_sz_boxed_2383_, v_i_boxed_2384_, v_b_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec_ref(v_as_2376_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(lean_object* v_msgData_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_2386_, v___y_2388_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___boxed(lean_object* v_msgData_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(v_msgData_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2395_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_object* v_00_u03b2_2396_, lean_object* v_a_2397_, lean_object* v_x_2398_){
_start:
{
uint8_t v___x_2399_; 
v___x_2399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_2397_, v_x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2400_, lean_object* v_a_2401_, lean_object* v_x_2402_){
_start:
{
uint8_t v_res_2403_; lean_object* v_r_2404_; 
v_res_2403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(v_00_u03b2_2400_, v_a_2401_, v_x_2402_);
lean_dec(v_x_2402_);
lean_dec_ref(v_a_2401_);
v_r_2404_ = lean_box(v_res_2403_);
return v_r_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3(lean_object* v_00_u03b2_2405_, lean_object* v_data_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_data_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2408_, lean_object* v_i_2409_, lean_object* v_source_2410_, lean_object* v_target_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v_i_2409_, v_source_2410_, v_target_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2413_, lean_object* v_x_2414_, lean_object* v_x_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_x_2414_, v_x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
v___x_2425_ = lean_apply_7(v_x_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, lean_box(0));
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___f_2444_; lean_object* v___x_2445_; 
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2444_, 0, v_x_2436_);
lean_closure_set(v___f_2444_, 1, v___y_2437_);
lean_closure_set(v___f_2444_, 2, v___y_2438_);
v___x_2445_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2435_, v___f_2444_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
if (lean_obj_tag(v___x_2445_) == 0)
{
return v___x_2445_;
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2454_, lean_object* v_x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2454_, v_x_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2464_, lean_object* v_mvarId_2465_, lean_object* v_x_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2465_, v_x_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2475_, lean_object* v_mvarId_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2475_, v_mvarId_2476_, v_x_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
return v_res_2527_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2528_, lean_object* v_x_2529_){
_start:
{
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2530_, lean_object* v_x_2531_){
_start:
{
uint8_t v___x_10972__boxed_2532_; uint8_t v_res_2533_; lean_object* v_r_2534_; 
v___x_10972__boxed_2532_ = lean_unbox(v___x_2530_);
v_res_2533_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_10972__boxed_2532_, v_x_2531_);
lean_dec(v_x_2531_);
v_r_2534_ = lean_box(v_res_2533_);
return v_r_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v_env_2542_; uint8_t v___x_2543_; lean_object* v_env_2544_; lean_object* v___x_2545_; lean_object* v_toCold_2546_; lean_object* v_mctx_2547_; lean_object* v_lctx_2548_; lean_object* v_options_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2541_ = lean_st_ref_get(v___y_2539_);
v_env_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc_ref(v_env_2542_);
lean_dec(v___x_2541_);
v___x_2543_ = 0;
v_env_2544_ = l_Lean_Environment_setRecordingDeps(v_env_2542_, v___x_2543_);
v___x_2545_ = lean_st_ref_get(v___y_2537_);
v_toCold_2546_ = lean_ctor_get(v___y_2538_, 0);
v_mctx_2547_ = lean_ctor_get(v___x_2545_, 0);
lean_inc_ref(v_mctx_2547_);
lean_dec(v___x_2545_);
v_lctx_2548_ = lean_ctor_get(v___y_2536_, 2);
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
lean_ctor_set(v___x_2551_, 1, v_msgData_2535_);
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
lean_object* v_ref_2567_; lean_object* v___x_2568_; lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2614_; 
v_ref_2567_ = lean_ctor_get(v___y_2564_, 2);
v___x_2568_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2614_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2614_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v_traceState_2574_; lean_object* v_env_2575_; lean_object* v_nextMacroScope_2576_; lean_object* v_ngen_2577_; lean_object* v_auxDeclNGen_2578_; lean_object* v_cache_2579_; lean_object* v_recordedDeps_2580_; lean_object* v_messages_2581_; lean_object* v_infoState_2582_; lean_object* v_snapshotTasks_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2613_; 
v___x_2573_ = lean_st_ref_take(v___y_2565_);
v_traceState_2574_ = lean_ctor_get(v___x_2573_, 4);
v_env_2575_ = lean_ctor_get(v___x_2573_, 0);
v_nextMacroScope_2576_ = lean_ctor_get(v___x_2573_, 1);
v_ngen_2577_ = lean_ctor_get(v___x_2573_, 2);
v_auxDeclNGen_2578_ = lean_ctor_get(v___x_2573_, 3);
v_cache_2579_ = lean_ctor_get(v___x_2573_, 5);
v_recordedDeps_2580_ = lean_ctor_get(v___x_2573_, 6);
v_messages_2581_ = lean_ctor_get(v___x_2573_, 7);
v_infoState_2582_ = lean_ctor_get(v___x_2573_, 8);
v_snapshotTasks_2583_ = lean_ctor_get(v___x_2573_, 9);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2585_ = v___x_2573_;
v_isShared_2586_ = v_isSharedCheck_2613_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_snapshotTasks_2583_);
lean_inc(v_infoState_2582_);
lean_inc(v_messages_2581_);
lean_inc(v_recordedDeps_2580_);
lean_inc(v_cache_2579_);
lean_inc(v_traceState_2574_);
lean_inc(v_auxDeclNGen_2578_);
lean_inc(v_ngen_2577_);
lean_inc(v_nextMacroScope_2576_);
lean_inc(v_env_2575_);
lean_dec(v___x_2573_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2613_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
uint64_t v_tid_2587_; lean_object* v_traces_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2612_; 
v_tid_2587_ = lean_ctor_get_uint64(v_traceState_2574_, sizeof(void*)*1);
v_traces_2588_ = lean_ctor_get(v_traceState_2574_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_traceState_2574_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2590_ = v_traceState_2574_;
v_isShared_2591_ = v_isSharedCheck_2612_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_traces_2588_);
lean_dec(v_traceState_2574_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2612_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; double v___x_2594_; uint8_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2592_ = lean_box(0);
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2595_ = 0;
v___x_2596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2597_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2597_, 0, v_cls_2560_);
lean_ctor_set(v___x_2597_, 1, v___x_2593_);
lean_ctor_set(v___x_2597_, 2, v___x_2596_);
lean_ctor_set_float(v___x_2597_, sizeof(void*)*3, v___x_2594_);
lean_ctor_set_float(v___x_2597_, sizeof(void*)*3 + 8, v___x_2594_);
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*3 + 16, v___x_2595_);
v___x_2598_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2599_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v_a_2569_);
lean_ctor_set(v___x_2599_, 2, v___x_2598_);
lean_inc(v_ref_2567_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v_ref_2567_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = l_Lean_PersistentArray_push___redArg(v_traces_2588_, v___x_2600_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2601_);
v___x_2603_ = v___x_2590_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2601_);
lean_ctor_set_uint64(v_reuseFailAlloc_2611_, sizeof(void*)*1, v_tid_2587_);
v___x_2603_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2605_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 4, v___x_2603_);
v___x_2605_ = v___x_2585_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_env_2575_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_nextMacroScope_2576_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_ngen_2577_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_auxDeclNGen_2578_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2610_, 5, v_cache_2579_);
lean_ctor_set(v_reuseFailAlloc_2610_, 6, v_recordedDeps_2580_);
lean_ctor_set(v_reuseFailAlloc_2610_, 7, v_messages_2581_);
lean_ctor_set(v_reuseFailAlloc_2610_, 8, v_infoState_2582_);
lean_ctor_set(v_reuseFailAlloc_2610_, 9, v_snapshotTasks_2583_);
v___x_2605_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2606_ = lean_st_ref_put(v___y_2565_, v___x_2605_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2592_);
v___x_2608_ = v___x_2571_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2592_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2615_, lean_object* v_msg_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2615_, v_msg_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2622_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2626_, lean_object* v___f_2627_, lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; lean_object* v_a_2639_; lean_object* v___y_2643_; lean_object* v___x_2657_; 
v___x_2637_ = lean_st_mk_ref(v___x_2626_);
v___x_2657_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2637_, v___y_2631_, v___y_2633_, v___y_2635_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2629_, v___x_2628_, v___x_2637_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; 
lean_dec(v_a_2658_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___f_2627_);
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v_a_2639_ = v_a_2660_;
goto v___jp_2638_;
}
else
{
lean_object* v_a_2661_; uint8_t v___x_2662_; 
v_a_2661_ = lean_ctor_get(v___x_2659_, 0);
v___x_2662_ = l_Lean_Exception_isInterrupt(v_a_2661_);
if (v___x_2662_ == 0)
{
uint8_t v___x_2663_; 
lean_inc(v_a_2661_);
v___x_2663_ = l_Lean_Exception_isRuntime(v_a_2661_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2664_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2658_, v___x_2663_, v___x_2637_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2693_; 
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2664_, 0);
lean_dec(v_unused_2694_);
v___x_2666_ = v___x_2664_;
v_isShared_2667_ = v_isSharedCheck_2693_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v___x_2664_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2693_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; 
lean_inc(v_a_2661_);
v___x_2668_ = l_Lean_Exception_isMaxRecDepth(v_a_2661_);
if (v___x_2668_ == 0)
{
lean_object* v_toCold_2669_; lean_object* v_options_2670_; uint8_t v_hasTrace_2671_; 
lean_del_object(v___x_2666_);
v_toCold_2669_ = lean_ctor_get(v___y_2634_, 0);
v_options_2670_ = lean_ctor_get(v_toCold_2669_, 2);
v_hasTrace_2671_ = lean_ctor_get_uint8(v_options_2670_, sizeof(void*)*1);
if (v_hasTrace_2671_ == 0)
{
lean_dec(v_a_2661_);
goto v___jp_2654_;
}
else
{
lean_object* v_inheritedTraceOptions_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_inheritedTraceOptions_2672_ = lean_ctor_get(v_toCold_2669_, 11);
v___x_2673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2670_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_dec(v_a_2661_);
goto v___jp_2654_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2676_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2677_ = l_Lean_Exception_toMessageData(v_a_2661_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2673_, v___x_2678_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
lean_inc(v___x_2637_);
v___x_2681_ = lean_apply_10(v___f_2627_, v_a_2680_, v___x_2628_, v___x_2637_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, lean_box(0));
v___y_2643_ = v___x_2681_;
goto v___jp_2642_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v___x_2637_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___f_2627_);
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
lean_dec(v___x_2637_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___f_2627_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set_tag(v___x_2666_, 1);
lean_ctor_set(v___x_2666_, 0, v_a_2661_);
v___x_2691_ = v___x_2666_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2661_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_a_2661_);
lean_dec(v___x_2637_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___f_2627_);
v_a_2695_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2664_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2664_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_dec(v_a_2658_);
lean_dec(v___x_2637_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___f_2627_);
return v___x_2659_;
}
}
else
{
lean_dec(v_a_2658_);
lean_dec(v___x_2637_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___f_2627_);
return v___x_2659_;
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v___x_2637_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v___x_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___f_2627_);
v_a_2703_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2657_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2657_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
v___jp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_st_ref_get(v___x_2637_);
lean_dec(v___x_2637_);
lean_dec(v___x_2640_);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_a_2639_);
return v___x_2641_;
}
v___jp_2642_:
{
if (lean_obj_tag(v___y_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v_a_2645_; 
v_a_2644_ = lean_ctor_get(v___y_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___y_2643_, 1);
v_a_2645_ = lean_ctor_get(v_a_2644_, 0);
lean_inc(v_a_2645_);
lean_dec(v_a_2644_);
v_a_2639_ = v_a_2645_;
goto v___jp_2638_;
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v___x_2637_);
v_a_2646_ = lean_ctor_get(v___y_2643_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___y_2643_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___y_2643_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___y_2643_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
v___jp_2654_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_box(0);
lean_inc(v___x_2637_);
v___x_2656_ = lean_apply_10(v___f_2627_, v___x_2655_, v___x_2628_, v___x_2637_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, lean_box(0));
v___y_2643_ = v___x_2656_;
goto v___jp_2642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2711_, lean_object* v___f_2712_, lean_object* v___x_2713_, lean_object* v___x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2711_, v___f_2712_, v___x_2713_, v___x_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2723_, uint8_t v___x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2723_, v___x_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2733_, lean_object* v___x_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
uint8_t v___x_11291__boxed_2742_; lean_object* v_res_2743_; 
v___x_11291__boxed_2742_ = lean_unbox(v___x_2734_);
v_res_2743_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2733_, v___x_11291__boxed_2742_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2744_, lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_ref_2751_; lean_object* v___x_2752_; lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2798_; 
v_ref_2751_ = lean_ctor_get(v___y_2748_, 2);
v___x_2752_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2798_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2798_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; lean_object* v_traceState_2758_; lean_object* v_env_2759_; lean_object* v_nextMacroScope_2760_; lean_object* v_ngen_2761_; lean_object* v_auxDeclNGen_2762_; lean_object* v_cache_2763_; lean_object* v_recordedDeps_2764_; lean_object* v_messages_2765_; lean_object* v_infoState_2766_; lean_object* v_snapshotTasks_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2797_; 
v___x_2757_ = lean_st_ref_take(v___y_2749_);
v_traceState_2758_ = lean_ctor_get(v___x_2757_, 4);
v_env_2759_ = lean_ctor_get(v___x_2757_, 0);
v_nextMacroScope_2760_ = lean_ctor_get(v___x_2757_, 1);
v_ngen_2761_ = lean_ctor_get(v___x_2757_, 2);
v_auxDeclNGen_2762_ = lean_ctor_get(v___x_2757_, 3);
v_cache_2763_ = lean_ctor_get(v___x_2757_, 5);
v_recordedDeps_2764_ = lean_ctor_get(v___x_2757_, 6);
v_messages_2765_ = lean_ctor_get(v___x_2757_, 7);
v_infoState_2766_ = lean_ctor_get(v___x_2757_, 8);
v_snapshotTasks_2767_ = lean_ctor_get(v___x_2757_, 9);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2769_ = v___x_2757_;
v_isShared_2770_ = v_isSharedCheck_2797_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_snapshotTasks_2767_);
lean_inc(v_infoState_2766_);
lean_inc(v_messages_2765_);
lean_inc(v_recordedDeps_2764_);
lean_inc(v_cache_2763_);
lean_inc(v_traceState_2758_);
lean_inc(v_auxDeclNGen_2762_);
lean_inc(v_ngen_2761_);
lean_inc(v_nextMacroScope_2760_);
lean_inc(v_env_2759_);
lean_dec(v___x_2757_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2797_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
uint64_t v_tid_2771_; lean_object* v_traces_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2796_; 
v_tid_2771_ = lean_ctor_get_uint64(v_traceState_2758_, sizeof(void*)*1);
v_traces_2772_ = lean_ctor_get(v_traceState_2758_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_traceState_2758_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2774_ = v_traceState_2758_;
v_isShared_2775_ = v_isSharedCheck_2796_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_traces_2772_);
lean_dec(v_traceState_2758_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2796_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; double v___x_2778_; uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_box(0);
v___x_2778_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2779_ = 0;
v___x_2780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2781_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2781_, 0, v_cls_2744_);
lean_ctor_set(v___x_2781_, 1, v___x_2777_);
lean_ctor_set(v___x_2781_, 2, v___x_2780_);
lean_ctor_set_float(v___x_2781_, sizeof(void*)*3, v___x_2778_);
lean_ctor_set_float(v___x_2781_, sizeof(void*)*3 + 8, v___x_2778_);
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*3 + 16, v___x_2779_);
v___x_2782_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2783_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v_a_2753_);
lean_ctor_set(v___x_2783_, 2, v___x_2782_);
lean_inc(v_ref_2751_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_ref_2751_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = l_Lean_PersistentArray_push___redArg(v_traces_2772_, v___x_2784_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2785_);
v___x_2787_ = v___x_2774_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2785_);
lean_ctor_set_uint64(v_reuseFailAlloc_2795_, sizeof(void*)*1, v_tid_2771_);
v___x_2787_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 4, v___x_2787_);
v___x_2789_ = v___x_2769_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_env_2759_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_nextMacroScope_2760_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_ngen_2761_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v_auxDeclNGen_2762_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2794_, 5, v_cache_2763_);
lean_ctor_set(v_reuseFailAlloc_2794_, 6, v_recordedDeps_2764_);
lean_ctor_set(v_reuseFailAlloc_2794_, 7, v_messages_2765_);
lean_ctor_set(v_reuseFailAlloc_2794_, 8, v_infoState_2766_);
lean_ctor_set(v_reuseFailAlloc_2794_, 9, v_snapshotTasks_2767_);
v___x_2789_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2790_ = lean_st_ref_put(v___y_2749_, v___x_2789_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2776_);
v___x_2792_ = v___x_2755_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2776_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2799_, lean_object* v_msg_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2799_, v_msg_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
return v_res_2806_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2809_ = l_Lean_stringToMessageData(v___x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v___f_2810_, lean_object* v_term_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___y_2820_; lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2811_, v___x_2812_, v___x_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v___f_2810_);
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
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2888_; 
v_a_2851_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2853_ = v___x_2841_;
v_isShared_2854_ = v_isSharedCheck_2888_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2841_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2888_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
uint8_t v___x_2855_; 
v___x_2855_ = l_Lean_Exception_isInterrupt(v_a_2851_);
if (v___x_2855_ == 0)
{
uint8_t v___x_2856_; 
lean_inc(v_a_2851_);
v___x_2856_ = l_Lean_Exception_isRuntime(v_a_2851_);
if (v___x_2856_ == 0)
{
uint8_t v___x_2857_; 
lean_inc(v_a_2851_);
v___x_2857_ = l_Lean_Exception_isMaxRecDepth(v_a_2851_);
if (v___x_2857_ == 0)
{
lean_object* v_toCold_2858_; lean_object* v_options_2859_; uint8_t v_hasTrace_2860_; 
lean_del_object(v___x_2853_);
v_toCold_2858_ = lean_ctor_get(v___y_2816_, 0);
v_options_2859_ = lean_ctor_get(v_toCold_2858_, 2);
v_hasTrace_2860_ = lean_ctor_get_uint8(v_options_2859_, sizeof(void*)*1);
if (v_hasTrace_2860_ == 0)
{
lean_dec(v_a_2851_);
goto v___jp_2838_;
}
else
{
lean_object* v_inheritedTraceOptions_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v_inheritedTraceOptions_2861_ = lean_ctor_get(v_toCold_2858_, 11);
v___x_2862_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2864_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2861_, v_options_2859_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_dec(v_a_2851_);
goto v___jp_2838_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2865_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2866_ = l_Lean_Exception_toMessageData(v_a_2851_);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2862_, v___x_2867_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = lean_apply_6(v___f_2810_, v_a_2869_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, lean_box(0));
v___y_2820_ = v___x_2870_;
goto v___jp_2819_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v___f_2810_);
v_a_2871_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2868_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2868_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
}
else
{
lean_object* v___x_2880_; 
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v___f_2810_);
if (v_isShared_2854_ == 0)
{
v___x_2880_ = v___x_2853_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2851_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
else
{
lean_object* v___x_2883_; 
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v___f_2810_);
if (v_isShared_2854_ == 0)
{
v___x_2883_ = v___x_2853_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2851_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
else
{
lean_object* v___x_2886_; 
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v___f_2810_);
if (v_isShared_2854_ == 0)
{
v___x_2886_ = v___x_2853_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2851_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
v___jp_2819_:
{
if (lean_obj_tag(v___y_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2829_; 
v_a_2821_ = lean_ctor_get(v___y_2820_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___y_2820_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2823_ = v___y_2820_;
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___y_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_a_2825_; lean_object* v___x_2827_; 
v_a_2825_ = lean_ctor_get(v_a_2821_, 0);
lean_inc(v_a_2825_);
lean_dec(v_a_2821_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v_a_2825_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
v_a_2830_ = lean_ctor_get(v___y_2820_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___y_2820_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___y_2820_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___y_2820_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
v___jp_2838_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_apply_6(v___f_2810_, v___x_2839_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, lean_box(0));
v___y_2820_ = v___x_2840_;
goto v___jp_2819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v___f_2889_, lean_object* v_term_2890_, lean_object* v___x_2891_, lean_object* v___x_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v___f_2889_, v_term_2890_, v___x_2891_, v___x_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2899_, lean_object* v_vals_2900_, lean_object* v_i_2901_, lean_object* v_k_2902_){
_start:
{
lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = lean_array_get_size(v_keys_2899_);
v___x_2904_ = lean_nat_dec_lt(v_i_2901_, v___x_2903_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; 
lean_dec(v_i_2901_);
v___x_2905_ = lean_box(0);
return v___x_2905_;
}
else
{
lean_object* v_k_x27_2906_; uint8_t v___x_2907_; 
v_k_x27_2906_ = lean_array_fget_borrowed(v_keys_2899_, v_i_2901_);
v___x_2907_ = l_Lean_instBEqMVarId_beq(v_k_2902_, v_k_x27_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_unsigned_to_nat(1u);
v___x_2909_ = lean_nat_add(v_i_2901_, v___x_2908_);
lean_dec(v_i_2901_);
v_i_2901_ = v___x_2909_;
goto _start;
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_array_fget_borrowed(v_vals_2900_, v_i_2901_);
lean_dec(v_i_2901_);
lean_inc(v___x_2911_);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2913_, lean_object* v_vals_2914_, lean_object* v_i_2915_, lean_object* v_k_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2913_, v_vals_2914_, v_i_2915_, v_k_2916_);
lean_dec(v_k_2916_);
lean_dec_ref(v_vals_2914_);
lean_dec_ref(v_keys_2913_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2918_, size_t v_x_2919_, lean_object* v_x_2920_){
_start:
{
if (lean_obj_tag(v_x_2918_) == 0)
{
lean_object* v_es_2921_; lean_object* v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v_j_2925_; lean_object* v___x_2926_; 
v_es_2921_ = lean_ctor_get(v_x_2918_, 0);
v___x_2922_ = lean_box(2);
v___x_2923_ = ((size_t)31ULL);
v___x_2924_ = lean_usize_land(v_x_2919_, v___x_2923_);
v_j_2925_ = lean_usize_to_nat(v___x_2924_);
v___x_2926_ = lean_array_get_borrowed(v___x_2922_, v_es_2921_, v_j_2925_);
lean_dec(v_j_2925_);
switch(lean_obj_tag(v___x_2926_))
{
case 0:
{
lean_object* v_key_2927_; lean_object* v_val_2928_; uint8_t v___x_2929_; 
v_key_2927_ = lean_ctor_get(v___x_2926_, 0);
v_val_2928_ = lean_ctor_get(v___x_2926_, 1);
v___x_2929_ = l_Lean_instBEqMVarId_beq(v_x_2920_, v_key_2927_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_box(0);
return v___x_2930_;
}
else
{
lean_object* v___x_2931_; 
lean_inc(v_val_2928_);
v___x_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_val_2928_);
return v___x_2931_;
}
}
case 1:
{
lean_object* v_node_2932_; size_t v___x_2933_; size_t v___x_2934_; 
v_node_2932_ = lean_ctor_get(v___x_2926_, 0);
v___x_2933_ = ((size_t)5ULL);
v___x_2934_ = lean_usize_shift_right(v_x_2919_, v___x_2933_);
v_x_2918_ = v_node_2932_;
v_x_2919_ = v___x_2934_;
goto _start;
}
default: 
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_box(0);
return v___x_2936_;
}
}
}
else
{
lean_object* v_ks_2937_; lean_object* v_vs_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_ks_2937_ = lean_ctor_get(v_x_2918_, 0);
v_vs_2938_ = lean_ctor_get(v_x_2918_, 1);
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2937_, v_vs_2938_, v___x_2939_, v_x_2920_);
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2941_, lean_object* v_x_2942_, lean_object* v_x_2943_){
_start:
{
size_t v_x_11604__boxed_2944_; lean_object* v_res_2945_; 
v_x_11604__boxed_2944_ = lean_unbox_usize(v_x_2942_);
lean_dec(v_x_2942_);
v_res_2945_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2941_, v_x_11604__boxed_2944_, v_x_2943_);
lean_dec(v_x_2943_);
lean_dec_ref(v_x_2941_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2946_, lean_object* v_x_2947_){
_start:
{
uint64_t v___x_2948_; size_t v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = l_Lean_instHashableMVarId_hash(v_x_2947_);
v___x_2949_ = lean_uint64_to_usize(v___x_2948_);
v___x_2950_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2946_, v___x_2949_, v_x_2947_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2951_, lean_object* v_x_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2951_, v_x_2952_);
lean_dec(v_x_2952_);
lean_dec_ref(v_x_2951_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_mctx_2983_; lean_object* v_env_2984_; lean_object* v_opts_2985_; lean_object* v_namingCtx_2986_; lean_object* v_goal_2987_; lean_object* v_decls_2988_; lean_object* v___x_2989_; 
v_mctx_2983_ = lean_ctor_get(v_c_2979_, 3);
lean_inc_ref(v_mctx_2983_);
v_env_2984_ = lean_ctor_get(v_c_2979_, 2);
lean_inc_ref(v_env_2984_);
v_opts_2985_ = lean_ctor_get(v_c_2979_, 4);
lean_inc_ref(v_opts_2985_);
v_namingCtx_2986_ = lean_ctor_get(v_c_2979_, 5);
lean_inc_ref(v_namingCtx_2986_);
v_goal_2987_ = lean_ctor_get(v_c_2979_, 6);
lean_inc(v_goal_2987_);
lean_dec_ref(v_c_2979_);
v_decls_2988_ = lean_ctor_get(v_mctx_2983_, 5);
v___x_2989_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_2988_, v_goal_2987_);
if (lean_obj_tag(v___x_2989_) == 1)
{
lean_object* v_val_2990_; lean_object* v_lctx_2991_; lean_object* v___f_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___f_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v_term_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; 
v_val_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_val_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v_lctx_2991_ = lean_ctor_get(v_val_2990_, 1);
lean_inc_ref(v_lctx_2991_);
lean_dec(v_val_2990_);
v___f_2992_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_2993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_2994_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_2995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_2996_ = lean_box(0);
lean_inc(v_goal_2987_);
v___x_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_goal_2987_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___f_2998_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_2998_, 0, v___x_2997_);
lean_closure_set(v___f_2998_, 1, v___f_2992_);
lean_closure_set(v___f_2998_, 2, v___x_2995_);
lean_closure_set(v___f_2998_, 3, v___x_2994_);
v___x_2999_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_2999_, 0, lean_box(0));
lean_closure_set(v___x_2999_, 1, v_goal_2987_);
lean_closure_set(v___x_2999_, 2, v___f_2998_);
v___x_3000_ = 1;
v___x_3001_ = lean_box(v___x_3000_);
v_term_3002_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3002_, 0, v___x_2999_);
lean_closure_set(v_term_3002_, 1, v___x_3001_);
v___x_3003_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3005_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3005_, 0, v___f_2993_);
lean_closure_set(v___f_3005_, 1, v_term_3002_);
lean_closure_set(v___f_3005_, 2, v___x_3003_);
lean_closure_set(v___f_3005_, 3, v___x_3004_);
v___x_3006_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2984_, v_mctx_2983_, v_lctx_2991_, v_opts_2985_, v_namingCtx_2986_, v___f_3005_, v_a_2980_, v_a_2981_);
return v___x_3006_;
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec(v___x_2989_);
lean_dec(v_goal_2987_);
lean_dec_ref(v_namingCtx_2986_);
lean_dec_ref(v_opts_2985_);
lean_dec_ref(v_env_2984_);
lean_dec_ref(v_mctx_2983_);
v___x_3007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3009_, v_a_3010_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3014_, lean_object* v_x_3015_, lean_object* v_x_3016_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3015_, v_x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3018_, lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3018_, v_x_3019_, v_x_3020_);
lean_dec(v_x_3020_);
lean_dec_ref(v_x_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3022_, lean_object* v_msg_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3022_, v_msg_3023_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3034_, lean_object* v_msg_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3034_, v_msg_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3046_, lean_object* v_x_3047_, size_t v_x_3048_, lean_object* v_x_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3047_, v_x_3048_, v_x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_, lean_object* v_x_3054_){
_start:
{
size_t v_x_11861__boxed_3055_; lean_object* v_res_3056_; 
v_x_11861__boxed_3055_ = lean_unbox_usize(v_x_3053_);
lean_dec(v_x_3053_);
v_res_3056_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3051_, v_x_3052_, v_x_11861__boxed_3055_, v_x_3054_);
lean_dec(v_x_3054_);
lean_dec_ref(v_x_3052_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3057_, lean_object* v_keys_3058_, lean_object* v_vals_3059_, lean_object* v_heq_3060_, lean_object* v_i_3061_, lean_object* v_k_3062_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3058_, v_vals_3059_, v_i_3061_, v_k_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3064_, lean_object* v_keys_3065_, lean_object* v_vals_3066_, lean_object* v_heq_3067_, lean_object* v_i_3068_, lean_object* v_k_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3064_, v_keys_3065_, v_vals_3066_, v_heq_3067_, v_i_3068_, v_k_3069_);
lean_dec(v_k_3069_);
lean_dec_ref(v_vals_3066_);
lean_dec_ref(v_keys_3065_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3073_, lean_object* v___x_3074_, lean_object* v_ref_3075_, lean_object* v_a_3076_, lean_object* v___x_3077_, lean_object* v___x_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
if (v___x_3073_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3074_);
v___x_3083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3084_ = lean_box(0);
v___x_3085_ = 4;
v___x_3086_ = l_Lean_MessageData_nil;
v___x_3087_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3075_, v_a_3076_, v___x_3082_, v___x_3083_, v___x_3084_, v___x_3085_, v___x_3086_, v___y_3079_, v___y_3080_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3088_ = lean_array_get(v___x_3077_, v_a_3076_, v___x_3078_);
lean_dec_ref(v_a_3076_);
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3074_);
v___x_3090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3091_ = lean_box(0);
v___x_3092_ = 4;
v___x_3093_ = l_Lean_MessageData_nil;
v___x_3094_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3075_, v___x_3088_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v___y_3079_, v___y_3080_);
return v___x_3094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3095_, lean_object* v___x_3096_, lean_object* v_ref_3097_, lean_object* v_a_3098_, lean_object* v___x_3099_, lean_object* v___x_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
uint8_t v___x_3507__boxed_3104_; lean_object* v_res_3105_; 
v___x_3507__boxed_3104_ = lean_unbox(v___x_3095_);
v_res_3105_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3507__boxed_3104_, v___x_3096_, v_ref_3097_, v_a_3098_, v___x_3099_, v___x_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___x_3100_);
lean_dec_ref(v___x_3099_);
return v_res_3105_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3106_, lean_object* v_x_3107_){
_start:
{
if (lean_obj_tag(v_x_3107_) == 1)
{
lean_object* v_pre_3108_; 
v_pre_3108_ = lean_ctor_get(v_x_3107_, 0);
if (lean_obj_tag(v_pre_3108_) == 0)
{
lean_object* v_str_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_str_3109_ = lean_ctor_get(v_x_3107_, 1);
v___x_3110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1));
v___x_3111_ = lean_string_dec_eq(v_str_3109_, v___x_3110_);
if (v___x_3111_ == 0)
{
return v___x_3111_;
}
else
{
return v_suppressElabErrors_3106_;
}
}
else
{
uint8_t v___x_3112_; 
v___x_3112_ = 0;
return v___x_3112_;
}
}
else
{
uint8_t v___x_3113_; 
v___x_3113_ = 0;
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3114_, lean_object* v_x_3115_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3116_; uint8_t v_res_3117_; lean_object* v_r_3118_; 
v_suppressElabErrors_boxed_3116_ = lean_unbox(v_suppressElabErrors_3114_);
v_res_3117_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3116_, v_x_3115_);
lean_dec(v_x_3115_);
v_r_3118_ = lean_box(v_res_3117_);
return v_r_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3119_, lean_object* v_msgData_3120_, uint8_t v_severity_3121_, uint8_t v_isSilent_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
uint8_t v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; uint8_t v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; uint8_t v___y_3192_; uint8_t v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; uint8_t v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3221_; uint8_t v___y_3225_; uint8_t v___y_3226_; uint8_t v___x_3241_; uint8_t v___y_3243_; uint8_t v___x_3253_; 
v___x_3241_ = 2;
v___x_3253_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3121_, v___x_3241_);
if (v___x_3253_ == 0)
{
v___y_3243_ = v___x_3253_;
goto v___jp_3242_;
}
else
{
uint8_t v___x_3254_; 
lean_inc_ref(v_msgData_3120_);
v___x_3254_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3120_);
if (v___x_3254_ == 0)
{
v___y_3243_ = v___x_3254_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_dec_ref(v_msgData_3120_);
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
return v___x_3256_;
}
}
v___jp_3126_:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lean_Elab_Command_getScope___redArg(v___y_3134_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v_currNamespace_3137_; lean_object* v___x_3138_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3135_, 1);
v_currNamespace_3137_ = lean_ctor_get(v_a_3136_, 2);
lean_inc(v_currNamespace_3137_);
lean_dec(v_a_3136_);
v___x_3138_ = l_Lean_Elab_Command_getScope___redArg(v___y_3134_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3174_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3174_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3174_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v_openDecls_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v_env_3148_; lean_object* v_messages_3149_; lean_object* v_scopes_3150_; lean_object* v_usedQuotCtxts_3151_; lean_object* v_nextMacroScope_3152_; lean_object* v_maxRecDepth_3153_; lean_object* v_ngen_3154_; lean_object* v_auxDeclNGen_3155_; lean_object* v_infoState_3156_; lean_object* v_traceState_3157_; lean_object* v_snapshotTasks_3158_; lean_object* v_prevLinterStates_3159_; lean_object* v_codeQualityEntryTasks_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3173_; 
v_openDecls_3143_ = lean_ctor_get(v_a_3139_, 3);
lean_inc(v_openDecls_3143_);
lean_dec(v_a_3139_);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v_currNamespace_3137_);
lean_ctor_set(v___x_3144_, 1, v_openDecls_3143_);
v___x_3145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v___y_3128_);
lean_inc_ref(v___y_3129_);
lean_inc_ref(v___y_3133_);
v___x_3146_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3146_, 0, v___y_3133_);
lean_ctor_set(v___x_3146_, 1, v___y_3132_);
lean_ctor_set(v___x_3146_, 2, v___y_3131_);
lean_ctor_set(v___x_3146_, 3, v___y_3129_);
lean_ctor_set(v___x_3146_, 4, v___x_3145_);
lean_ctor_set_uint8(v___x_3146_, sizeof(void*)*5, v___y_3130_);
lean_ctor_set_uint8(v___x_3146_, sizeof(void*)*5 + 1, v___y_3127_);
lean_ctor_set_uint8(v___x_3146_, sizeof(void*)*5 + 2, v_isSilent_3122_);
v___x_3147_ = lean_st_ref_take(v___y_3134_);
v_env_3148_ = lean_ctor_get(v___x_3147_, 0);
v_messages_3149_ = lean_ctor_get(v___x_3147_, 1);
v_scopes_3150_ = lean_ctor_get(v___x_3147_, 2);
v_usedQuotCtxts_3151_ = lean_ctor_get(v___x_3147_, 3);
v_nextMacroScope_3152_ = lean_ctor_get(v___x_3147_, 4);
v_maxRecDepth_3153_ = lean_ctor_get(v___x_3147_, 5);
v_ngen_3154_ = lean_ctor_get(v___x_3147_, 6);
v_auxDeclNGen_3155_ = lean_ctor_get(v___x_3147_, 7);
v_infoState_3156_ = lean_ctor_get(v___x_3147_, 8);
v_traceState_3157_ = lean_ctor_get(v___x_3147_, 9);
v_snapshotTasks_3158_ = lean_ctor_get(v___x_3147_, 10);
v_prevLinterStates_3159_ = lean_ctor_get(v___x_3147_, 11);
v_codeQualityEntryTasks_3160_ = lean_ctor_get(v___x_3147_, 12);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3162_ = v___x_3147_;
v_isShared_3163_ = v_isSharedCheck_3173_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3160_);
lean_inc(v_prevLinterStates_3159_);
lean_inc(v_snapshotTasks_3158_);
lean_inc(v_traceState_3157_);
lean_inc(v_infoState_3156_);
lean_inc(v_auxDeclNGen_3155_);
lean_inc(v_ngen_3154_);
lean_inc(v_maxRecDepth_3153_);
lean_inc(v_nextMacroScope_3152_);
lean_inc(v_usedQuotCtxts_3151_);
lean_inc(v_scopes_3150_);
lean_inc(v_messages_3149_);
lean_inc(v_env_3148_);
lean_dec(v___x_3147_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3173_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3164_ = lean_box(0);
v___x_3165_ = l_Lean_MessageLog_add(v___x_3146_, v_messages_3149_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3165_);
v___x_3167_ = v___x_3162_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_env_3148_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_scopes_3150_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_usedQuotCtxts_3151_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_nextMacroScope_3152_);
lean_ctor_set(v_reuseFailAlloc_3172_, 5, v_maxRecDepth_3153_);
lean_ctor_set(v_reuseFailAlloc_3172_, 6, v_ngen_3154_);
lean_ctor_set(v_reuseFailAlloc_3172_, 7, v_auxDeclNGen_3155_);
lean_ctor_set(v_reuseFailAlloc_3172_, 8, v_infoState_3156_);
lean_ctor_set(v_reuseFailAlloc_3172_, 9, v_traceState_3157_);
lean_ctor_set(v_reuseFailAlloc_3172_, 10, v_snapshotTasks_3158_);
lean_ctor_set(v_reuseFailAlloc_3172_, 11, v_prevLinterStates_3159_);
lean_ctor_set(v_reuseFailAlloc_3172_, 12, v_codeQualityEntryTasks_3160_);
v___x_3167_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3168_ = lean_st_ref_put(v___y_3134_, v___x_3167_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3164_);
v___x_3170_ = v___x_3141_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3164_);
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
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec(v_currNamespace_3137_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3128_);
v_a_3175_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3138_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3138_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3128_);
v_a_3183_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3135_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3135_);
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
v___jp_3191_:
{
lean_object* v_fileName_3196_; lean_object* v_fileMap_3197_; uint8_t v_suppressElabErrors_3198_; lean_object* v___x_3199_; lean_object* v___f_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3216_; 
v_fileName_3196_ = lean_ctor_get(v___y_3123_, 0);
v_fileMap_3197_ = lean_ctor_get(v___y_3123_, 1);
v_suppressElabErrors_3198_ = lean_ctor_get_uint8(v___y_3123_, sizeof(void*)*10);
v___x_3199_ = lean_box(v_suppressElabErrors_3198_);
v___f_3200_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3200_, 0, v___x_3199_);
v___x_3201_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3120_);
v___x_3202_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v___x_3201_, v___y_3124_);
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3216_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3216_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_inc_ref_n(v_fileMap_3197_, 2);
v___x_3207_ = l_Lean_FileMap_toPosition(v_fileMap_3197_, v___y_3194_);
lean_dec(v___y_3194_);
v___x_3208_ = l_Lean_FileMap_toPosition(v_fileMap_3197_, v___y_3195_);
lean_dec(v___y_3195_);
v___x_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
v___x_3210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3198_ == 0)
{
lean_del_object(v___x_3205_);
lean_dec_ref(v___f_3200_);
v___y_3127_ = v___y_3192_;
v___y_3128_ = v_a_3203_;
v___y_3129_ = v___x_3210_;
v___y_3130_ = v___y_3193_;
v___y_3131_ = v___x_3209_;
v___y_3132_ = v___x_3207_;
v___y_3133_ = v_fileName_3196_;
v___y_3134_ = v___y_3124_;
goto v___jp_3126_;
}
else
{
uint8_t v___x_3211_; 
lean_inc(v_a_3203_);
v___x_3211_ = l_Lean_MessageData_hasTag(v___f_3200_, v_a_3203_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
lean_dec_ref_known(v___x_3209_, 1);
lean_dec_ref(v___x_3207_);
lean_dec(v_a_3203_);
v___x_3212_ = lean_box(0);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3212_);
v___x_3214_ = v___x_3205_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
else
{
lean_del_object(v___x_3205_);
v___y_3127_ = v___y_3192_;
v___y_3128_ = v_a_3203_;
v___y_3129_ = v___x_3210_;
v___y_3130_ = v___y_3193_;
v___y_3131_ = v___x_3209_;
v___y_3132_ = v___x_3207_;
v___y_3133_ = v_fileName_3196_;
v___y_3134_ = v___y_3124_;
goto v___jp_3126_;
}
}
}
}
v___jp_3217_:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_Syntax_getTailPos_x3f(v___y_3219_, v___y_3220_);
lean_dec(v___y_3219_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_inc(v___y_3221_);
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3221_;
v___y_3195_ = v___y_3221_;
goto v___jp_3191_;
}
else
{
lean_object* v_val_3223_; 
v_val_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_val_3223_);
lean_dec_ref_known(v___x_3222_, 1);
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3221_;
v___y_3195_ = v_val_3223_;
goto v___jp_3191_;
}
}
v___jp_3224_:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_Elab_Command_getRef___redArg(v___y_3123_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v_ref_3229_; lean_object* v___x_3230_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3227_, 1);
v_ref_3229_ = l_Lean_replaceRef(v_ref_3119_, v_a_3228_);
lean_dec(v_a_3228_);
v___x_3230_ = l_Lean_Syntax_getPos_x3f(v_ref_3229_, v___y_3225_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_unsigned_to_nat(0u);
v___y_3218_ = v___y_3226_;
v___y_3219_ = v_ref_3229_;
v___y_3220_ = v___y_3225_;
v___y_3221_ = v___x_3231_;
goto v___jp_3217_;
}
else
{
lean_object* v_val_3232_; 
v_val_3232_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_val_3232_);
lean_dec_ref_known(v___x_3230_, 1);
v___y_3218_ = v___y_3226_;
v___y_3219_ = v_ref_3229_;
v___y_3220_ = v___y_3225_;
v___y_3221_ = v_val_3232_;
goto v___jp_3217_;
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec_ref(v_msgData_3120_);
v_a_3233_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3227_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3227_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
v___jp_3242_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v_scopes_3246_; lean_object* v___x_3247_; lean_object* v_opts_3248_; uint8_t v___x_3249_; uint8_t v___x_3250_; 
v___x_3244_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3245_ = lean_st_ref_get(v___y_3124_);
v_scopes_3246_ = lean_ctor_get(v___x_3245_, 2);
lean_inc(v_scopes_3246_);
lean_dec(v___x_3245_);
v___x_3247_ = l_List_head_x21___redArg(v___x_3244_, v_scopes_3246_);
lean_dec(v_scopes_3246_);
v_opts_3248_ = lean_ctor_get(v___x_3247_, 1);
lean_inc_ref(v_opts_3248_);
lean_dec(v___x_3247_);
v___x_3249_ = 1;
v___x_3250_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3121_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_dec_ref(v_opts_3248_);
v___y_3225_ = v___y_3243_;
v___y_3226_ = v_severity_3121_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3251_ = l_Lean_warningAsError;
v___x_3252_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3248_, v___x_3251_);
lean_dec_ref(v_opts_3248_);
if (v___x_3252_ == 0)
{
v___y_3225_ = v___y_3243_;
v___y_3226_ = v_severity_3121_;
goto v___jp_3224_;
}
else
{
v___y_3225_ = v___y_3243_;
v___y_3226_ = v___x_3241_;
goto v___jp_3224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3257_, lean_object* v_msgData_3258_, lean_object* v_severity_3259_, lean_object* v_isSilent_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
uint8_t v_severity_boxed_3264_; uint8_t v_isSilent_boxed_3265_; lean_object* v_res_3266_; 
v_severity_boxed_3264_ = lean_unbox(v_severity_3259_);
v_isSilent_boxed_3265_ = lean_unbox(v_isSilent_3260_);
v_res_3266_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3257_, v_msgData_3258_, v_severity_boxed_3264_, v_isSilent_boxed_3265_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v_ref_3257_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3267_, lean_object* v_msgData_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
uint8_t v___x_3272_; uint8_t v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = 0;
v___x_3273_ = 0;
v___x_3274_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3267_, v_msgData_3268_, v___x_3272_, v___x_3273_, v___y_3269_, v___y_3270_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3275_, lean_object* v_msgData_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3275_, v_msgData_3276_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v_ref_3275_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3285_ = lean_string_append(v___x_3284_, v___x_3282_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3286_, v_x_3287_);
lean_dec_ref(v_x_3287_);
lean_dec_ref(v___x_3286_);
return v_res_3288_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3291_ = l_Lean_stringToMessageData(v___x_3290_);
return v___x_3291_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3294_ = l_Lean_stringToMessageData(v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3297_ = l_Lean_stringToMessageData(v___x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3298_, uint8_t v___x_3299_, lean_object* v___x_3300_, lean_object* v_insertPos_3301_, lean_object* v_cmdLine_3302_, lean_object* v_ref_3303_, size_t v_sz_3304_, size_t v_i_3305_, lean_object* v_bs_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
uint8_t v___x_3310_; 
v___x_3310_ = lean_usize_dec_lt(v_i_3305_, v_sz_3304_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; 
lean_dec_ref(v___x_3300_);
lean_dec_ref(v___x_3298_);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v_bs_3306_);
return v___x_3311_;
}
else
{
lean_object* v_v_3312_; lean_object* v___x_3313_; lean_object* v_bs_x27_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_v_3312_ = lean_array_uget(v_bs_3306_, v_i_3305_);
v___x_3313_ = lean_unsigned_to_nat(0u);
v_bs_x27_3314_ = lean_array_uset(v_bs_3306_, v_i_3305_, v___x_3313_);
lean_inc(v_v_3312_);
v___x_3315_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3315_, 0, v_v_3312_);
v___x_3316_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3315_, v___y_3307_, v___y_3308_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___f_3320_; lean_object* v___x_3321_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = l_Std_Format_defWidth;
v___x_3319_ = l_Std_Format_pretty(v_a_3317_, v___x_3318_, v___x_3313_, v___x_3313_);
lean_inc_ref(v___x_3319_);
v___f_3320_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3320_, 0, v___x_3319_);
lean_inc_ref(v___x_3298_);
v___x_3321_ = lean_string_append(v___x_3298_, v___x_3319_);
lean_dec_ref(v___x_3319_);
if (v___x_3299_ == 0)
{
goto v___jp_3322_;
}
else
{
lean_object* v___x_3333_; lean_object* v_line_3334_; lean_object* v_column_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3370_; 
lean_inc_ref(v___x_3300_);
v___x_3333_ = l_Lean_FileMap_toPosition(v___x_3300_, v_insertPos_3301_);
v_line_3334_ = lean_ctor_get(v___x_3333_, 0);
v_column_3335_ = lean_ctor_get(v___x_3333_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3337_ = v___x_3333_;
v_isShared_3338_ = v_isSharedCheck_3370_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_column_3335_);
lean_inc(v_line_3334_);
lean_dec(v___x_3333_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3370_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3339_ = lean_nat_sub(v_line_3334_, v_cmdLine_3302_);
lean_dec(v_line_3334_);
v___x_3340_ = lean_unsigned_to_nat(1u);
v___x_3341_ = lean_nat_add(v___x_3339_, v___x_3340_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3321_);
v___x_3343_ = l_String_quote(v___x_3321_);
v___x_3344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
v___x_3345_ = l_Lean_MessageData_ofFormat(v___x_3344_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set_tag(v___x_3337_, 7);
lean_ctor_set(v___x_3337_, 1, v___x_3345_);
lean_ctor_set(v___x_3337_, 0, v___x_3342_);
v___x_3347_ = v___x_3337_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3348_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = l_Nat_reprFast(v___x_3341_);
v___x_3351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
v___x_3352_ = l_Lean_MessageData_ofFormat(v___x_3351_);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3349_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l_Nat_reprFast(v_column_3335_);
v___x_3357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
v___x_3358_ = l_Lean_MessageData_ofFormat(v___x_3357_);
v___x_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3355_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3303_, v___x_3359_, v___y_3307_, v___y_3308_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_dec_ref_known(v___x_3360_, 1);
goto v___jp_3322_;
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec_ref(v___x_3321_);
lean_dec_ref(v___f_3320_);
lean_dec_ref(v_bs_x27_3314_);
lean_dec(v_v_3312_);
lean_dec_ref(v___x_3300_);
lean_dec_ref(v___x_3298_);
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
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
v___jp_3322_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; size_t v___x_3329_; size_t v___x_3330_; lean_object* v___x_3331_; 
v___x_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
v___x_3324_ = lean_box(0);
v___x_3325_ = l_Lean_MessageData_ofSyntax(v_v_3312_);
v___x_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___f_3320_);
v___x_3328_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3323_);
lean_ctor_set(v___x_3328_, 1, v___x_3324_);
lean_ctor_set(v___x_3328_, 2, v___x_3324_);
lean_ctor_set(v___x_3328_, 3, v___x_3324_);
lean_ctor_set(v___x_3328_, 4, v___x_3326_);
lean_ctor_set(v___x_3328_, 5, v___x_3327_);
v___x_3329_ = ((size_t)1ULL);
v___x_3330_ = lean_usize_add(v_i_3305_, v___x_3329_);
v___x_3331_ = lean_array_uset(v_bs_x27_3314_, v_i_3305_, v___x_3328_);
v_i_3305_ = v___x_3330_;
v_bs_3306_ = v___x_3331_;
goto _start;
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v_bs_x27_3314_);
lean_dec(v_v_3312_);
lean_dec_ref(v___x_3300_);
lean_dec_ref(v___x_3298_);
v_a_3371_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3316_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3316_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3379_, lean_object* v___x_3380_, lean_object* v___x_3381_, lean_object* v_insertPos_3382_, lean_object* v_cmdLine_3383_, lean_object* v_ref_3384_, lean_object* v_sz_3385_, lean_object* v_i_3386_, lean_object* v_bs_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
uint8_t v___x_3853__boxed_3391_; size_t v_sz_boxed_3392_; size_t v_i_boxed_3393_; lean_object* v_res_3394_; 
v___x_3853__boxed_3391_ = lean_unbox(v___x_3380_);
v_sz_boxed_3392_ = lean_unbox_usize(v_sz_3385_);
lean_dec(v_sz_3385_);
v_i_boxed_3393_ = lean_unbox_usize(v_i_3386_);
lean_dec(v_i_3386_);
v_res_3394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3379_, v___x_3853__boxed_3391_, v___x_3381_, v_insertPos_3382_, v_cmdLine_3383_, v_ref_3384_, v_sz_boxed_3392_, v_i_boxed_3393_, v_bs_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v_ref_3384_);
lean_dec(v_cmdLine_3383_);
lean_dec(v_insertPos_3382_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3395_, lean_object* v_ref_3396_, lean_object* v_insertPos_3397_, lean_object* v_suggs_3398_, lean_object* v_cmdLine_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3403_ = lean_array_get_size(v_suggs_3398_);
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_nat_dec_eq(v___x_3403_, v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v_fileMap_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v_scopes_3412_; lean_object* v___x_3413_; lean_object* v_opts_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; size_t v_sz_3417_; size_t v___x_3418_; lean_object* v___x_3419_; 
v_fileMap_3406_ = lean_ctor_get(v_a_3400_, 1);
v___x_3407_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_inc_ref_n(v_fileMap_3406_, 2);
v___x_3408_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3395_, v_fileMap_3406_);
lean_inc(v_insertPos_3397_);
v___x_3409_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3397_);
v___x_3410_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3411_ = lean_st_ref_get(v_a_3401_);
v_scopes_3412_ = lean_ctor_get(v___x_3411_, 2);
lean_inc(v_scopes_3412_);
lean_dec(v___x_3411_);
v___x_3413_ = l_List_head_x21___redArg(v___x_3410_, v_scopes_3412_);
lean_dec(v_scopes_3412_);
v_opts_3414_ = lean_ctor_get(v___x_3413_, 1);
lean_inc_ref(v_opts_3414_);
lean_dec(v___x_3413_);
v___x_3415_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3416_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3414_, v___x_3415_);
lean_dec_ref(v_opts_3414_);
v_sz_3417_ = lean_array_size(v_suggs_3398_);
v___x_3418_ = ((size_t)0ULL);
v___x_3419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3408_, v___x_3416_, v_fileMap_3406_, v_insertPos_3397_, v_cmdLine_3399_, v_ref_3396_, v_sz_3417_, v___x_3418_, v_suggs_3398_, v_a_3400_, v_a_3401_);
lean_dec(v_insertPos_3397_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; uint8_t v___x_3423_; lean_object* v___x_3424_; lean_object* v___y_3425_; lean_object* v___x_3426_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v___x_3421_ = lean_array_get_size(v_a_3420_);
v___x_3422_ = lean_unsigned_to_nat(1u);
v___x_3423_ = lean_nat_dec_eq(v___x_3421_, v___x_3422_);
v___x_3424_ = lean_box(v___x_3423_);
v___y_3425_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3425_, 0, v___x_3424_);
lean_closure_set(v___y_3425_, 1, v___x_3409_);
lean_closure_set(v___y_3425_, 2, v_ref_3396_);
lean_closure_set(v___y_3425_, 3, v_a_3420_);
lean_closure_set(v___y_3425_, 4, v___x_3407_);
lean_closure_set(v___y_3425_, 5, v___x_3404_);
v___x_3426_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3425_, v_a_3400_, v_a_3401_);
return v___x_3426_;
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v___x_3409_);
lean_dec(v_ref_3396_);
v_a_3427_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3419_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3419_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
lean_dec_ref(v_suggs_3398_);
lean_dec(v_insertPos_3397_);
lean_dec(v_ref_3396_);
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3437_, lean_object* v_ref_3438_, lean_object* v_insertPos_3439_, lean_object* v_suggs_3440_, lean_object* v_cmdLine_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3437_, v_ref_3438_, v_insertPos_3439_, v_suggs_3440_, v_cmdLine_3441_, v_a_3442_, v_a_3443_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
lean_dec(v_cmdLine_3441_);
lean_dec(v_tacticSeq_3437_);
return v_res_3445_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3446_){
_start:
{
uint8_t v___x_3447_; 
v___x_3447_ = 0;
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3448_){
_start:
{
uint8_t v_res_3449_; lean_object* v_r_3450_; 
v_res_3449_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3448_);
lean_dec(v_x_3448_);
v_r_3450_ = lean_box(v_res_3449_);
return v_r_3450_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Array_mkArray0___redArg();
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3471_, lean_object* v_ref_3472_, lean_object* v_goal_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_toCold_3482_; lean_object* v_currRecDepth_3483_; lean_object* v_ref_3484_; uint16_t v_optionFlags_3485_; uint8_t v_suppressElabErrors_3486_; uint8_t v_isRecordingDeps_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v_ref_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_toCold_3482_ = lean_ctor_get(v___y_3476_, 0);
v_currRecDepth_3483_ = lean_ctor_get(v___y_3476_, 1);
v_ref_3484_ = lean_ctor_get(v___y_3476_, 2);
v_optionFlags_3485_ = lean_ctor_get_uint16(v___y_3476_, sizeof(void*)*3);
v_suppressElabErrors_3486_ = lean_ctor_get_uint8(v___y_3476_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3487_ = lean_ctor_get_uint8(v___y_3476_, sizeof(void*)*3 + 3);
v___x_3488_ = 0;
v___x_3489_ = l_Lean_SourceInfo_fromRef(v_ref_3484_, v___x_3488_);
v___x_3490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0));
lean_inc_n(v___x_3489_, 3);
v___x_3491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
v___x_3493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3494_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5);
v___x_3495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3489_);
lean_ctor_set(v___x_3495_, 1, v___x_3493_);
lean_ctor_set(v___x_3495_, 2, v___x_3494_);
v___x_3496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7));
v___x_3497_ = l_Lean_Syntax_node1(v___x_3489_, v___x_3496_, v___x_3495_);
v___x_3498_ = l_Lean_Syntax_node2(v___x_3489_, v___x_3492_, v___x_3491_, v___x_3497_);
v___x_3499_ = lean_box(0);
v___x_3500_ = lean_box(0);
v___x_3501_ = 1;
v___x_3502_ = lean_box(1);
v___x_3503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3504_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3504_, 0, v___x_3499_);
lean_ctor_set(v___x_3504_, 1, v___x_3500_);
lean_ctor_set(v___x_3504_, 2, v___x_3499_);
lean_ctor_set(v___x_3504_, 3, v___f_3471_);
lean_ctor_set(v___x_3504_, 4, v___x_3502_);
lean_ctor_set(v___x_3504_, 5, v___x_3502_);
lean_ctor_set(v___x_3504_, 6, v___x_3499_);
lean_ctor_set(v___x_3504_, 7, v___x_3503_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8, v___x_3501_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 1, v___x_3501_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 2, v___x_3501_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 3, v___x_3501_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 4, v___x_3488_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 5, v___x_3488_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 6, v___x_3488_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 7, v___x_3488_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 8, v___x_3501_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 9, v___x_3488_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*8 + 10, v___x_3501_);
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v___x_3506_ = lean_box(0);
v_ref_3507_ = l_Lean_replaceRef(v_ref_3472_, v_ref_3484_);
lean_inc(v_currRecDepth_3483_);
lean_inc_ref(v_toCold_3482_);
v___x_3508_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3508_, 0, v_toCold_3482_);
lean_ctor_set(v___x_3508_, 1, v_currRecDepth_3483_);
lean_ctor_set(v___x_3508_, 2, v_ref_3507_);
lean_ctor_set_uint16(v___x_3508_, sizeof(void*)*3, v_optionFlags_3485_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*3 + 2, v_suppressElabErrors_3486_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*3 + 3, v_isRecordingDeps_3487_);
v___x_3509_ = l_Lean_Elab_runTactic(v_goal_3473_, v___x_3498_, v___x_3504_, v___x_3505_, v___y_3474_, v___y_3475_, v___x_3508_, v___y_3477_);
lean_dec_ref_known(v___x_3508_, 3);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3516_ == 0)
{
lean_object* v_unused_3517_; 
v_unused_3517_ = lean_ctor_get(v___x_3509_, 0);
lean_dec(v_unused_3517_);
v___x_3511_ = v___x_3509_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_dec(v___x_3509_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3506_);
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3506_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3538_; 
v_a_3518_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3520_ = v___x_3509_;
v_isShared_3521_ = v_isSharedCheck_3538_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3509_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3538_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
lean_inc(v_a_3518_);
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
uint8_t v___x_3524_; 
v___x_3524_ = l_Lean_Exception_isInterrupt(v_a_3518_);
if (v___x_3524_ == 0)
{
uint8_t v___x_3525_; 
lean_inc(v_a_3518_);
v___x_3525_ = l_Lean_Exception_isRuntime(v_a_3518_);
if (v___x_3525_ == 0)
{
uint8_t v___x_3526_; 
lean_inc(v_a_3518_);
v___x_3526_ = l_Lean_Exception_isMaxRecDepth(v_a_3518_);
if (v___x_3526_ == 0)
{
lean_object* v_options_3527_; uint8_t v_hasTrace_3528_; 
lean_dec_ref(v___x_3523_);
v_options_3527_ = lean_ctor_get(v_toCold_3482_, 2);
v_hasTrace_3528_ = lean_ctor_get_uint8(v_options_3527_, sizeof(void*)*1);
if (v_hasTrace_3528_ == 0)
{
lean_dec(v_a_3518_);
goto v___jp_3479_;
}
else
{
lean_object* v_inheritedTraceOptions_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; 
v_inheritedTraceOptions_3529_ = lean_ctor_get(v_toCold_3482_, 11);
v___x_3530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3529_, v_options_3527_, v___x_3531_);
if (v___x_3532_ == 0)
{
lean_dec(v_a_3518_);
goto v___jp_3479_;
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3533_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3534_ = l_Lean_Exception_toMessageData(v_a_3518_);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3530_, v___x_3535_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
return v___x_3536_;
}
}
}
else
{
lean_dec(v_a_3518_);
return v___x_3523_;
}
}
else
{
lean_dec(v_a_3518_);
return v___x_3523_;
}
}
else
{
lean_dec(v_a_3518_);
return v___x_3523_;
}
}
}
}
v___jp_3479_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_box(0);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3539_, lean_object* v_ref_3540_, lean_object* v_goal_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3539_, v_ref_3540_, v_goal_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v_ref_3540_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v_mctx_3553_; lean_object* v_ref_3554_; lean_object* v_env_3555_; lean_object* v_opts_3556_; lean_object* v_namingCtx_3557_; lean_object* v_goal_3558_; lean_object* v_decls_3559_; lean_object* v___x_3560_; 
v_mctx_3553_ = lean_ctor_get(v_c_3549_, 3);
lean_inc_ref(v_mctx_3553_);
v_ref_3554_ = lean_ctor_get(v_c_3549_, 1);
lean_inc(v_ref_3554_);
v_env_3555_ = lean_ctor_get(v_c_3549_, 2);
lean_inc_ref(v_env_3555_);
v_opts_3556_ = lean_ctor_get(v_c_3549_, 4);
lean_inc_ref(v_opts_3556_);
v_namingCtx_3557_ = lean_ctor_get(v_c_3549_, 5);
lean_inc_ref(v_namingCtx_3557_);
v_goal_3558_ = lean_ctor_get(v_c_3549_, 6);
lean_inc(v_goal_3558_);
lean_dec_ref(v_c_3549_);
v_decls_3559_ = lean_ctor_get(v_mctx_3553_, 5);
v___x_3560_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3559_, v_goal_3558_);
if (lean_obj_tag(v___x_3560_) == 1)
{
lean_object* v_val_3561_; lean_object* v_lctx_3562_; lean_object* v___f_3563_; lean_object* v___f_3564_; lean_object* v___x_3565_; 
v_val_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_val_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v_lctx_3562_ = lean_ctor_get(v_val_3561_, 1);
lean_inc_ref(v_lctx_3562_);
lean_dec(v_val_3561_);
v___f_3563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3564_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3564_, 0, v___f_3563_);
lean_closure_set(v___f_3564_, 1, v_ref_3554_);
lean_closure_set(v___f_3564_, 2, v_goal_3558_);
v___x_3565_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3555_, v_mctx_3553_, v_lctx_3562_, v_opts_3556_, v_namingCtx_3557_, v___f_3564_, v_a_3550_, v_a_3551_);
return v___x_3565_;
}
else
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_dec(v___x_3560_);
lean_dec(v_goal_3558_);
lean_dec_ref(v_namingCtx_3557_);
lean_dec_ref(v_opts_3556_);
lean_dec_ref(v_env_3555_);
lean_dec(v_ref_3554_);
lean_dec_ref(v_mctx_3553_);
v___x_3566_ = lean_box(0);
v___x_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
return v___x_3567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3568_, v_a_3569_, v_a_3570_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
return v_res_3572_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3573_, lean_object* v_val_3574_, lean_object* v_as_3575_, size_t v_i_3576_, size_t v_stop_3577_){
_start:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_usize_dec_eq(v_i_3576_, v_stop_3577_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v_pos_3584_; uint8_t v_severity_3585_; lean_object* v_data_3586_; lean_object* v___f_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; uint8_t v___y_3592_; 
v___x_3583_ = lean_array_uget_borrowed(v_as_3575_, v_i_3576_);
v_pos_3584_ = lean_ctor_get(v___x_3583_, 1);
v_severity_3585_ = lean_ctor_get_uint8(v___x_3583_, sizeof(void*)*5 + 1);
v_data_3586_ = lean_ctor_get(v___x_3583_, 4);
v___f_3587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
v___x_3588_ = 1;
lean_inc_ref(v_pos_3584_);
v___x_3589_ = l_Lean_FileMap_ofPosition(v___x_3573_, v_pos_3584_);
v___x_3590_ = l_Lean_Syntax_Range_contains(v_val_3574_, v___x_3589_, v___x_3588_);
lean_dec(v___x_3589_);
if (v_severity_3585_ == 2)
{
v___y_3592_ = v___x_3588_;
goto v___jp_3591_;
}
else
{
v___y_3592_ = v___x_3582_;
goto v___jp_3591_;
}
v___jp_3591_:
{
if (v___x_3590_ == 0)
{
goto v___jp_3578_;
}
else
{
if (v___y_3592_ == 0)
{
goto v___jp_3578_;
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
goto v___jp_3578_;
}
}
}
}
}
else
{
uint8_t v___x_3594_; 
v___x_3594_ = 0;
return v___x_3594_;
}
v___jp_3578_:
{
size_t v___x_3579_; size_t v___x_3580_; 
v___x_3579_ = ((size_t)1ULL);
v___x_3580_ = lean_usize_add(v_i_3576_, v___x_3579_);
v_i_3576_ = v___x_3580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3595_, lean_object* v_val_3596_, lean_object* v_as_3597_, lean_object* v_i_3598_, lean_object* v_stop_3599_){
_start:
{
size_t v_i_boxed_3600_; size_t v_stop_boxed_3601_; uint8_t v_res_3602_; lean_object* v_r_3603_; 
v_i_boxed_3600_ = lean_unbox_usize(v_i_3598_);
lean_dec(v_i_3598_);
v_stop_boxed_3601_ = lean_unbox_usize(v_stop_3599_);
lean_dec(v_stop_3599_);
v_res_3602_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3595_, v_val_3596_, v_as_3597_, v_i_boxed_3600_, v_stop_boxed_3601_);
lean_dec_ref(v_as_3597_);
lean_dec_ref(v_val_3596_);
lean_dec_ref(v___x_3595_);
v_r_3603_ = lean_box(v_res_3602_);
return v_r_3603_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3604_, lean_object* v_val_3605_, lean_object* v_x_3606_){
_start:
{
if (lean_obj_tag(v_x_3606_) == 0)
{
lean_object* v_cs_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v_cs_3607_ = lean_ctor_get(v_x_3606_, 0);
v___x_3608_ = lean_unsigned_to_nat(0u);
v___x_3609_ = lean_array_get_size(v_cs_3607_);
v___x_3610_ = lean_nat_dec_lt(v___x_3608_, v___x_3609_);
if (v___x_3610_ == 0)
{
return v___x_3610_;
}
else
{
size_t v___x_3611_; size_t v___x_3612_; uint8_t v___x_3613_; 
v___x_3611_ = ((size_t)0ULL);
v___x_3612_ = lean_usize_of_nat(v___x_3609_);
v___x_3613_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3604_, v_val_3605_, v_cs_3607_, v___x_3611_, v___x_3612_);
return v___x_3613_;
}
}
else
{
lean_object* v_vs_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; 
v_vs_3614_ = lean_ctor_get(v_x_3606_, 0);
v___x_3615_ = lean_unsigned_to_nat(0u);
v___x_3616_ = lean_array_get_size(v_vs_3614_);
v___x_3617_ = lean_nat_dec_lt(v___x_3615_, v___x_3616_);
if (v___x_3617_ == 0)
{
return v___x_3617_;
}
else
{
size_t v___x_3618_; size_t v___x_3619_; uint8_t v___x_3620_; 
v___x_3618_ = ((size_t)0ULL);
v___x_3619_ = lean_usize_of_nat(v___x_3616_);
v___x_3620_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3604_, v_val_3605_, v_vs_3614_, v___x_3618_, v___x_3619_);
return v___x_3620_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3621_, lean_object* v_val_3622_, lean_object* v_as_3623_, size_t v_i_3624_, size_t v_stop_3625_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_usize_dec_eq(v_i_3624_, v_stop_3625_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3627_ = lean_array_uget_borrowed(v_as_3623_, v_i_3624_);
v___x_3628_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3621_, v_val_3622_, v___x_3627_);
if (v___x_3628_ == 0)
{
size_t v___x_3629_; size_t v___x_3630_; 
v___x_3629_ = ((size_t)1ULL);
v___x_3630_ = lean_usize_add(v_i_3624_, v___x_3629_);
v_i_3624_ = v___x_3630_;
goto _start;
}
else
{
return v___x_3628_;
}
}
else
{
uint8_t v___x_3632_; 
v___x_3632_ = 0;
return v___x_3632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3633_, lean_object* v_val_3634_, lean_object* v_as_3635_, lean_object* v_i_3636_, lean_object* v_stop_3637_){
_start:
{
size_t v_i_boxed_3638_; size_t v_stop_boxed_3639_; uint8_t v_res_3640_; lean_object* v_r_3641_; 
v_i_boxed_3638_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_stop_boxed_3639_ = lean_unbox_usize(v_stop_3637_);
lean_dec(v_stop_3637_);
v_res_3640_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3633_, v_val_3634_, v_as_3635_, v_i_boxed_3638_, v_stop_boxed_3639_);
lean_dec_ref(v_as_3635_);
lean_dec_ref(v_val_3634_);
lean_dec_ref(v___x_3633_);
v_r_3641_ = lean_box(v_res_3640_);
return v_r_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3642_, lean_object* v_val_3643_, lean_object* v_x_3644_){
_start:
{
uint8_t v_res_3645_; lean_object* v_r_3646_; 
v_res_3645_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3642_, v_val_3643_, v_x_3644_);
lean_dec_ref(v_x_3644_);
lean_dec_ref(v_val_3643_);
lean_dec_ref(v___x_3642_);
v_r_3646_ = lean_box(v_res_3645_);
return v_r_3646_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3647_, lean_object* v_val_3648_, lean_object* v_t_3649_){
_start:
{
lean_object* v_root_3650_; lean_object* v_tail_3651_; uint8_t v___x_3652_; 
v_root_3650_ = lean_ctor_get(v_t_3649_, 0);
v_tail_3651_ = lean_ctor_get(v_t_3649_, 1);
v___x_3652_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3647_, v_val_3648_, v_root_3650_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = lean_array_get_size(v_tail_3651_);
v___x_3655_ = lean_nat_dec_lt(v___x_3653_, v___x_3654_);
if (v___x_3655_ == 0)
{
return v___x_3655_;
}
else
{
size_t v___x_3656_; size_t v___x_3657_; uint8_t v___x_3658_; 
v___x_3656_ = ((size_t)0ULL);
v___x_3657_ = lean_usize_of_nat(v___x_3654_);
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3647_, v_val_3648_, v_tail_3651_, v___x_3656_, v___x_3657_);
return v___x_3658_;
}
}
else
{
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3659_, lean_object* v_val_3660_, lean_object* v_t_3661_){
_start:
{
uint8_t v_res_3662_; lean_object* v_r_3663_; 
v_res_3662_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3659_, v_val_3660_, v_t_3661_);
lean_dec_ref(v_t_3661_);
lean_dec_ref(v_val_3660_);
lean_dec_ref(v___x_3659_);
v_r_3663_ = lean_box(v_res_3662_);
return v_r_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
uint8_t v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = 0;
v___x_3669_ = l_Lean_Syntax_getRange_x3f(v_stx_3664_, v___x_3668_);
if (lean_obj_tag(v___x_3669_) == 1)
{
lean_object* v_val_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3683_; 
v_val_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3683_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_val_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3683_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v_fileMap_3674_; lean_object* v___x_3675_; lean_object* v_messages_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v_fileMap_3674_ = lean_ctor_get(v_a_3665_, 1);
v___x_3675_ = lean_st_ref_get(v_a_3666_);
v_messages_3676_ = lean_ctor_get(v___x_3675_, 1);
lean_inc_ref(v_messages_3676_);
lean_dec(v___x_3675_);
v___x_3677_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3676_);
v___x_3678_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3674_, v_val_3670_, v___x_3677_);
lean_dec_ref(v___x_3677_);
lean_dec(v_val_3670_);
v___x_3679_ = lean_box(v___x_3678_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set_tag(v___x_3672_, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3679_);
v___x_3681_ = v___x_3672_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3679_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_dec(v___x_3669_);
v___x_3684_ = lean_box(v___x_3668_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3686_, v_a_3687_, v_a_3688_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_stx_3686_);
return v_res_3690_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3691_, lean_object* v_fileMap_3692_, lean_object* v_c_3693_){
_start:
{
lean_object* v___y_3695_; lean_object* v_kind_3699_; lean_object* v_ref_3700_; lean_object* v___y_3702_; 
v_kind_3699_ = lean_ctor_get(v_c_3693_, 0);
lean_inc(v_kind_3699_);
v_ref_3700_ = lean_ctor_get(v_c_3693_, 1);
lean_inc(v_ref_3700_);
lean_dec_ref(v_c_3693_);
if (lean_obj_tag(v_kind_3699_) == 0)
{
lean_object* v_insertPos_3718_; 
lean_dec(v_ref_3700_);
v_insertPos_3718_ = lean_ctor_get(v_kind_3699_, 1);
lean_inc(v_insertPos_3718_);
v___y_3702_ = v_insertPos_3718_;
goto v___jp_3701_;
}
else
{
uint8_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = 0;
v___x_3720_ = l_Lean_Syntax_getPos_x3f(v_ref_3700_, v___x_3719_);
lean_dec(v_ref_3700_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_unsigned_to_nat(0u);
v___y_3702_ = v___x_3721_;
goto v___jp_3701_;
}
else
{
lean_object* v_val_3722_; 
v_val_3722_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_val_3722_);
lean_dec_ref_known(v___x_3720_, 1);
v___y_3702_ = v_val_3722_;
goto v___jp_3701_;
}
}
v___jp_3694_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3696_ = l_List_lengthTR___redArg(v___y_3695_);
lean_dec(v___y_3695_);
v___x_3697_ = lean_unsigned_to_nat(1u);
v___x_3698_ = lean_nat_dec_eq(v___x_3696_, v___x_3697_);
lean_dec(v___x_3696_);
return v___x_3698_;
}
v___jp_3701_:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3692_, v_tree_3691_, v___y_3702_);
if (lean_obj_tag(v___x_3703_) == 1)
{
lean_object* v_tail_3704_; 
v_tail_3704_ = lean_ctor_get(v___x_3703_, 1);
if (lean_obj_tag(v_tail_3704_) == 0)
{
if (lean_obj_tag(v_kind_3699_) == 0)
{
lean_object* v_head_3705_; lean_object* v_tacticSeq_3706_; uint8_t v___x_3707_; lean_object* v___x_3708_; 
v_head_3705_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_head_3705_);
lean_dec_ref_known(v___x_3703_, 2);
v_tacticSeq_3706_ = lean_ctor_get(v_kind_3699_, 0);
lean_inc(v_tacticSeq_3706_);
lean_dec_ref_known(v_kind_3699_, 2);
v___x_3707_ = 0;
v___x_3708_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3706_, v___x_3707_);
lean_dec(v_tacticSeq_3706_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_tacticInfo_3709_; lean_object* v_goalsBefore_3710_; 
v_tacticInfo_3709_ = lean_ctor_get(v_head_3705_, 1);
lean_inc_ref(v_tacticInfo_3709_);
lean_dec(v_head_3705_);
v_goalsBefore_3710_ = lean_ctor_get(v_tacticInfo_3709_, 2);
lean_inc(v_goalsBefore_3710_);
lean_dec_ref(v_tacticInfo_3709_);
v___y_3695_ = v_goalsBefore_3710_;
goto v___jp_3694_;
}
else
{
lean_object* v_tacticInfo_3711_; lean_object* v_goalsAfter_3712_; 
lean_dec_ref_known(v___x_3708_, 1);
v_tacticInfo_3711_ = lean_ctor_get(v_head_3705_, 1);
lean_inc_ref(v_tacticInfo_3711_);
lean_dec(v_head_3705_);
v_goalsAfter_3712_ = lean_ctor_get(v_tacticInfo_3711_, 4);
lean_inc(v_goalsAfter_3712_);
lean_dec_ref(v_tacticInfo_3711_);
v___y_3695_ = v_goalsAfter_3712_;
goto v___jp_3694_;
}
}
else
{
lean_object* v_head_3713_; lean_object* v_tacticInfo_3714_; lean_object* v_goalsBefore_3715_; 
v_head_3713_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_head_3713_);
lean_dec_ref_known(v___x_3703_, 2);
v_tacticInfo_3714_ = lean_ctor_get(v_head_3713_, 1);
lean_inc_ref(v_tacticInfo_3714_);
lean_dec(v_head_3713_);
v_goalsBefore_3715_ = lean_ctor_get(v_tacticInfo_3714_, 2);
lean_inc(v_goalsBefore_3715_);
lean_dec_ref(v_tacticInfo_3714_);
v___y_3695_ = v_goalsBefore_3715_;
goto v___jp_3694_;
}
}
else
{
uint8_t v___x_3716_; 
lean_dec_ref_known(v___x_3703_, 2);
lean_dec(v_kind_3699_);
v___x_3716_ = 0;
return v___x_3716_;
}
}
else
{
uint8_t v___x_3717_; 
lean_dec(v___x_3703_);
lean_dec(v_kind_3699_);
v___x_3717_ = 0;
return v___x_3717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3723_, lean_object* v_fileMap_3724_, lean_object* v_c_3725_){
_start:
{
uint8_t v_res_3726_; lean_object* v_r_3727_; 
v_res_3726_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3723_, v_fileMap_3724_, v_c_3725_);
v_r_3727_ = lean_box(v_res_3726_);
return v_r_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; lean_object* v_infoState_3731_; lean_object* v_trees_3732_; lean_object* v___x_3733_; 
v___x_3730_ = lean_st_ref_get(v___y_3728_);
v_infoState_3731_ = lean_ctor_get(v___x_3730_, 8);
lean_inc_ref(v_infoState_3731_);
lean_dec(v___x_3730_);
v_trees_3732_ = lean_ctor_get(v_infoState_3731_, 2);
lean_inc_ref(v_trees_3732_);
lean_dec_ref(v_infoState_3731_);
v___x_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3733_, 0, v_trees_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3734_);
lean_dec(v___y_3734_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3738_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
return v_res_3744_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3747_ = l_Lean_stringToMessageData(v___x_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3748_, lean_object* v___x_3749_, lean_object* v___x_3750_, lean_object* v_as_3751_, size_t v_sz_3752_, size_t v_i_3753_, lean_object* v_b_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_a_3759_; uint8_t v___x_3763_; 
v___x_3763_ = lean_usize_dec_lt(v_i_3753_, v_sz_3752_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
lean_dec_ref(v___x_3749_);
lean_dec_ref(v_tree_3748_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_b_3754_);
return v___x_3764_;
}
else
{
lean_object* v___x_3765_; lean_object* v_a_3766_; uint8_t v___x_3767_; 
v___x_3765_ = lean_box(0);
v_a_3766_ = lean_array_uget_borrowed(v_as_3751_, v_i_3753_);
lean_inc(v_a_3766_);
lean_inc_ref(v___x_3749_);
lean_inc_ref(v_tree_3748_);
v___x_3767_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3748_, v___x_3749_, v_a_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v_scopes_3773_; lean_object* v___x_3774_; lean_object* v_opts_3775_; uint8_t v_hasTrace_3776_; 
v___x_3768_ = l_Lean_inheritedTraceOptions;
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3770_ = lean_st_ref_get(v___x_3768_);
v___x_3771_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3772_ = lean_st_ref_get(v___y_3756_);
v_scopes_3773_ = lean_ctor_get(v___x_3772_, 2);
lean_inc(v_scopes_3773_);
lean_dec(v___x_3772_);
v___x_3774_ = l_List_head_x21___redArg(v___x_3771_, v_scopes_3773_);
lean_dec(v_scopes_3773_);
v_opts_3775_ = lean_ctor_get(v___x_3774_, 1);
lean_inc_ref(v_opts_3775_);
lean_dec(v___x_3774_);
v_hasTrace_3776_ = lean_ctor_get_uint8(v_opts_3775_, sizeof(void*)*1);
if (v_hasTrace_3776_ == 0)
{
lean_dec_ref(v_opts_3775_);
lean_dec(v___x_3770_);
v_a_3759_ = v___x_3765_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3777_; uint8_t v___x_3778_; 
v___x_3777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3778_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3770_, v_opts_3775_, v___x_3777_);
lean_dec_ref(v_opts_3775_);
lean_dec(v___x_3770_);
if (v___x_3778_ == 0)
{
v_a_3759_ = v___x_3765_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3779_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3780_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3769_, v___x_3779_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_dec_ref_known(v___x_3780_, 1);
v_a_3759_ = v___x_3765_;
goto v___jp_3758_;
}
else
{
lean_dec_ref(v___x_3749_);
lean_dec_ref(v_tree_3748_);
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_kind_3781_; 
v_kind_3781_ = lean_ctor_get(v_a_3766_, 0);
if (lean_obj_tag(v_kind_3781_) == 0)
{
lean_object* v_ref_3782_; lean_object* v_tacticSeq_3783_; lean_object* v_insertPos_3784_; lean_object* v___x_3785_; 
v_ref_3782_ = lean_ctor_get(v_a_3766_, 1);
v_tacticSeq_3783_ = lean_ctor_get(v_kind_3781_, 0);
v_insertPos_3784_ = lean_ctor_get(v_kind_3781_, 1);
lean_inc(v_a_3766_);
v___x_3785_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3766_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
lean_inc(v_insertPos_3784_);
lean_inc(v_ref_3782_);
v___x_3787_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3783_, v_ref_3782_, v_insertPos_3784_, v_a_3786_, v___x_3750_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_dec_ref_known(v___x_3787_, 1);
v_a_3759_ = v___x_3765_;
goto v___jp_3758_;
}
else
{
lean_dec_ref(v___x_3749_);
lean_dec_ref(v_tree_3748_);
return v___x_3787_;
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v___x_3749_);
lean_dec_ref(v_tree_3748_);
v_a_3788_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3785_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3785_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
else
{
lean_object* v___x_3796_; 
lean_inc(v_a_3766_);
v___x_3796_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3766_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_dec_ref_known(v___x_3796_, 1);
v_a_3759_ = v___x_3765_;
goto v___jp_3758_;
}
else
{
lean_dec_ref(v___x_3749_);
lean_dec_ref(v_tree_3748_);
return v___x_3796_;
}
}
}
}
v___jp_3758_:
{
size_t v___x_3760_; size_t v___x_3761_; 
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_add(v_i_3753_, v___x_3760_);
v_i_3753_ = v___x_3761_;
v_b_3754_ = v_a_3759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3797_, lean_object* v___x_3798_, lean_object* v___x_3799_, lean_object* v_as_3800_, lean_object* v_sz_3801_, lean_object* v_i_3802_, lean_object* v_b_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
size_t v_sz_boxed_3807_; size_t v_i_boxed_3808_; lean_object* v_res_3809_; 
v_sz_boxed_3807_ = lean_unbox_usize(v_sz_3801_);
lean_dec(v_sz_3801_);
v_i_boxed_3808_ = lean_unbox_usize(v_i_3802_);
lean_dec(v_i_3802_);
v_res_3809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3797_, v___x_3798_, v___x_3799_, v_as_3800_, v_sz_boxed_3807_, v_i_boxed_3808_, v_b_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v_as_3800_);
lean_dec(v___x_3799_);
return v_res_3809_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3815_ = l_Lean_stringToMessageData(v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3816_, lean_object* v___x_3817_, lean_object* v___x_3818_, lean_object* v___x_3819_, lean_object* v___x_3820_, lean_object* v_as_3821_, size_t v_sz_3822_, size_t v_i_3823_, lean_object* v_b_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_usize_dec_lt(v_i_3823_, v_sz_3822_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
lean_dec_ref(v___x_3819_);
lean_dec(v_stx_3816_);
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_b_3824_);
return v___x_3829_;
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v_a_3833_; lean_object* v___x_3834_; 
lean_dec_ref(v_b_3824_);
v___x_3830_ = lean_box(0);
v___x_3831_ = l_Lean_inheritedTraceOptions;
v___x_3832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3833_ = lean_array_uget_borrowed(v_as_3821_, v_i_3823_);
lean_inc(v_a_3833_);
lean_inc(v_stx_3816_);
v___x_3834_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3816_, v___x_3817_, v_a_3833_, v___x_3818_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v_scopes_3857_; lean_object* v___x_3858_; lean_object* v_opts_3859_; uint8_t v_hasTrace_3860_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
v___x_3854_ = lean_st_ref_get(v___x_3831_);
v___x_3855_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3856_ = lean_st_ref_get(v___y_3826_);
v_scopes_3857_ = lean_ctor_get(v___x_3856_, 2);
lean_inc(v_scopes_3857_);
lean_dec(v___x_3856_);
v___x_3858_ = l_List_head_x21___redArg(v___x_3855_, v_scopes_3857_);
lean_dec(v_scopes_3857_);
v_opts_3859_ = lean_ctor_get(v___x_3858_, 1);
lean_inc_ref(v_opts_3859_);
lean_dec(v___x_3858_);
v_hasTrace_3860_ = lean_ctor_get_uint8(v_opts_3859_, sizeof(void*)*1);
if (v_hasTrace_3860_ == 0)
{
lean_dec_ref(v_opts_3859_);
lean_dec(v___x_3854_);
v___y_3837_ = v___y_3825_;
v___y_3838_ = v___y_3826_;
goto v___jp_3836_;
}
else
{
lean_object* v___x_3861_; uint8_t v___x_3862_; 
v___x_3861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3862_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3854_, v_opts_3859_, v___x_3861_);
lean_dec_ref(v_opts_3859_);
lean_dec(v___x_3854_);
if (v___x_3862_ == 0)
{
v___y_3837_ = v___y_3825_;
v___y_3838_ = v___y_3826_;
goto v___jp_3836_;
}
else
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3864_ = lean_array_get_size(v_a_3835_);
v___x_3865_ = l_Nat_reprFast(v___x_3864_);
v___x_3866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
v___x_3867_ = l_Lean_MessageData_ofFormat(v___x_3866_);
v___x_3868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3863_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3832_, v___x_3868_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_dec_ref_known(v___x_3869_, 1);
v___y_3837_ = v___y_3825_;
v___y_3838_ = v___y_3826_;
goto v___jp_3836_;
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_a_3835_);
lean_dec_ref(v___x_3819_);
lean_dec(v_stx_3816_);
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3869_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3869_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
}
v___jp_3836_:
{
size_t v_sz_3839_; size_t v___x_3840_; lean_object* v___x_3841_; 
v_sz_3839_ = lean_array_size(v_a_3835_);
v___x_3840_ = ((size_t)0ULL);
lean_inc_ref(v___x_3819_);
lean_inc(v_a_3833_);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3833_, v___x_3819_, v___x_3820_, v_a_3835_, v_sz_3839_, v___x_3840_, v___x_3830_, v___y_3837_, v___y_3838_);
lean_dec(v_a_3835_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v___x_3842_; size_t v___x_3843_; size_t v___x_3844_; 
lean_dec_ref_known(v___x_3841_, 1);
v___x_3842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3823_, v___x_3843_);
v_i_3823_ = v___x_3844_;
v_b_3824_ = v___x_3842_;
goto _start;
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec_ref(v___x_3819_);
lean_dec(v_stx_3816_);
v_a_3846_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3841_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3841_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v___x_3819_);
lean_dec(v_stx_3816_);
v_a_3878_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3834_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3834_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3886_, lean_object* v___x_3887_, lean_object* v___x_3888_, lean_object* v___x_3889_, lean_object* v___x_3890_, lean_object* v_as_3891_, lean_object* v_sz_3892_, lean_object* v_i_3893_, lean_object* v_b_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
size_t v_sz_boxed_3898_; size_t v_i_boxed_3899_; lean_object* v_res_3900_; 
v_sz_boxed_3898_ = lean_unbox_usize(v_sz_3892_);
lean_dec(v_sz_3892_);
v_i_boxed_3899_ = lean_unbox_usize(v_i_3893_);
lean_dec(v_i_3893_);
v_res_3900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3886_, v___x_3887_, v___x_3888_, v___x_3889_, v___x_3890_, v_as_3891_, v_sz_boxed_3898_, v_i_boxed_3899_, v_b_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec_ref(v_as_3891_);
lean_dec(v___x_3890_);
lean_dec_ref(v___x_3888_);
lean_dec_ref(v___x_3887_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3901_, lean_object* v___x_3902_, lean_object* v___x_3903_, lean_object* v___x_3904_, lean_object* v___x_3905_, lean_object* v_as_3906_, size_t v_sz_3907_, size_t v_i_3908_, lean_object* v_b_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
uint8_t v___x_3913_; 
v___x_3913_ = lean_usize_dec_lt(v_i_3908_, v_sz_3907_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; 
lean_dec_ref(v___x_3904_);
lean_dec(v_stx_3901_);
v___x_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3914_, 0, v_b_3909_);
return v___x_3914_;
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v_a_3918_; lean_object* v___x_3919_; 
lean_dec_ref(v_b_3909_);
v___x_3915_ = lean_box(0);
v___x_3916_ = l_Lean_inheritedTraceOptions;
v___x_3917_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3918_ = lean_array_uget_borrowed(v_as_3906_, v_i_3908_);
lean_inc(v_a_3918_);
lean_inc(v_stx_3901_);
v___x_3919_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3901_, v___x_3902_, v_a_3918_, v___x_3903_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v_scopes_3942_; lean_object* v___x_3943_; lean_object* v_opts_3944_; uint8_t v_hasTrace_3945_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v___x_3939_ = lean_st_ref_get(v___x_3916_);
v___x_3940_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3941_ = lean_st_ref_get(v___y_3911_);
v_scopes_3942_ = lean_ctor_get(v___x_3941_, 2);
lean_inc(v_scopes_3942_);
lean_dec(v___x_3941_);
v___x_3943_ = l_List_head_x21___redArg(v___x_3940_, v_scopes_3942_);
lean_dec(v_scopes_3942_);
v_opts_3944_ = lean_ctor_get(v___x_3943_, 1);
lean_inc_ref(v_opts_3944_);
lean_dec(v___x_3943_);
v_hasTrace_3945_ = lean_ctor_get_uint8(v_opts_3944_, sizeof(void*)*1);
if (v_hasTrace_3945_ == 0)
{
lean_dec_ref(v_opts_3944_);
lean_dec(v___x_3939_);
v___y_3922_ = v___y_3910_;
v___y_3923_ = v___y_3911_;
goto v___jp_3921_;
}
else
{
lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3947_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3939_, v_opts_3944_, v___x_3946_);
lean_dec_ref(v_opts_3944_);
lean_dec(v___x_3939_);
if (v___x_3947_ == 0)
{
v___y_3922_ = v___y_3910_;
v___y_3923_ = v___y_3911_;
goto v___jp_3921_;
}
else
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3948_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3949_ = lean_array_get_size(v_a_3920_);
v___x_3950_ = l_Nat_reprFast(v___x_3949_);
v___x_3951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
v___x_3952_ = l_Lean_MessageData_ofFormat(v___x_3951_);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3948_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3917_, v___x_3953_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_dec_ref_known(v___x_3954_, 1);
v___y_3922_ = v___y_3910_;
v___y_3923_ = v___y_3911_;
goto v___jp_3921_;
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_a_3920_);
lean_dec_ref(v___x_3904_);
lean_dec(v_stx_3901_);
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
v___jp_3921_:
{
size_t v_sz_3924_; size_t v___x_3925_; lean_object* v___x_3926_; 
v_sz_3924_ = lean_array_size(v_a_3920_);
v___x_3925_ = ((size_t)0ULL);
lean_inc_ref(v___x_3904_);
lean_inc(v_a_3918_);
v___x_3926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3918_, v___x_3904_, v___x_3905_, v_a_3920_, v_sz_3924_, v___x_3925_, v___x_3915_, v___y_3922_, v___y_3923_);
lean_dec(v_a_3920_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3927_; size_t v___x_3928_; size_t v___x_3929_; lean_object* v___x_3930_; 
lean_dec_ref_known(v___x_3926_, 1);
v___x_3927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3928_ = ((size_t)1ULL);
v___x_3929_ = lean_usize_add(v_i_3908_, v___x_3928_);
v___x_3930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3901_, v___x_3902_, v___x_3903_, v___x_3904_, v___x_3905_, v_as_3906_, v_sz_3907_, v___x_3929_, v___x_3927_, v___y_3910_, v___y_3911_);
return v___x_3930_;
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v___x_3904_);
lean_dec(v_stx_3901_);
v_a_3931_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3926_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3926_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref(v___x_3904_);
lean_dec(v_stx_3901_);
v_a_3963_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3919_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3919_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3971_, lean_object* v___x_3972_, lean_object* v___x_3973_, lean_object* v___x_3974_, lean_object* v___x_3975_, lean_object* v_as_3976_, lean_object* v_sz_3977_, lean_object* v_i_3978_, lean_object* v_b_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
size_t v_sz_boxed_3983_; size_t v_i_boxed_3984_; lean_object* v_res_3985_; 
v_sz_boxed_3983_ = lean_unbox_usize(v_sz_3977_);
lean_dec(v_sz_3977_);
v_i_boxed_3984_ = lean_unbox_usize(v_i_3978_);
lean_dec(v_i_3978_);
v_res_3985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3971_, v___x_3972_, v___x_3973_, v___x_3974_, v___x_3975_, v_as_3976_, v_sz_boxed_3983_, v_i_boxed_3984_, v_b_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec_ref(v_as_3976_);
lean_dec(v___x_3975_);
lean_dec_ref(v___x_3973_);
lean_dec_ref(v___x_3972_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_3989_, lean_object* v___x_3990_, lean_object* v___x_3991_, lean_object* v___x_3992_, lean_object* v___x_3993_, lean_object* v_as_3994_, size_t v_sz_3995_, size_t v_i_3996_, lean_object* v_b_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
uint8_t v___x_4001_; 
v___x_4001_ = lean_usize_dec_lt(v_i_3996_, v_sz_3995_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; 
lean_dec_ref(v___x_3992_);
lean_dec(v_stx_3989_);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v_b_3997_);
return v___x_4002_;
}
else
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v_a_4006_; lean_object* v___x_4007_; 
lean_dec_ref(v_b_3997_);
v___x_4003_ = lean_box(0);
v___x_4004_ = l_Lean_inheritedTraceOptions;
v___x_4005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4006_ = lean_array_uget_borrowed(v_as_3994_, v_i_3996_);
lean_inc(v_a_4006_);
lean_inc(v_stx_3989_);
v___x_4007_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3989_, v___x_3990_, v_a_4006_, v___x_3991_, v___y_3998_, v___y_3999_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v_scopes_4030_; lean_object* v___x_4031_; lean_object* v_opts_4032_; uint8_t v_hasTrace_4033_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref_known(v___x_4007_, 1);
v___x_4027_ = lean_st_ref_get(v___x_4004_);
v___x_4028_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4029_ = lean_st_ref_get(v___y_3999_);
v_scopes_4030_ = lean_ctor_get(v___x_4029_, 2);
lean_inc(v_scopes_4030_);
lean_dec(v___x_4029_);
v___x_4031_ = l_List_head_x21___redArg(v___x_4028_, v_scopes_4030_);
lean_dec(v_scopes_4030_);
v_opts_4032_ = lean_ctor_get(v___x_4031_, 1);
lean_inc_ref(v_opts_4032_);
lean_dec(v___x_4031_);
v_hasTrace_4033_ = lean_ctor_get_uint8(v_opts_4032_, sizeof(void*)*1);
if (v_hasTrace_4033_ == 0)
{
lean_dec_ref(v_opts_4032_);
lean_dec(v___x_4027_);
v___y_4010_ = v___y_3998_;
v___y_4011_ = v___y_3999_;
goto v___jp_4009_;
}
else
{
lean_object* v___x_4034_; uint8_t v___x_4035_; 
v___x_4034_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4027_, v_opts_4032_, v___x_4034_);
lean_dec_ref(v_opts_4032_);
lean_dec(v___x_4027_);
if (v___x_4035_ == 0)
{
v___y_4010_ = v___y_3998_;
v___y_4011_ = v___y_3999_;
goto v___jp_4009_;
}
else
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4036_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4037_ = lean_array_get_size(v_a_4008_);
v___x_4038_ = l_Nat_reprFast(v___x_4037_);
v___x_4039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
v___x_4040_ = l_Lean_MessageData_ofFormat(v___x_4039_);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4036_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4005_, v___x_4041_, v___y_3998_, v___y_3999_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_dec_ref_known(v___x_4042_, 1);
v___y_4010_ = v___y_3998_;
v___y_4011_ = v___y_3999_;
goto v___jp_4009_;
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec(v_a_4008_);
lean_dec_ref(v___x_3992_);
lean_dec(v_stx_3989_);
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4042_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4042_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
v___jp_4009_:
{
size_t v_sz_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v_sz_4012_ = lean_array_size(v_a_4008_);
v___x_4013_ = ((size_t)0ULL);
lean_inc_ref(v___x_3992_);
lean_inc(v_a_4006_);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4006_, v___x_3992_, v___x_3993_, v_a_4008_, v_sz_4012_, v___x_4013_, v___x_4003_, v___y_4010_, v___y_4011_);
lean_dec(v_a_4008_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v___x_4015_; size_t v___x_4016_; size_t v___x_4017_; 
lean_dec_ref_known(v___x_4014_, 1);
v___x_4015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4016_ = ((size_t)1ULL);
v___x_4017_ = lean_usize_add(v_i_3996_, v___x_4016_);
v_i_3996_ = v___x_4017_;
v_b_3997_ = v___x_4015_;
goto _start;
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_dec_ref(v___x_3992_);
lean_dec(v_stx_3989_);
v_a_4019_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4014_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4014_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec_ref(v___x_3992_);
lean_dec(v_stx_3989_);
v_a_4051_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4007_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4007_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4059_, lean_object* v___x_4060_, lean_object* v___x_4061_, lean_object* v___x_4062_, lean_object* v___x_4063_, lean_object* v_as_4064_, lean_object* v_sz_4065_, lean_object* v_i_4066_, lean_object* v_b_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
size_t v_sz_boxed_4071_; size_t v_i_boxed_4072_; lean_object* v_res_4073_; 
v_sz_boxed_4071_ = lean_unbox_usize(v_sz_4065_);
lean_dec(v_sz_4065_);
v_i_boxed_4072_ = lean_unbox_usize(v_i_4066_);
lean_dec(v_i_4066_);
v_res_4073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4059_, v___x_4060_, v___x_4061_, v___x_4062_, v___x_4063_, v_as_4064_, v_sz_boxed_4071_, v_i_boxed_4072_, v_b_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec_ref(v_as_4064_);
lean_dec(v___x_4063_);
lean_dec_ref(v___x_4061_);
lean_dec_ref(v___x_4060_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4074_, lean_object* v___x_4075_, lean_object* v___x_4076_, lean_object* v___x_4077_, lean_object* v___x_4078_, lean_object* v_as_4079_, size_t v_sz_4080_, size_t v_i_4081_, lean_object* v_b_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
uint8_t v___x_4086_; 
v___x_4086_ = lean_usize_dec_lt(v_i_4081_, v_sz_4080_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; 
lean_dec_ref(v___x_4077_);
lean_dec(v_stx_4074_);
v___x_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4087_, 0, v_b_4082_);
return v___x_4087_;
}
else
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v_a_4091_; lean_object* v___x_4092_; 
lean_dec_ref(v_b_4082_);
v___x_4088_ = lean_box(0);
v___x_4089_ = l_Lean_inheritedTraceOptions;
v___x_4090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4091_ = lean_array_uget_borrowed(v_as_4079_, v_i_4081_);
lean_inc(v_a_4091_);
lean_inc(v_stx_4074_);
v___x_4092_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4074_, v___x_4075_, v_a_4091_, v___x_4076_, v___y_4083_, v___y_4084_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v_scopes_4115_; lean_object* v___x_4116_; lean_object* v_opts_4117_; uint8_t v_hasTrace_4118_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___x_4092_, 1);
v___x_4112_ = lean_st_ref_get(v___x_4089_);
v___x_4113_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4114_ = lean_st_ref_get(v___y_4084_);
v_scopes_4115_ = lean_ctor_get(v___x_4114_, 2);
lean_inc(v_scopes_4115_);
lean_dec(v___x_4114_);
v___x_4116_ = l_List_head_x21___redArg(v___x_4113_, v_scopes_4115_);
lean_dec(v_scopes_4115_);
v_opts_4117_ = lean_ctor_get(v___x_4116_, 1);
lean_inc_ref(v_opts_4117_);
lean_dec(v___x_4116_);
v_hasTrace_4118_ = lean_ctor_get_uint8(v_opts_4117_, sizeof(void*)*1);
if (v_hasTrace_4118_ == 0)
{
lean_dec_ref(v_opts_4117_);
lean_dec(v___x_4112_);
v___y_4095_ = v___y_4083_;
v___y_4096_ = v___y_4084_;
goto v___jp_4094_;
}
else
{
lean_object* v___x_4119_; uint8_t v___x_4120_; 
v___x_4119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4120_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4112_, v_opts_4117_, v___x_4119_);
lean_dec_ref(v_opts_4117_);
lean_dec(v___x_4112_);
if (v___x_4120_ == 0)
{
v___y_4095_ = v___y_4083_;
v___y_4096_ = v___y_4084_;
goto v___jp_4094_;
}
else
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4122_ = lean_array_get_size(v_a_4093_);
v___x_4123_ = l_Nat_reprFast(v___x_4122_);
v___x_4124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
v___x_4125_ = l_Lean_MessageData_ofFormat(v___x_4124_);
v___x_4126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4121_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
v___x_4127_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4090_, v___x_4126_, v___y_4083_, v___y_4084_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_dec_ref_known(v___x_4127_, 1);
v___y_4095_ = v___y_4083_;
v___y_4096_ = v___y_4084_;
goto v___jp_4094_;
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_dec(v_a_4093_);
lean_dec_ref(v___x_4077_);
lean_dec(v_stx_4074_);
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
}
v___jp_4094_:
{
size_t v_sz_4097_; size_t v___x_4098_; lean_object* v___x_4099_; 
v_sz_4097_ = lean_array_size(v_a_4093_);
v___x_4098_ = ((size_t)0ULL);
lean_inc_ref(v___x_4077_);
lean_inc(v_a_4091_);
v___x_4099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4091_, v___x_4077_, v___x_4078_, v_a_4093_, v_sz_4097_, v___x_4098_, v___x_4088_, v___y_4095_, v___y_4096_);
lean_dec(v_a_4093_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v___x_4100_; size_t v___x_4101_; size_t v___x_4102_; lean_object* v___x_4103_; 
lean_dec_ref_known(v___x_4099_, 1);
v___x_4100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4101_ = ((size_t)1ULL);
v___x_4102_ = lean_usize_add(v_i_4081_, v___x_4101_);
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4074_, v___x_4075_, v___x_4076_, v___x_4077_, v___x_4078_, v_as_4079_, v_sz_4080_, v___x_4102_, v___x_4100_, v___y_4083_, v___y_4084_);
return v___x_4103_;
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec_ref(v___x_4077_);
lean_dec(v_stx_4074_);
v_a_4104_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4099_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4099_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v___x_4077_);
lean_dec(v_stx_4074_);
v_a_4136_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4092_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4092_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4144_, lean_object* v___x_4145_, lean_object* v___x_4146_, lean_object* v___x_4147_, lean_object* v___x_4148_, lean_object* v_as_4149_, lean_object* v_sz_4150_, lean_object* v_i_4151_, lean_object* v_b_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
size_t v_sz_boxed_4156_; size_t v_i_boxed_4157_; lean_object* v_res_4158_; 
v_sz_boxed_4156_ = lean_unbox_usize(v_sz_4150_);
lean_dec(v_sz_4150_);
v_i_boxed_4157_ = lean_unbox_usize(v_i_4151_);
lean_dec(v_i_4151_);
v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4144_, v___x_4145_, v___x_4146_, v___x_4147_, v___x_4148_, v_as_4149_, v_sz_boxed_4156_, v_i_boxed_4157_, v_b_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v_as_4149_);
lean_dec(v___x_4148_);
lean_dec_ref(v___x_4146_);
lean_dec_ref(v___x_4145_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4159_, lean_object* v_stx_4160_, lean_object* v___x_4161_, lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v_n_4165_, lean_object* v_b_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
if (lean_obj_tag(v_n_4165_) == 0)
{
lean_object* v_cs_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; size_t v_sz_4173_; size_t v___x_4174_; lean_object* v___x_4175_; 
v_cs_4170_ = lean_ctor_get(v_n_4165_, 0);
v___x_4171_ = lean_box(0);
v___x_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
lean_ctor_set(v___x_4172_, 1, v_b_4166_);
v_sz_4173_ = lean_array_size(v_cs_4170_);
v___x_4174_ = ((size_t)0ULL);
v___x_4175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4159_, v_stx_4160_, v___x_4161_, v___x_4162_, v___x_4163_, v___x_4164_, v_cs_4170_, v_sz_4173_, v___x_4174_, v___x_4172_, v___y_4167_, v___y_4168_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4190_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4190_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4190_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v_fst_4180_; 
v_fst_4180_ = lean_ctor_get(v_a_4176_, 0);
if (lean_obj_tag(v_fst_4180_) == 0)
{
lean_object* v_snd_4181_; lean_object* v___x_4182_; lean_object* v___x_4184_; 
v_snd_4181_ = lean_ctor_get(v_a_4176_, 1);
lean_inc(v_snd_4181_);
lean_dec(v_a_4176_);
v___x_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4182_, 0, v_snd_4181_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4182_);
v___x_4184_ = v___x_4178_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
else
{
lean_object* v_val_4186_; lean_object* v___x_4188_; 
lean_inc_ref(v_fst_4180_);
lean_dec(v_a_4176_);
v_val_4186_ = lean_ctor_get(v_fst_4180_, 0);
lean_inc(v_val_4186_);
lean_dec_ref_known(v_fst_4180_, 1);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v_val_4186_);
v___x_4188_ = v___x_4178_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_val_4186_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
v_a_4191_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4175_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4175_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
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
lean_object* v_vs_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; size_t v_sz_4202_; size_t v___x_4203_; lean_object* v___x_4204_; 
v_vs_4199_ = lean_ctor_get(v_n_4165_, 0);
v___x_4200_ = lean_box(0);
v___x_4201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
lean_ctor_set(v___x_4201_, 1, v_b_4166_);
v_sz_4202_ = lean_array_size(v_vs_4199_);
v___x_4203_ = ((size_t)0ULL);
v___x_4204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4160_, v___x_4161_, v___x_4162_, v___x_4163_, v___x_4164_, v_vs_4199_, v_sz_4202_, v___x_4203_, v___x_4201_, v___y_4167_, v___y_4168_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4219_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4219_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4219_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v_fst_4209_; 
v_fst_4209_ = lean_ctor_get(v_a_4205_, 0);
if (lean_obj_tag(v_fst_4209_) == 0)
{
lean_object* v_snd_4210_; lean_object* v___x_4211_; lean_object* v___x_4213_; 
v_snd_4210_ = lean_ctor_get(v_a_4205_, 1);
lean_inc(v_snd_4210_);
lean_dec(v_a_4205_);
v___x_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4211_, 0, v_snd_4210_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4211_);
v___x_4213_ = v___x_4207_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
else
{
lean_object* v_val_4215_; lean_object* v___x_4217_; 
lean_inc_ref(v_fst_4209_);
lean_dec(v_a_4205_);
v_val_4215_ = lean_ctor_get(v_fst_4209_, 0);
lean_inc(v_val_4215_);
lean_dec_ref_known(v_fst_4209_, 1);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v_val_4215_);
v___x_4217_ = v___x_4207_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_val_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
v_a_4220_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4204_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4204_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4228_, lean_object* v_stx_4229_, lean_object* v___x_4230_, lean_object* v___x_4231_, lean_object* v___x_4232_, lean_object* v___x_4233_, lean_object* v_as_4234_, size_t v_sz_4235_, size_t v_i_4236_, lean_object* v_b_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
uint8_t v___x_4241_; 
v___x_4241_ = lean_usize_dec_lt(v_i_4236_, v_sz_4235_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; 
lean_dec_ref(v___x_4232_);
lean_dec(v_stx_4229_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v_b_4237_);
return v___x_4242_;
}
else
{
lean_object* v_snd_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4277_; 
v_snd_4243_ = lean_ctor_get(v_b_4237_, 1);
v_isSharedCheck_4277_ = !lean_is_exclusive(v_b_4237_);
if (v_isSharedCheck_4277_ == 0)
{
lean_object* v_unused_4278_; 
v_unused_4278_ = lean_ctor_get(v_b_4237_, 0);
lean_dec(v_unused_4278_);
v___x_4245_ = v_b_4237_;
v_isShared_4246_ = v_isSharedCheck_4277_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_snd_4243_);
lean_dec(v_b_4237_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4277_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4247_; lean_object* v_a_4248_; lean_object* v___x_4249_; 
v___x_4247_ = lean_box(0);
v_a_4248_ = lean_array_uget_borrowed(v_as_4234_, v_i_4236_);
lean_inc(v_snd_4243_);
lean_inc_ref(v___x_4232_);
lean_inc(v_stx_4229_);
v___x_4249_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4228_, v_stx_4229_, v___x_4230_, v___x_4231_, v___x_4232_, v___x_4233_, v_a_4248_, v_snd_4243_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4268_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4252_ = v___x_4249_;
v_isShared_4253_ = v_isSharedCheck_4268_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4249_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4268_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
if (lean_obj_tag(v_a_4250_) == 0)
{
lean_object* v___x_4254_; lean_object* v___x_4256_; 
lean_dec_ref(v___x_4232_);
lean_dec(v_stx_4229_);
v___x_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4254_, 0, v_a_4250_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4254_);
v___x_4256_ = v___x_4245_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4254_);
lean_ctor_set(v_reuseFailAlloc_4260_, 1, v_snd_4243_);
v___x_4256_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
lean_object* v___x_4258_; 
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v___x_4256_);
v___x_4258_ = v___x_4252_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; 
lean_del_object(v___x_4252_);
lean_dec(v_snd_4243_);
v_a_4261_ = lean_ctor_get(v_a_4250_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v_a_4250_, 1);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 1, v_a_4261_);
lean_ctor_set(v___x_4245_, 0, v___x_4247_);
v___x_4263_ = v___x_4245_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_a_4261_);
v___x_4263_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
size_t v___x_4264_; size_t v___x_4265_; 
v___x_4264_ = ((size_t)1ULL);
v___x_4265_ = lean_usize_add(v_i_4236_, v___x_4264_);
v_i_4236_ = v___x_4265_;
v_b_4237_ = v___x_4263_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_del_object(v___x_4245_);
lean_dec(v_snd_4243_);
lean_dec_ref(v___x_4232_);
lean_dec(v_stx_4229_);
v_a_4269_ = lean_ctor_get(v___x_4249_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4249_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4249_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4279_, lean_object* v_stx_4280_, lean_object* v___x_4281_, lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v_as_4285_, lean_object* v_sz_4286_, lean_object* v_i_4287_, lean_object* v_b_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
size_t v_sz_boxed_4292_; size_t v_i_boxed_4293_; lean_object* v_res_4294_; 
v_sz_boxed_4292_ = lean_unbox_usize(v_sz_4286_);
lean_dec(v_sz_4286_);
v_i_boxed_4293_ = lean_unbox_usize(v_i_4287_);
lean_dec(v_i_4287_);
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4279_, v_stx_4280_, v___x_4281_, v___x_4282_, v___x_4283_, v___x_4284_, v_as_4285_, v_sz_boxed_4292_, v_i_boxed_4293_, v_b_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec_ref(v_as_4285_);
lean_dec(v___x_4284_);
lean_dec_ref(v___x_4282_);
lean_dec_ref(v___x_4281_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4295_, lean_object* v_stx_4296_, lean_object* v___x_4297_, lean_object* v___x_4298_, lean_object* v___x_4299_, lean_object* v___x_4300_, lean_object* v_n_4301_, lean_object* v_b_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4295_, v_stx_4296_, v___x_4297_, v___x_4298_, v___x_4299_, v___x_4300_, v_n_4301_, v_b_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v_n_4301_);
lean_dec(v___x_4300_);
lean_dec_ref(v___x_4298_);
lean_dec_ref(v___x_4297_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4307_, lean_object* v___x_4308_, lean_object* v_stx_4309_, lean_object* v___x_4310_, lean_object* v___x_4311_, lean_object* v_t_4312_, lean_object* v_init_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_root_4317_; lean_object* v_tail_4318_; lean_object* v___x_4319_; 
v_root_4317_ = lean_ctor_get(v_t_4312_, 0);
v_tail_4318_ = lean_ctor_get(v_t_4312_, 1);
lean_inc_ref(v___x_4307_);
lean_inc(v_stx_4309_);
v___x_4319_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4313_, v_stx_4309_, v___x_4310_, v___x_4311_, v___x_4307_, v___x_4308_, v_root_4317_, v_init_4313_, v___y_4314_, v___y_4315_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4356_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4356_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4356_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
if (lean_obj_tag(v_a_4320_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; 
lean_dec(v_stx_4309_);
lean_dec_ref(v___x_4307_);
v_a_4324_ = lean_ctor_get(v_a_4320_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v_a_4320_, 1);
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 0, v_a_4324_);
v___x_4326_ = v___x_4322_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4324_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; size_t v_sz_4331_; size_t v___x_4332_; lean_object* v___x_4333_; 
lean_del_object(v___x_4322_);
v_a_4328_ = lean_ctor_get(v_a_4320_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v_a_4320_, 1);
v___x_4329_ = lean_box(0);
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4329_);
lean_ctor_set(v___x_4330_, 1, v_a_4328_);
v_sz_4331_ = lean_array_size(v_tail_4318_);
v___x_4332_ = ((size_t)0ULL);
v___x_4333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4309_, v___x_4310_, v___x_4311_, v___x_4307_, v___x_4308_, v_tail_4318_, v_sz_4331_, v___x_4332_, v___x_4330_, v___y_4314_, v___y_4315_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4347_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4347_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4347_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v_fst_4338_; 
v_fst_4338_ = lean_ctor_get(v_a_4334_, 0);
if (lean_obj_tag(v_fst_4338_) == 0)
{
lean_object* v_snd_4339_; lean_object* v___x_4341_; 
v_snd_4339_ = lean_ctor_get(v_a_4334_, 1);
lean_inc(v_snd_4339_);
lean_dec(v_a_4334_);
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 0, v_snd_4339_);
v___x_4341_ = v___x_4336_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_snd_4339_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
else
{
lean_object* v_val_4343_; lean_object* v___x_4345_; 
lean_inc_ref(v_fst_4338_);
lean_dec(v_a_4334_);
v_val_4343_ = lean_ctor_get(v_fst_4338_, 0);
lean_inc(v_val_4343_);
lean_dec_ref_known(v_fst_4338_, 1);
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 0, v_val_4343_);
v___x_4345_ = v___x_4336_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_val_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
v_a_4348_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4333_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4333_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
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
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v_stx_4309_);
lean_dec_ref(v___x_4307_);
v_a_4357_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4319_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4319_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4365_, lean_object* v___x_4366_, lean_object* v_stx_4367_, lean_object* v___x_4368_, lean_object* v___x_4369_, lean_object* v_t_4370_, lean_object* v_init_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4365_, v___x_4366_, v_stx_4367_, v___x_4368_, v___x_4369_, v_t_4370_, v_init_4371_, v___y_4372_, v___y_4373_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec_ref(v_t_4370_);
lean_dec_ref(v___x_4369_);
lean_dec_ref(v___x_4368_);
lean_dec(v___x_4366_);
return v_res_4375_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4378_ = l_Lean_stringToMessageData(v___x_4377_);
return v___x_4378_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4383_ = l_Lean_stringToMessageData(v___x_4382_);
return v___x_4383_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4386_ = l_Lean_stringToMessageData(v___x_4385_);
return v___x_4386_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4389_ = l_Lean_stringToMessageData(v___x_4388_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v_scopes_4399_; lean_object* v___x_4400_; lean_object* v_opts_4401_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; uint8_t v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4433_; lean_object* v___y_4434_; uint8_t v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4442_; uint8_t v___y_4443_; uint8_t v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; uint8_t v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; uint8_t v___y_4458_; uint8_t v___y_4459_; lean_object* v___y_4460_; uint8_t v___y_4469_; uint8_t v___y_4470_; uint8_t v___y_4471_; uint8_t v___y_4505_; lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4397_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4398_ = lean_st_ref_get(v___y_4392_);
v_scopes_4399_ = lean_ctor_get(v___x_4398_, 2);
lean_inc(v_scopes_4399_);
lean_dec(v___x_4398_);
v___x_4400_ = l_List_head_x21___redArg(v___x_4397_, v_scopes_4399_);
lean_dec(v_scopes_4399_);
v_opts_4401_ = lean_ctor_get(v___x_4400_, 1);
lean_inc_ref(v_opts_4401_);
lean_dec(v___x_4400_);
v___x_4512_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4513_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4401_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4514_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4515_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4401_, v___x_4514_);
v___y_4505_ = v___x_4515_;
goto v___jp_4504_;
}
else
{
v___y_4505_ = v___x_4513_;
goto v___jp_4504_;
}
v___jp_4394_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = lean_box(0);
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
v___jp_4402_:
{
lean_object* v___x_4407_; lean_object* v_line_4408_; lean_object* v___x_4409_; lean_object* v_messages_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v_a_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
lean_inc_ref_n(v___y_4404_, 2);
v___x_4407_ = l_Lean_FileMap_toPosition(v___y_4404_, v___y_4406_);
lean_dec(v___y_4406_);
v_line_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_line_4408_);
lean_dec_ref(v___x_4407_);
v___x_4409_ = lean_st_ref_get(v___y_4403_);
v_messages_4410_ = lean_ctor_get(v___x_4409_, 1);
lean_inc_ref(v_messages_4410_);
lean_dec(v___x_4409_);
v___x_4411_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4410_);
v___x_4412_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4403_);
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref(v___x_4412_);
v___x_4414_ = lean_box(0);
v___x_4415_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4404_, v_line_4408_, v_stx_4390_, v_opts_4401_, v___x_4411_, v_a_4413_, v___x_4414_, v___y_4405_, v___y_4403_);
lean_dec(v_a_4413_);
lean_dec_ref(v___x_4411_);
lean_dec_ref(v_opts_4401_);
lean_dec(v_line_4408_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4422_ == 0)
{
lean_object* v_unused_4423_; 
v_unused_4423_ = lean_ctor_get(v___x_4415_, 0);
lean_dec(v_unused_4423_);
v___x_4417_ = v___x_4415_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_dec(v___x_4415_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4414_);
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4414_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
else
{
return v___x_4415_;
}
}
v___jp_4424_:
{
lean_object* v_fileMap_4428_; lean_object* v___x_4429_; 
v_fileMap_4428_ = lean_ctor_get(v___y_4426_, 1);
v___x_4429_ = l_Lean_Syntax_getPos_x3f(v_stx_4390_, v___y_4425_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v___x_4430_; 
v___x_4430_ = lean_unsigned_to_nat(0u);
v___y_4403_ = v___y_4427_;
v___y_4404_ = v_fileMap_4428_;
v___y_4405_ = v___y_4426_;
v___y_4406_ = v___x_4430_;
goto v___jp_4402_;
}
else
{
lean_object* v_val_4431_; 
v_val_4431_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_val_4431_);
lean_dec_ref_known(v___x_4429_, 1);
v___y_4403_ = v___y_4427_;
v___y_4404_ = v_fileMap_4428_;
v___y_4405_ = v___y_4426_;
v___y_4406_ = v_val_4431_;
goto v___jp_4402_;
}
}
v___jp_4432_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
lean_inc_ref(v___y_4436_);
v___x_4437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___y_4436_);
v___x_4438_ = l_Lean_MessageData_ofFormat(v___x_4437_);
v___x_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4439_, 0, v___y_4433_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
lean_inc(v___y_4434_);
v___x_4440_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___y_4434_, v___x_4439_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_dec_ref_known(v___x_4440_, 1);
v___y_4425_ = v___y_4435_;
v___y_4426_ = v___y_4391_;
v___y_4427_ = v___y_4392_;
goto v___jp_4424_;
}
else
{
lean_dec_ref(v_opts_4401_);
lean_dec(v_stx_4390_);
return v___x_4440_;
}
}
v___jp_4441_:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_inc_ref(v___y_4446_);
v___x_4447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4447_, 0, v___y_4446_);
v___x_4448_ = l_Lean_MessageData_ofFormat(v___x_4447_);
v___x_4449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___y_4445_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4449_);
lean_ctor_set(v___x_4451_, 1, v___x_4450_);
if (v___y_4443_ == 0)
{
lean_object* v___x_4452_; 
v___x_4452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4433_ = v___x_4451_;
v___y_4434_ = v___y_4442_;
v___y_4435_ = v___y_4444_;
v___y_4436_ = v___x_4452_;
goto v___jp_4432_;
}
else
{
lean_object* v___x_4453_; 
v___x_4453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4433_ = v___x_4451_;
v___y_4434_ = v___y_4442_;
v___y_4435_ = v___y_4444_;
v___y_4436_ = v___x_4453_;
goto v___jp_4432_;
}
}
v___jp_4454_:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
lean_inc_ref(v___y_4460_);
v___x_4461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___y_4460_);
v___x_4462_ = l_Lean_MessageData_ofFormat(v___x_4461_);
lean_inc_ref(v___y_4456_);
v___x_4463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___y_4456_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
v___x_4464_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4463_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
if (v___y_4455_ == 0)
{
lean_object* v___x_4466_; 
v___x_4466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4442_ = v___y_4457_;
v___y_4443_ = v___y_4458_;
v___y_4444_ = v___y_4459_;
v___y_4445_ = v___x_4465_;
v___y_4446_ = v___x_4466_;
goto v___jp_4441_;
}
else
{
lean_object* v___x_4467_; 
v___x_4467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4442_ = v___y_4457_;
v___y_4443_ = v___y_4458_;
v___y_4444_ = v___y_4459_;
v___y_4445_ = v___x_4465_;
v___y_4446_ = v___x_4467_;
goto v___jp_4441_;
}
}
v___jp_4468_:
{
lean_object* v___x_4472_; lean_object* v_a_4473_; uint8_t v___x_4474_; 
v___x_4472_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4390_, v___y_4391_, v___y_4392_);
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref(v___x_4472_);
v___x_4474_ = lean_unbox(v_a_4473_);
if (v___x_4474_ == 0)
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v_scopes_4479_; lean_object* v___x_4480_; lean_object* v_opts_4481_; uint8_t v_hasTrace_4482_; 
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4476_ = l_Lean_inheritedTraceOptions;
v___x_4477_ = lean_st_ref_get(v___x_4476_);
v___x_4478_ = lean_st_ref_get(v___y_4392_);
v_scopes_4479_ = lean_ctor_get(v___x_4478_, 2);
lean_inc(v_scopes_4479_);
lean_dec(v___x_4478_);
v___x_4480_ = l_List_head_x21___redArg(v___x_4397_, v_scopes_4479_);
lean_dec(v_scopes_4479_);
v_opts_4481_ = lean_ctor_get(v___x_4480_, 1);
lean_inc_ref(v_opts_4481_);
lean_dec(v___x_4480_);
v_hasTrace_4482_ = lean_ctor_get_uint8(v_opts_4481_, sizeof(void*)*1);
if (v_hasTrace_4482_ == 0)
{
uint8_t v___x_4483_; 
lean_dec_ref(v_opts_4481_);
lean_dec(v___x_4477_);
v___x_4483_ = lean_unbox(v_a_4473_);
lean_dec(v_a_4473_);
v___y_4425_ = v___x_4483_;
v___y_4426_ = v___y_4391_;
v___y_4427_ = v___y_4392_;
goto v___jp_4424_;
}
else
{
lean_object* v___x_4484_; uint8_t v___x_4485_; 
v___x_4484_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4485_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4477_, v_opts_4481_, v___x_4484_);
lean_dec_ref(v_opts_4481_);
lean_dec(v___x_4477_);
if (v___x_4485_ == 0)
{
uint8_t v___x_4486_; 
v___x_4486_ = lean_unbox(v_a_4473_);
lean_dec(v_a_4473_);
v___y_4425_ = v___x_4486_;
v___y_4426_ = v___y_4391_;
v___y_4427_ = v___y_4392_;
goto v___jp_4424_;
}
else
{
lean_object* v___x_4487_; 
v___x_4487_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4470_ == 0)
{
lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4489_ = lean_unbox(v_a_4473_);
lean_dec(v_a_4473_);
v___y_4455_ = v___y_4469_;
v___y_4456_ = v___x_4487_;
v___y_4457_ = v___x_4475_;
v___y_4458_ = v___y_4471_;
v___y_4459_ = v___x_4489_;
v___y_4460_ = v___x_4488_;
goto v___jp_4454_;
}
else
{
lean_object* v___x_4490_; uint8_t v___x_4491_; 
v___x_4490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4491_ = lean_unbox(v_a_4473_);
lean_dec(v_a_4473_);
v___y_4455_ = v___y_4469_;
v___y_4456_ = v___x_4487_;
v___y_4457_ = v___x_4475_;
v___y_4458_ = v___y_4471_;
v___y_4459_ = v___x_4491_;
v___y_4460_ = v___x_4490_;
goto v___jp_4454_;
}
}
}
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v_scopes_4496_; lean_object* v___x_4497_; lean_object* v_opts_4498_; uint8_t v_hasTrace_4499_; 
lean_dec(v_a_4473_);
lean_dec_ref(v_opts_4401_);
lean_dec(v_stx_4390_);
v___x_4492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4493_ = l_Lean_inheritedTraceOptions;
v___x_4494_ = lean_st_ref_get(v___x_4493_);
v___x_4495_ = lean_st_ref_get(v___y_4392_);
v_scopes_4496_ = lean_ctor_get(v___x_4495_, 2);
lean_inc(v_scopes_4496_);
lean_dec(v___x_4495_);
v___x_4497_ = l_List_head_x21___redArg(v___x_4397_, v_scopes_4496_);
lean_dec(v_scopes_4496_);
v_opts_4498_ = lean_ctor_get(v___x_4497_, 1);
lean_inc_ref(v_opts_4498_);
lean_dec(v___x_4497_);
v_hasTrace_4499_ = lean_ctor_get_uint8(v_opts_4498_, sizeof(void*)*1);
if (v_hasTrace_4499_ == 0)
{
lean_dec_ref(v_opts_4498_);
lean_dec(v___x_4494_);
goto v___jp_4394_;
}
else
{
lean_object* v___x_4500_; uint8_t v___x_4501_; 
v___x_4500_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4494_, v_opts_4498_, v___x_4500_);
lean_dec_ref(v_opts_4498_);
lean_dec(v___x_4494_);
if (v___x_4501_ == 0)
{
goto v___jp_4394_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4503_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4492_, v___x_4502_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_dec_ref_known(v___x_4503_, 1);
goto v___jp_4394_;
}
else
{
return v___x_4503_;
}
}
}
}
}
v___jp_4504_:
{
lean_object* v___x_4506_; uint8_t v___x_4507_; lean_object* v___x_4508_; uint8_t v___x_4509_; 
v___x_4506_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4507_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4401_, v___x_4506_);
v___x_4508_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4509_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4401_, v___x_4508_);
if (v___y_4505_ == 0)
{
if (v___x_4507_ == 0)
{
if (v___x_4509_ == 0)
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec_ref(v_opts_4401_);
lean_dec(v_stx_4390_);
v___x_4510_ = lean_box(0);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
return v___x_4511_;
}
else
{
v___y_4469_ = v___x_4507_;
v___y_4470_ = v___y_4505_;
v___y_4471_ = v___x_4509_;
goto v___jp_4468_;
}
}
else
{
v___y_4469_ = v___x_4507_;
v___y_4470_ = v___y_4505_;
v___y_4471_ = v___x_4509_;
goto v___jp_4468_;
}
}
else
{
v___y_4469_ = v___x_4507_;
v___y_4470_ = v___y_4505_;
v___y_4471_ = v___x_4509_;
goto v___jp_4468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4534_ = l_Lean_Elab_Command_addLinter(v___x_4533_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4536_;
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
