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
v___x_266_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_ctor_set(v___x_266_, 2, v___x_265_);
lean_ctor_set(v___x_266_, 3, v___x_265_);
lean_ctor_set(v___x_266_, 4, v___x_265_);
lean_ctor_set(v___x_266_, 5, v___x_265_);
lean_ctor_set(v___x_266_, 6, v___x_265_);
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
lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_fileName_344_; lean_object* v_fileMap_345_; lean_object* v_ref_346_; lean_object* v_cancelTk_x3f_347_; lean_object* v_a_349_; lean_object* v_a_356_; lean_object* v_currNamespace_358_; lean_object* v_openDecls_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint16_t v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___y_380_; lean_object* v___y_381_; uint16_t v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint16_t v___y_486_; uint8_t v___y_487_; lean_object* v___y_488_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v_fileName_523_; lean_object* v_fileMap_524_; lean_object* v_currNamespace_525_; lean_object* v_openDecls_526_; lean_object* v_initHeartbeats_527_; lean_object* v_maxHeartbeats_528_; lean_object* v_quotContext_529_; lean_object* v_currMacroScope_530_; lean_object* v_cancelTk_x3f_531_; lean_object* v_inheritedTraceOptions_532_; lean_object* v_currRecDepth_533_; lean_object* v_ref_534_; uint8_t v_suppressElabErrors_535_; uint8_t v_checkDeprecated_536_; uint8_t v_isRecordingDeps_537_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___y_546_; lean_object* v_env_567_; uint8_t v___x_568_; uint8_t v___x_569_; 
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
v___x_367_ = 0;
v___x_368_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12);
v___x_369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15));
v___x_370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16));
v___x_371_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17);
v___x_372_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18);
v___x_373_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
v___x_374_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20);
v___x_375_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21);
v___x_376_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_376_, 0, v___x_334_);
lean_ctor_set(v___x_376_, 1, v___x_368_);
lean_ctor_set(v___x_376_, 2, v___x_369_);
lean_ctor_set(v___x_376_, 3, v___x_370_);
lean_ctor_set(v___x_376_, 4, v___x_371_);
lean_ctor_set(v___x_376_, 5, v___x_372_);
lean_ctor_set(v___x_376_, 6, v___x_373_);
lean_ctor_set(v___x_376_, 7, v___x_374_);
lean_ctor_set(v___x_376_, 8, v___x_375_);
lean_ctor_set(v___x_376_, 9, v___x_338_);
v___x_377_ = lean_io_get_num_heartbeats();
v___x_378_ = lean_st_mk_ref(v___x_376_);
v___x_542_ = l_Lean_inheritedTraceOptions;
v___x_543_ = lean_st_ref_get(v___x_542_);
v___x_544_ = lean_st_ref_get(v___x_378_);
v_env_567_ = lean_ctor_get(v___x_544_, 0);
lean_inc_ref(v_env_567_);
lean_dec(v___x_544_);
v___x_568_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_567_);
lean_dec_ref(v_env_567_);
v___x_569_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__27);
if (v___x_569_ == 0)
{
if (v___x_568_ == 0)
{
v___y_546_ = v___x_335_;
goto v___jp_545_;
}
else
{
v_fileName_523_ = v_fileName_344_;
v_fileMap_524_ = v_fileMap_345_;
v_currNamespace_525_ = v_currNamespace_358_;
v_openDecls_526_ = v_openDecls_359_;
v_initHeartbeats_527_ = v___x_377_;
v_maxHeartbeats_528_ = v___x_362_;
v_quotContext_529_ = v___x_363_;
v_currMacroScope_530_ = v___x_364_;
v_cancelTk_x3f_531_ = v_cancelTk_x3f_347_;
v_inheritedTraceOptions_532_ = v___x_543_;
v_currRecDepth_533_ = v___x_337_;
v_ref_534_ = v___x_365_;
v_suppressElabErrors_535_ = v___x_333_;
v_checkDeprecated_536_ = v___x_367_;
v_isRecordingDeps_537_ = v___x_333_;
goto v___jp_522_;
}
}
else
{
if (v___x_568_ == 0)
{
v_fileName_523_ = v_fileName_344_;
v_fileMap_524_ = v_fileMap_345_;
v_currNamespace_525_ = v_currNamespace_358_;
v_openDecls_526_ = v_openDecls_359_;
v_initHeartbeats_527_ = v___x_377_;
v_maxHeartbeats_528_ = v___x_362_;
v_quotContext_529_ = v___x_363_;
v_currMacroScope_530_ = v___x_364_;
v_cancelTk_x3f_531_ = v_cancelTk_x3f_347_;
v_inheritedTraceOptions_532_ = v___x_543_;
v_currRecDepth_533_ = v___x_337_;
v_ref_534_ = v___x_365_;
v_suppressElabErrors_535_ = v___x_333_;
v_checkDeprecated_536_ = v___x_367_;
v_isRecordingDeps_537_ = v___x_333_;
goto v___jp_522_;
}
else
{
v___y_546_ = v___x_333_;
goto v___jp_545_;
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
v___jp_379_:
{
lean_object* v_toCold_385_; lean_object* v_currRecDepth_386_; lean_object* v_ref_387_; uint8_t v_suppressElabErrors_388_; uint8_t v_checkDeprecated_389_; uint8_t v_isRecordingDeps_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_481_; 
v_toCold_385_ = lean_ctor_get(v___y_383_, 0);
v_currRecDepth_386_ = lean_ctor_get(v___y_383_, 1);
v_ref_387_ = lean_ctor_get(v___y_383_, 2);
v_suppressElabErrors_388_ = lean_ctor_get_uint8(v___y_383_, sizeof(void*)*3 + 2);
v_checkDeprecated_389_ = lean_ctor_get_uint8(v___y_383_, sizeof(void*)*3 + 3);
v_isRecordingDeps_390_ = lean_ctor_get_uint8(v___y_383_, sizeof(void*)*3 + 4);
v_isSharedCheck_481_ = !lean_is_exclusive(v___y_383_);
if (v_isSharedCheck_481_ == 0)
{
v___x_392_ = v___y_383_;
v_isShared_393_ = v_isSharedCheck_481_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_ref_387_);
lean_inc(v_currRecDepth_386_);
lean_inc(v_toCold_385_);
lean_dec(v___y_383_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_481_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_fileName_394_; lean_object* v_fileMap_395_; lean_object* v_currNamespace_396_; lean_object* v_openDecls_397_; lean_object* v_initHeartbeats_398_; lean_object* v_maxHeartbeats_399_; lean_object* v_quotContext_400_; lean_object* v_currMacroScope_401_; lean_object* v_cancelTk_x3f_402_; lean_object* v_inheritedTraceOptions_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_478_; 
v_fileName_394_ = lean_ctor_get(v_toCold_385_, 0);
v_fileMap_395_ = lean_ctor_get(v_toCold_385_, 1);
v_currNamespace_396_ = lean_ctor_get(v_toCold_385_, 4);
v_openDecls_397_ = lean_ctor_get(v_toCold_385_, 5);
v_initHeartbeats_398_ = lean_ctor_get(v_toCold_385_, 6);
v_maxHeartbeats_399_ = lean_ctor_get(v_toCold_385_, 7);
v_quotContext_400_ = lean_ctor_get(v_toCold_385_, 8);
v_currMacroScope_401_ = lean_ctor_get(v_toCold_385_, 9);
v_cancelTk_x3f_402_ = lean_ctor_get(v_toCold_385_, 10);
v_inheritedTraceOptions_403_ = lean_ctor_get(v_toCold_385_, 11);
v_isSharedCheck_478_ = !lean_is_exclusive(v_toCold_385_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; lean_object* v_unused_480_; 
v_unused_479_ = lean_ctor_get(v_toCold_385_, 3);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_toCold_385_, 2);
lean_dec(v_unused_480_);
v___x_405_ = v_toCold_385_;
v_isShared_406_ = v_isSharedCheck_478_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_inheritedTraceOptions_403_);
lean_inc(v_cancelTk_x3f_402_);
lean_inc(v_currMacroScope_401_);
lean_inc(v_quotContext_400_);
lean_inc(v_maxHeartbeats_399_);
lean_inc(v_initHeartbeats_398_);
lean_inc(v_openDecls_397_);
lean_inc(v_currNamespace_396_);
lean_inc(v_fileMap_395_);
lean_inc(v_fileName_394_);
lean_dec(v_toCold_385_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_478_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v___y_381_, v___y_380_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 3, v___x_407_);
lean_ctor_set(v___x_405_, 2, v___y_381_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_fileName_394_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_fileMap_395_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v___y_381_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_currNamespace_396_);
lean_ctor_set(v_reuseFailAlloc_477_, 5, v_openDecls_397_);
lean_ctor_set(v_reuseFailAlloc_477_, 6, v_initHeartbeats_398_);
lean_ctor_set(v_reuseFailAlloc_477_, 7, v_maxHeartbeats_399_);
lean_ctor_set(v_reuseFailAlloc_477_, 8, v_quotContext_400_);
lean_ctor_set(v_reuseFailAlloc_477_, 9, v_currMacroScope_401_);
lean_ctor_set(v_reuseFailAlloc_477_, 10, v_cancelTk_x3f_402_);
lean_ctor_set(v_reuseFailAlloc_477_, 11, v_inheritedTraceOptions_403_);
v___x_409_ = v_reuseFailAlloc_477_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_409_);
v___x_411_ = v___x_392_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_currRecDepth_386_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_ref_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*3 + 2, v_suppressElabErrors_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*3 + 3, v_checkDeprecated_389_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*3 + 4, v_isRecordingDeps_390_);
v___x_411_ = v_reuseFailAlloc_476_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_ctor_set_uint16(v___x_411_, sizeof(void*)*3, v___y_382_);
v___x_412_ = lean_st_mk_ref(v___x_360_);
lean_inc(v___x_412_);
v___x_413_ = lean_apply_5(v_x_328_, v___x_340_, v___x_412_, v___x_411_, v___y_384_, lean_box(0));
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_460_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_460_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_460_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_460_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_traceState_421_; lean_object* v_traceState_422_; lean_object* v_env_423_; lean_object* v_messages_424_; lean_object* v_scopes_425_; lean_object* v_usedQuotCtxts_426_; lean_object* v_nextMacroScope_427_; lean_object* v_maxRecDepth_428_; lean_object* v_ngen_429_; lean_object* v_auxDeclNGen_430_; lean_object* v_infoState_431_; lean_object* v_snapshotTasks_432_; lean_object* v_prevLinterStates_433_; lean_object* v_codeQualityEntryTasks_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_458_; 
v___x_418_ = lean_st_ref_get(v___x_412_);
lean_dec(v___x_412_);
lean_dec(v___x_418_);
v___x_419_ = lean_st_ref_get(v___x_378_);
lean_dec(v___x_378_);
v___x_420_ = lean_st_ref_take(v_a_330_);
v_traceState_421_ = lean_ctor_get(v___x_420_, 9);
lean_inc_ref(v_traceState_421_);
v_traceState_422_ = lean_ctor_get(v___x_419_, 4);
lean_inc_ref(v_traceState_422_);
v_env_423_ = lean_ctor_get(v___x_420_, 0);
v_messages_424_ = lean_ctor_get(v___x_420_, 1);
v_scopes_425_ = lean_ctor_get(v___x_420_, 2);
v_usedQuotCtxts_426_ = lean_ctor_get(v___x_420_, 3);
v_nextMacroScope_427_ = lean_ctor_get(v___x_420_, 4);
v_maxRecDepth_428_ = lean_ctor_get(v___x_420_, 5);
v_ngen_429_ = lean_ctor_get(v___x_420_, 6);
v_auxDeclNGen_430_ = lean_ctor_get(v___x_420_, 7);
v_infoState_431_ = lean_ctor_get(v___x_420_, 8);
v_snapshotTasks_432_ = lean_ctor_get(v___x_420_, 10);
v_prevLinterStates_433_ = lean_ctor_get(v___x_420_, 11);
v_codeQualityEntryTasks_434_ = lean_ctor_get(v___x_420_, 12);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_458_ == 0)
{
lean_object* v_unused_459_; 
v_unused_459_ = lean_ctor_get(v___x_420_, 9);
lean_dec(v_unused_459_);
v___x_436_ = v___x_420_;
v_isShared_437_ = v_isSharedCheck_458_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_codeQualityEntryTasks_434_);
lean_inc(v_prevLinterStates_433_);
lean_inc(v_snapshotTasks_432_);
lean_inc(v_infoState_431_);
lean_inc(v_auxDeclNGen_430_);
lean_inc(v_ngen_429_);
lean_inc(v_maxRecDepth_428_);
lean_inc(v_nextMacroScope_427_);
lean_inc(v_usedQuotCtxts_426_);
lean_inc(v_scopes_425_);
lean_inc(v_messages_424_);
lean_inc(v_env_423_);
lean_dec(v___x_420_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_458_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_messages_438_; uint64_t v_tid_439_; lean_object* v_traces_440_; lean_object* v_traces_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_457_; 
v_messages_438_ = lean_ctor_get(v___x_419_, 7);
lean_inc_ref(v_messages_438_);
lean_dec(v___x_419_);
v_tid_439_ = lean_ctor_get_uint64(v_traceState_421_, sizeof(void*)*1);
v_traces_440_ = lean_ctor_get(v_traceState_421_, 0);
lean_inc_ref(v_traces_440_);
lean_dec_ref(v_traceState_421_);
v_traces_441_ = lean_ctor_get(v_traceState_422_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_traceState_422_);
if (v_isSharedCheck_457_ == 0)
{
v___x_443_ = v_traceState_422_;
v_isShared_444_ = v_isSharedCheck_457_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_traces_441_);
lean_dec(v_traceState_422_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_457_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_445_ = l_Lean_MessageLog_append(v_messages_424_, v_messages_438_);
v___x_446_ = l_Lean_PersistentArray_append___redArg(v_traces_440_, v_traces_441_);
lean_dec_ref(v_traces_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_446_);
v___x_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_456_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
lean_ctor_set_uint64(v___x_448_, sizeof(void*)*1, v_tid_439_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 9, v___x_448_);
lean_ctor_set(v___x_436_, 1, v___x_445_);
v___x_450_ = v___x_436_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_env_423_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_scopes_425_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_usedQuotCtxts_426_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_nextMacroScope_427_);
lean_ctor_set(v_reuseFailAlloc_455_, 5, v_maxRecDepth_428_);
lean_ctor_set(v_reuseFailAlloc_455_, 6, v_ngen_429_);
lean_ctor_set(v_reuseFailAlloc_455_, 7, v_auxDeclNGen_430_);
lean_ctor_set(v_reuseFailAlloc_455_, 8, v_infoState_431_);
lean_ctor_set(v_reuseFailAlloc_455_, 9, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_455_, 10, v_snapshotTasks_432_);
lean_ctor_set(v_reuseFailAlloc_455_, 11, v_prevLinterStates_433_);
lean_ctor_set(v_reuseFailAlloc_455_, 12, v_codeQualityEntryTasks_434_);
v___x_450_ = v_reuseFailAlloc_455_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_st_ref_put(v_a_330_, v___x_450_);
if (v_isShared_417_ == 0)
{
v___x_453_ = v___x_416_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_414_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_461_; 
lean_dec(v___x_412_);
lean_dec(v___x_378_);
v_a_461_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_413_, 1);
if (lean_obj_tag(v_a_461_) == 0)
{
lean_object* v_msg_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_msg_462_ = lean_ctor_get(v_a_461_, 1);
lean_inc_ref(v_msg_462_);
lean_dec_ref_known(v_a_461_, 2);
v___x_463_ = l_Lean_MessageData_toString(v_msg_462_);
v___x_464_ = lean_mk_io_user_error(v___x_463_);
v_a_349_ = v___x_464_;
goto v___jp_348_;
}
else
{
lean_object* v_id_465_; lean_object* v___x_466_; 
v_id_465_ = lean_ctor_get(v_a_461_, 0);
lean_inc(v_id_465_);
lean_dec_ref_known(v_a_461_, 2);
v___x_466_ = l_Lean_InternalExceptionId_getName(v_id_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_id_465_);
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_469_ = l_Lean_Name_toString(v_a_467_, v___x_335_);
v___x_470_ = lean_string_append(v___x_468_, v___x_469_);
lean_dec_ref(v___x_469_);
v_a_356_ = v___x_470_;
goto v___jp_355_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref_known(v___x_466_, 1);
v___x_471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23));
v___x_472_ = l_Nat_reprFast(v_id_465_);
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
lean_dec_ref(v___x_472_);
v___x_474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24));
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
v_a_356_ = v___x_475_;
goto v___jp_355_;
}
}
}
}
}
}
}
}
v___jp_482_:
{
lean_object* v___x_489_; lean_object* v_env_490_; lean_object* v_nextMacroScope_491_; lean_object* v_ngen_492_; lean_object* v_auxDeclNGen_493_; lean_object* v_traceState_494_; lean_object* v_recordedDeps_495_; lean_object* v_messages_496_; lean_object* v_infoState_497_; lean_object* v_snapshotTasks_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_507_; 
v___x_489_ = lean_st_ref_take(v___y_488_);
v_env_490_ = lean_ctor_get(v___x_489_, 0);
v_nextMacroScope_491_ = lean_ctor_get(v___x_489_, 1);
v_ngen_492_ = lean_ctor_get(v___x_489_, 2);
v_auxDeclNGen_493_ = lean_ctor_get(v___x_489_, 3);
v_traceState_494_ = lean_ctor_get(v___x_489_, 4);
v_recordedDeps_495_ = lean_ctor_get(v___x_489_, 6);
v_messages_496_ = lean_ctor_get(v___x_489_, 7);
v_infoState_497_ = lean_ctor_get(v___x_489_, 8);
v_snapshotTasks_498_ = lean_ctor_get(v___x_489_, 9);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_489_, 5);
lean_dec(v_unused_508_);
v___x_500_ = v___x_489_;
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snapshotTasks_498_);
lean_inc(v_infoState_497_);
lean_inc(v_messages_496_);
lean_inc(v_recordedDeps_495_);
lean_inc(v_traceState_494_);
lean_inc(v_auxDeclNGen_493_);
lean_inc(v_ngen_492_);
lean_inc(v_nextMacroScope_491_);
lean_inc(v_env_490_);
lean_dec(v___x_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = l_Lean_Kernel_enableDiag(v_env_490_, v___y_487_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 5, v___x_372_);
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_nextMacroScope_491_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_ngen_492_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_auxDeclNGen_493_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_traceState_494_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_506_, 6, v_recordedDeps_495_);
lean_ctor_set(v_reuseFailAlloc_506_, 7, v_messages_496_);
lean_ctor_set(v_reuseFailAlloc_506_, 8, v_infoState_497_);
lean_ctor_set(v_reuseFailAlloc_506_, 9, v_snapshotTasks_498_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_st_ref_put(v___y_488_, v___x_504_);
v___y_380_ = v___y_483_;
v___y_381_ = v___y_484_;
v___y_382_ = v___y_486_;
v___y_383_ = v___y_485_;
v___y_384_ = v___y_488_;
goto v___jp_379_;
}
}
}
v___jp_509_:
{
uint16_t v___x_514_; lean_object* v___x_515_; lean_object* v_env_516_; uint8_t v___x_517_; uint16_t v___x_518_; uint16_t v___x_519_; uint16_t v___x_520_; uint8_t v___x_521_; 
v___x_514_ = l_Lean_OptionFlags_ofOptions(v___y_513_);
v___x_515_ = lean_st_ref_get(v___y_512_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref(v_env_516_);
lean_dec(v___x_515_);
v___x_517_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_516_);
lean_dec_ref(v_env_516_);
v___x_518_ = 512;
v___x_519_ = lean_uint16_land(v___x_514_, v___x_518_);
v___x_520_ = 0;
v___x_521_ = lean_uint16_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
if (v___x_517_ == 0)
{
v___y_483_ = v___y_510_;
v___y_484_ = v___y_513_;
v___y_485_ = v___y_511_;
v___y_486_ = v___x_514_;
v___y_487_ = v___x_335_;
v___y_488_ = v___y_512_;
goto v___jp_482_;
}
else
{
v___y_380_ = v___y_510_;
v___y_381_ = v___y_513_;
v___y_382_ = v___x_514_;
v___y_383_ = v___y_511_;
v___y_384_ = v___y_512_;
goto v___jp_379_;
}
}
else
{
if (v___x_517_ == 0)
{
v___y_380_ = v___y_510_;
v___y_381_ = v___y_513_;
v___y_382_ = v___x_514_;
v___y_383_ = v___y_511_;
v___y_384_ = v___y_512_;
goto v___jp_379_;
}
else
{
v___y_483_ = v___y_510_;
v___y_484_ = v___y_513_;
v___y_485_ = v___y_511_;
v___y_486_ = v___x_514_;
v___y_487_ = v___x_333_;
v___y_488_ = v___y_512_;
goto v___jp_482_;
}
}
}
v___jp_522_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = l_Lean_maxRecDepth;
v___x_539_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25);
lean_inc(v_cancelTk_x3f_531_);
lean_inc(v_currMacroScope_530_);
lean_inc(v_quotContext_529_);
lean_inc(v_maxHeartbeats_528_);
lean_inc_ref(v_fileMap_524_);
lean_inc_ref(v_fileName_523_);
v___x_540_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_540_, 0, v_fileName_523_);
lean_ctor_set(v___x_540_, 1, v_fileMap_524_);
lean_ctor_set(v___x_540_, 2, v___x_361_);
lean_ctor_set(v___x_540_, 3, v___x_539_);
lean_ctor_set(v___x_540_, 4, v_currNamespace_525_);
lean_ctor_set(v___x_540_, 5, v_openDecls_526_);
lean_ctor_set(v___x_540_, 6, v_initHeartbeats_527_);
lean_ctor_set(v___x_540_, 7, v_maxHeartbeats_528_);
lean_ctor_set(v___x_540_, 8, v_quotContext_529_);
lean_ctor_set(v___x_540_, 9, v_currMacroScope_530_);
lean_ctor_set(v___x_540_, 10, v_cancelTk_x3f_531_);
lean_ctor_set(v___x_540_, 11, v_inheritedTraceOptions_532_);
lean_inc(v_ref_534_);
v___x_541_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v_currRecDepth_533_);
lean_ctor_set(v___x_541_, 2, v_ref_534_);
lean_ctor_set_uint16(v___x_541_, sizeof(void*)*3, v___x_366_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*3 + 2, v_suppressElabErrors_535_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*3 + 3, v_checkDeprecated_536_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*3 + 4, v_isRecordingDeps_537_);
lean_inc(v___x_378_);
v___y_510_ = v___x_538_;
v___y_511_ = v___x_541_;
v___y_512_ = v___x_378_;
v___y_513_ = v_opts_326_;
goto v___jp_509_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v_env_548_; lean_object* v_nextMacroScope_549_; lean_object* v_ngen_550_; lean_object* v_auxDeclNGen_551_; lean_object* v_traceState_552_; lean_object* v_recordedDeps_553_; lean_object* v_messages_554_; lean_object* v_infoState_555_; lean_object* v_snapshotTasks_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_565_; 
v___x_547_ = lean_st_ref_take(v___x_378_);
v_env_548_ = lean_ctor_get(v___x_547_, 0);
v_nextMacroScope_549_ = lean_ctor_get(v___x_547_, 1);
v_ngen_550_ = lean_ctor_get(v___x_547_, 2);
v_auxDeclNGen_551_ = lean_ctor_get(v___x_547_, 3);
v_traceState_552_ = lean_ctor_get(v___x_547_, 4);
v_recordedDeps_553_ = lean_ctor_get(v___x_547_, 6);
v_messages_554_ = lean_ctor_get(v___x_547_, 7);
v_infoState_555_ = lean_ctor_get(v___x_547_, 8);
v_snapshotTasks_556_ = lean_ctor_get(v___x_547_, 9);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v___x_547_, 5);
lean_dec(v_unused_566_);
v___x_558_ = v___x_547_;
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snapshotTasks_556_);
lean_inc(v_infoState_555_);
lean_inc(v_messages_554_);
lean_inc(v_recordedDeps_553_);
lean_inc(v_traceState_552_);
lean_inc(v_auxDeclNGen_551_);
lean_inc(v_ngen_550_);
lean_inc(v_nextMacroScope_549_);
lean_inc(v_env_548_);
lean_dec(v___x_547_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = l_Lean_Kernel_enableDiag(v_env_548_, v___y_546_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 5, v___x_372_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_nextMacroScope_549_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_ngen_550_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_auxDeclNGen_551_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_traceState_552_);
lean_ctor_set(v_reuseFailAlloc_564_, 5, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_564_, 6, v_recordedDeps_553_);
lean_ctor_set(v_reuseFailAlloc_564_, 7, v_messages_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 8, v_infoState_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 9, v_snapshotTasks_556_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_st_ref_put(v___x_378_, v___x_562_);
v_fileName_523_ = v_fileName_344_;
v_fileMap_524_ = v_fileMap_345_;
v_currNamespace_525_ = v_currNamespace_358_;
v_openDecls_526_ = v_openDecls_359_;
v_initHeartbeats_527_ = v___x_377_;
v_maxHeartbeats_528_ = v___x_362_;
v_quotContext_529_ = v___x_363_;
v_currMacroScope_530_ = v___x_364_;
v_cancelTk_x3f_531_ = v_cancelTk_x3f_347_;
v_inheritedTraceOptions_532_ = v___x_543_;
v_currRecDepth_533_ = v___x_337_;
v_ref_534_ = v___x_365_;
v_suppressElabErrors_535_ = v___x_333_;
v_checkDeprecated_536_ = v___x_367_;
v_isRecordingDeps_537_ = v___x_333_;
goto v___jp_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_570_, lean_object* v_mctx_571_, lean_object* v_lctx_572_, lean_object* v_opts_573_, lean_object* v_namingCtx_574_, lean_object* v_x_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_570_, v_mctx_571_, v_lctx_572_, v_opts_573_, v_namingCtx_574_, v_x_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_580_, lean_object* v_env_581_, lean_object* v_mctx_582_, lean_object* v_lctx_583_, lean_object* v_opts_584_, lean_object* v_namingCtx_585_, lean_object* v_x_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_581_, v_mctx_582_, v_lctx_583_, v_opts_584_, v_namingCtx_585_, v_x_586_, v_a_587_, v_a_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_591_, lean_object* v_env_592_, lean_object* v_mctx_593_, lean_object* v_lctx_594_, lean_object* v_opts_595_, lean_object* v_namingCtx_596_, lean_object* v_x_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_591_, v_env_592_, v_mctx_593_, v_lctx_594_, v_opts_595_, v_namingCtx_596_, v_x_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_601_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Syntax_getKind(v_stx_605_);
if (lean_obj_tag(v___x_606_) == 1)
{
lean_object* v_pre_607_; 
v_pre_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_pre_607_);
if (lean_obj_tag(v_pre_607_) == 1)
{
lean_object* v_pre_608_; 
v_pre_608_ = lean_ctor_get(v_pre_607_, 0);
lean_inc(v_pre_608_);
if (lean_obj_tag(v_pre_608_) == 1)
{
lean_object* v_pre_609_; 
v_pre_609_ = lean_ctor_get(v_pre_608_, 0);
lean_inc(v_pre_609_);
if (lean_obj_tag(v_pre_609_) == 1)
{
lean_object* v_pre_610_; 
v_pre_610_ = lean_ctor_get(v_pre_609_, 0);
if (lean_obj_tag(v_pre_610_) == 0)
{
lean_object* v_str_611_; lean_object* v_str_612_; lean_object* v_str_613_; lean_object* v_str_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_str_611_ = lean_ctor_get(v___x_606_, 1);
lean_inc_ref(v_str_611_);
lean_dec_ref_known(v___x_606_, 2);
v_str_612_ = lean_ctor_get(v_pre_607_, 1);
lean_inc_ref(v_str_612_);
lean_dec_ref_known(v_pre_607_, 2);
v_str_613_ = lean_ctor_get(v_pre_608_, 1);
lean_inc_ref(v_str_613_);
lean_dec_ref_known(v_pre_608_, 2);
v_str_614_ = lean_ctor_get(v_pre_609_, 1);
lean_inc_ref(v_str_614_);
lean_dec_ref_known(v_pre_609_, 2);
v___x_615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_616_ = lean_string_dec_eq(v_str_614_, v___x_615_);
lean_dec_ref(v_str_614_);
if (v___x_616_ == 0)
{
lean_dec_ref(v_str_613_);
lean_dec_ref(v_str_612_);
lean_dec_ref(v_str_611_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_618_ = lean_string_dec_eq(v_str_613_, v___x_617_);
lean_dec_ref(v_str_613_);
if (v___x_618_ == 0)
{
lean_dec_ref(v_str_612_);
lean_dec_ref(v_str_611_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_620_ = lean_string_dec_eq(v_str_612_, v___x_619_);
lean_dec_ref(v_str_612_);
if (v___x_620_ == 0)
{
lean_dec_ref(v_str_611_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_622_ = lean_string_dec_eq(v_str_611_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_624_ = lean_string_dec_eq(v_str_611_, v___x_623_);
lean_dec_ref(v_str_611_);
return v___x_624_;
}
else
{
lean_dec_ref(v_str_611_);
return v___x_622_;
}
}
}
}
}
else
{
uint8_t v___x_625_; 
lean_dec_ref_known(v_pre_609_, 2);
lean_dec_ref_known(v_pre_608_, 2);
lean_dec_ref_known(v_pre_607_, 2);
lean_dec_ref_known(v___x_606_, 2);
v___x_625_ = 0;
return v___x_625_;
}
}
else
{
uint8_t v___x_626_; 
lean_dec_ref_known(v_pre_608_, 2);
lean_dec(v_pre_609_);
lean_dec_ref_known(v_pre_607_, 2);
lean_dec_ref_known(v___x_606_, 2);
v___x_626_ = 0;
return v___x_626_;
}
}
else
{
uint8_t v___x_627_; 
lean_dec(v_pre_608_);
lean_dec_ref_known(v_pre_607_, 2);
lean_dec_ref_known(v___x_606_, 2);
v___x_627_ = 0;
return v___x_627_;
}
}
else
{
uint8_t v___x_628_; 
lean_dec_ref_known(v___x_606_, 2);
lean_dec(v_pre_607_);
v___x_628_ = 0;
return v___x_628_;
}
}
else
{
uint8_t v___x_629_; 
lean_dec(v___x_606_);
v___x_629_ = 0;
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_630_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_tag_nat(v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl___boxed(lean_object* v_x_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___impl(v_x_635_);
lean_dec(v_x_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_637_, lean_object* v_k_638_){
_start:
{
if (lean_obj_tag(v_t_637_) == 0)
{
lean_object* v_tacticSeq_639_; lean_object* v_insertPos_640_; lean_object* v___x_641_; 
v_tacticSeq_639_ = lean_ctor_get(v_t_637_, 0);
lean_inc(v_tacticSeq_639_);
v_insertPos_640_ = lean_ctor_get(v_t_637_, 1);
lean_inc(v_insertPos_640_);
lean_dec_ref_known(v_t_637_, 2);
v___x_641_ = lean_apply_2(v_k_638_, v_tacticSeq_639_, v_insertPos_640_);
return v___x_641_;
}
else
{
return v_k_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_642_, lean_object* v_ctorIdx_643_, lean_object* v_t_644_, lean_object* v_h_645_, lean_object* v_k_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_644_, v_k_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_648_, lean_object* v_ctorIdx_649_, lean_object* v_t_650_, lean_object* v_h_651_, lean_object* v_k_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_648_, v_ctorIdx_649_, v_t_650_, v_h_651_, v_k_652_);
lean_dec(v_ctorIdx_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_654_, lean_object* v_unsolvedGoal_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_654_, v_unsolvedGoal_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_657_, lean_object* v_t_658_, lean_object* v_h_659_, lean_object* v_unsolvedGoal_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_658_, v_unsolvedGoal_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_662_, lean_object* v_sorryTactic_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_662_, v_sorryTactic_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_665_, lean_object* v_t_666_, lean_object* v_h_667_, lean_object* v_sorryTactic_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_666_, v_sorryTactic_668_);
return v___x_669_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_673_; lean_object* v___x_674_; 
v___x_673_ = 32;
v___x_674_ = lean_box_uint32(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_675_, lean_object* v_fileMap_676_){
_start:
{
uint8_t v___x_677_; lean_object* v___x_678_; 
v___x_677_ = 0;
v___x_678_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_675_, v___x_677_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_680_; 
v_val_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v___x_678_, 1);
v___x_680_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_675_, v___x_677_);
if (lean_obj_tag(v___x_680_) == 1)
{
lean_object* v_val_681_; lean_object* v_startPos_682_; lean_object* v_line_683_; lean_object* v_column_684_; lean_object* v_endPos_685_; lean_object* v_line_686_; uint8_t v___x_687_; 
v_val_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v___x_680_, 1);
lean_inc_ref(v_fileMap_676_);
v_startPos_682_ = l_Lean_FileMap_toPosition(v_fileMap_676_, v_val_679_);
lean_dec(v_val_679_);
v_line_683_ = lean_ctor_get(v_startPos_682_, 0);
lean_inc(v_line_683_);
v_column_684_ = lean_ctor_get(v_startPos_682_, 1);
lean_inc(v_column_684_);
lean_dec_ref(v_startPos_682_);
v_endPos_685_ = l_Lean_FileMap_toPosition(v_fileMap_676_, v_val_681_);
lean_dec(v_val_681_);
v_line_686_ = lean_ctor_get(v_endPos_685_, 0);
lean_inc(v_line_686_);
lean_dec_ref(v_endPos_685_);
v___x_687_ = lean_nat_dec_eq(v_line_683_, v_line_686_);
lean_dec(v_line_686_);
lean_dec(v_line_683_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_689_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_690_ = l_List_replicateTR___redArg(v_column_684_, v___x_689_);
v___x_691_ = lean_string_mk(v___x_690_);
v___x_692_ = lean_string_append(v___x_688_, v___x_691_);
lean_dec_ref(v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; 
lean_dec(v_column_684_);
v___x_693_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_693_;
}
}
else
{
lean_object* v___x_694_; 
lean_dec(v___x_680_);
lean_dec(v_val_679_);
lean_dec_ref(v_fileMap_676_);
v___x_694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_694_;
}
}
else
{
lean_object* v___x_695_; 
lean_dec(v___x_678_);
lean_dec_ref(v_fileMap_676_);
v___x_695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_696_, lean_object* v_fileMap_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_696_, v_fileMap_697_);
lean_dec(v_tacticSeq_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_705_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
lean_inc(v_p_703_);
v___x_706_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_p_703_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
lean_ctor_set(v___x_706_, 3, v_p_703_);
v___x_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_704_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_start_711_; lean_object* v_stop_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
v___x_709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1));
v_start_711_ = lean_ctor_get(v_range_708_, 0);
v_stop_712_ = lean_ctor_get(v_range_708_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_range_708_);
if (v_isSharedCheck_720_ == 0)
{
v___x_714_ = v_range_708_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_stop_712_);
lean_inc(v_start_711_);
lean_dec(v_range_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_716_, 0, v___x_710_);
lean_ctor_set(v___x_716_, 1, v_start_711_);
lean_ctor_set(v___x_716_, 2, v___x_710_);
lean_ctor_set(v___x_716_, 3, v_stop_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 2);
lean_ctor_set(v___x_714_, 1, v___x_709_);
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_709_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_721_, lean_object* v_nc_x3f_722_, lean_object* v_msg_723_, lean_object* v_acc_724_){
_start:
{
switch(lean_obj_tag(v_msg_723_))
{
case 3:
{
lean_object* v_a_725_; lean_object* v_a_726_; lean_object* v___x_727_; 
lean_dec(v_mc_x3f_721_);
v_a_725_ = lean_ctor_get(v_msg_723_, 0);
v_a_726_ = lean_ctor_get(v_msg_723_, 1);
lean_inc_ref(v_a_725_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_a_725_);
v_mc_x3f_721_ = v___x_727_;
v_msg_723_ = v_a_726_;
goto _start;
}
case 4:
{
lean_object* v_a_729_; lean_object* v_a_730_; lean_object* v___x_731_; 
lean_dec(v_nc_x3f_722_);
v_a_729_ = lean_ctor_get(v_msg_723_, 0);
v_a_730_ = lean_ctor_get(v_msg_723_, 1);
lean_inc_ref(v_a_729_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_a_729_);
v_nc_x3f_722_ = v___x_731_;
v_msg_723_ = v_a_730_;
goto _start;
}
case 5:
{
lean_object* v_a_733_; 
v_a_733_ = lean_ctor_get(v_msg_723_, 1);
v_msg_723_ = v_a_733_;
goto _start;
}
case 6:
{
lean_object* v_a_735_; 
v_a_735_ = lean_ctor_get(v_msg_723_, 0);
v_msg_723_ = v_a_735_;
goto _start;
}
case 8:
{
lean_object* v_a_737_; 
v_a_737_ = lean_ctor_get(v_msg_723_, 1);
v_msg_723_ = v_a_737_;
goto _start;
}
case 7:
{
lean_object* v_a_739_; lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_739_ = lean_ctor_get(v_msg_723_, 0);
v_a_740_ = lean_ctor_get(v_msg_723_, 1);
lean_inc(v_nc_x3f_722_);
lean_inc(v_mc_x3f_721_);
v___x_741_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_721_, v_nc_x3f_722_, v_a_739_, v_acc_724_);
v_msg_723_ = v_a_740_;
v_acc_724_ = v___x_741_;
goto _start;
}
case 2:
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v_msg_723_, 1);
v_msg_723_ = v_a_743_;
goto _start;
}
case 9:
{
lean_object* v_msg_745_; lean_object* v_children_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_msg_745_ = lean_ctor_get(v_msg_723_, 1);
v_children_746_ = lean_ctor_get(v_msg_723_, 2);
lean_inc(v_nc_x3f_722_);
lean_inc(v_mc_x3f_721_);
v___x_747_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_721_, v_nc_x3f_722_, v_msg_745_, v_acc_724_);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_array_get_size(v_children_746_);
v___x_750_ = lean_nat_dec_lt(v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec(v_nc_x3f_722_);
lean_dec(v_mc_x3f_721_);
return v___x_747_;
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_of_nat(v___x_749_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_721_, v_nc_x3f_722_, v_children_746_, v___x_751_, v___x_752_, v___x_747_);
return v___x_753_;
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_721_) == 1)
{
if (lean_obj_tag(v_nc_x3f_722_) == 1)
{
lean_object* v_a_754_; lean_object* v_val_755_; lean_object* v_val_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_754_ = lean_ctor_get(v_msg_723_, 0);
v_val_755_ = lean_ctor_get(v_mc_x3f_721_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v_mc_x3f_721_, 1);
v_val_756_ = lean_ctor_get(v_nc_x3f_722_, 0);
lean_inc(v_val_756_);
lean_dec_ref_known(v_nc_x3f_722_, 1);
lean_inc(v_a_754_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_val_756_);
lean_ctor_set(v___x_757_, 1, v_a_754_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_val_755_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_array_push(v_acc_724_, v___x_758_);
return v___x_759_;
}
else
{
lean_dec_ref_known(v_mc_x3f_721_, 1);
lean_dec(v_nc_x3f_722_);
return v_acc_724_;
}
}
else
{
lean_dec(v_nc_x3f_722_);
lean_dec(v_mc_x3f_721_);
return v_acc_724_;
}
}
default: 
{
lean_dec(v_nc_x3f_722_);
lean_dec(v_mc_x3f_721_);
return v_acc_724_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_760_, lean_object* v_nc_x3f_761_, lean_object* v_as_762_, size_t v_i_763_, size_t v_stop_764_, lean_object* v_b_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_eq(v_i_763_, v_stop_764_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; size_t v___x_769_; size_t v___x_770_; 
v___x_767_ = lean_array_uget_borrowed(v_as_762_, v_i_763_);
lean_inc(v_nc_x3f_761_);
lean_inc(v_mc_x3f_760_);
v___x_768_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_760_, v_nc_x3f_761_, v___x_767_, v_b_765_);
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_add(v_i_763_, v___x_769_);
v_i_763_ = v___x_770_;
v_b_765_ = v___x_768_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_761_);
lean_dec(v_mc_x3f_760_);
return v_b_765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_772_, lean_object* v_nc_x3f_773_, lean_object* v_as_774_, lean_object* v_i_775_, lean_object* v_stop_776_, lean_object* v_b_777_){
_start:
{
size_t v_i_boxed_778_; size_t v_stop_boxed_779_; lean_object* v_res_780_; 
v_i_boxed_778_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_stop_boxed_779_ = lean_unbox_usize(v_stop_776_);
lean_dec(v_stop_776_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_772_, v_nc_x3f_773_, v_as_774_, v_i_boxed_778_, v_stop_boxed_779_, v_b_777_);
lean_dec_ref(v_as_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_781_, lean_object* v_nc_x3f_782_, lean_object* v_msg_783_, lean_object* v_acc_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_781_, v_nc_x3f_782_, v_msg_783_, v_acc_784_);
lean_dec_ref(v_msg_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_box(0);
v___x_790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_791_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_789_, v___x_789_, v_msg_788_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_792_);
lean_dec_ref(v_msg_792_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_796_, lean_object* v_stx_797_){
_start:
{
lean_object* v___x_798_; 
lean_inc(v_stx_797_);
v___x_798_ = l_Lean_Syntax_getKind(v_stx_797_);
if (lean_obj_tag(v___x_798_) == 1)
{
lean_object* v_pre_799_; 
v_pre_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_pre_799_);
if (lean_obj_tag(v_pre_799_) == 1)
{
lean_object* v_pre_800_; 
v_pre_800_ = lean_ctor_get(v_pre_799_, 0);
lean_inc(v_pre_800_);
if (lean_obj_tag(v_pre_800_) == 1)
{
lean_object* v_pre_801_; 
v_pre_801_ = lean_ctor_get(v_pre_800_, 0);
lean_inc(v_pre_801_);
if (lean_obj_tag(v_pre_801_) == 1)
{
lean_object* v_pre_802_; 
v_pre_802_ = lean_ctor_get(v_pre_801_, 0);
if (lean_obj_tag(v_pre_802_) == 0)
{
lean_object* v_str_803_; lean_object* v_str_804_; lean_object* v_str_805_; lean_object* v_str_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_str_803_ = lean_ctor_get(v___x_798_, 1);
lean_inc_ref(v_str_803_);
lean_dec_ref_known(v___x_798_, 2);
v_str_804_ = lean_ctor_get(v_pre_799_, 1);
lean_inc_ref(v_str_804_);
lean_dec_ref_known(v_pre_799_, 2);
v_str_805_ = lean_ctor_get(v_pre_800_, 1);
lean_inc_ref(v_str_805_);
lean_dec_ref_known(v_pre_800_, 2);
v_str_806_ = lean_ctor_get(v_pre_801_, 1);
lean_inc_ref(v_str_806_);
lean_dec_ref_known(v_pre_801_, 2);
v___x_807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_808_ = lean_string_dec_eq(v_str_806_, v___x_807_);
lean_dec_ref(v_str_806_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v_str_805_);
lean_dec_ref(v_str_804_);
lean_dec_ref(v_str_803_);
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_809_ = lean_box(0);
return v___x_809_;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_811_ = lean_string_dec_eq(v_str_805_, v___x_810_);
lean_dec_ref(v_str_805_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec_ref(v_str_804_);
lean_dec_ref(v_str_803_);
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_812_ = lean_box(0);
return v___x_812_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_814_ = lean_string_dec_eq(v_str_804_, v___x_813_);
lean_dec_ref(v_str_804_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_dec_ref(v_str_803_);
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_815_ = lean_box(0);
return v___x_815_;
}
else
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_817_ = lean_string_dec_eq(v_str_803_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_819_ = lean_string_dec_eq(v_str_803_, v___x_818_);
lean_dec_ref(v_str_803_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_820_ = lean_box(0);
return v___x_820_;
}
else
{
lean_object* v___x_821_; lean_object* v_body_822_; lean_object* v___y_824_; lean_object* v___x_827_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v_body_822_ = l_Lean_Syntax_getArg(v_stx_797_, v___x_821_);
v___x_827_ = l_Lean_Syntax_getTailPos_x3f(v_body_822_, v___x_817_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_unsigned_to_nat(2u);
v___x_829_ = l_Lean_Syntax_getArg(v_stx_797_, v___x_828_);
lean_dec(v_stx_797_);
v___x_830_ = l_Lean_Syntax_getPos_x3f(v___x_829_, v___x_817_);
lean_dec(v___x_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_stop_831_; 
v_stop_831_ = lean_ctor_get(v_range_796_, 1);
lean_inc(v_stop_831_);
lean_dec_ref(v_range_796_);
v___y_824_ = v_stop_831_;
goto v___jp_823_;
}
else
{
lean_object* v_val_832_; 
lean_dec_ref(v_range_796_);
v_val_832_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v___x_830_, 1);
v___y_824_ = v_val_832_;
goto v___jp_823_;
}
}
else
{
lean_object* v_val_833_; 
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v_val_833_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v___x_827_, 1);
v___y_824_ = v_val_833_;
goto v___jp_823_;
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_body_822_);
lean_ctor_set(v___x_825_, 1, v___y_824_);
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
else
{
lean_object* v___x_834_; lean_object* v_body_835_; lean_object* v___y_837_; uint8_t v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v_str_803_);
v___x_834_ = lean_unsigned_to_nat(0u);
v_body_835_ = l_Lean_Syntax_getArg(v_stx_797_, v___x_834_);
lean_dec(v_stx_797_);
v___x_840_ = 0;
v___x_841_ = l_Lean_Syntax_getTailPos_x3f(v_body_835_, v___x_840_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_stop_842_; 
v_stop_842_ = lean_ctor_get(v_range_796_, 1);
lean_inc(v_stop_842_);
lean_dec_ref(v_range_796_);
v___y_837_ = v_stop_842_;
goto v___jp_836_;
}
else
{
lean_object* v_val_843_; 
lean_dec_ref(v_range_796_);
v_val_843_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_841_, 1);
v___y_837_ = v_val_843_;
goto v___jp_836_;
}
v___jp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_body_835_);
lean_ctor_set(v___x_838_, 1, v___y_837_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
}
}
}
}
else
{
lean_object* v___x_844_; 
lean_dec_ref_known(v_pre_801_, 2);
lean_dec_ref_known(v_pre_800_, 2);
lean_dec_ref_known(v_pre_799_, 2);
lean_dec_ref_known(v___x_798_, 2);
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_844_ = lean_box(0);
return v___x_844_;
}
}
else
{
lean_object* v___x_845_; 
lean_dec_ref_known(v_pre_800_, 2);
lean_dec(v_pre_801_);
lean_dec_ref_known(v_pre_799_, 2);
lean_dec_ref_known(v___x_798_, 2);
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_845_ = lean_box(0);
return v___x_845_;
}
}
else
{
lean_object* v___x_846_; 
lean_dec_ref_known(v_pre_799_, 2);
lean_dec(v_pre_800_);
lean_dec_ref_known(v___x_798_, 2);
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_846_ = lean_box(0);
return v___x_846_;
}
}
else
{
lean_object* v___x_847_; 
lean_dec_ref_known(v___x_798_, 2);
lean_dec(v_pre_799_);
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_847_ = lean_box(0);
return v___x_847_;
}
}
else
{
lean_object* v___x_848_; 
lean_dec(v___x_798_);
lean_dec(v_stx_797_);
lean_dec_ref(v_range_796_);
v___x_848_ = lean_box(0);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_852_, lean_object* v_stx_853_){
_start:
{
lean_object* v___x_854_; 
lean_inc(v_stx_853_);
lean_inc_ref(v_range_852_);
v___x_854_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_852_, v_stx_853_);
if (lean_obj_tag(v___x_854_) == 1)
{
lean_dec(v_stx_853_);
lean_dec_ref(v_range_852_);
return v___x_854_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; size_t v_sz_858_; size_t v___x_859_; lean_object* v___x_860_; lean_object* v_fst_861_; 
lean_dec(v___x_854_);
v___x_855_ = l_Lean_Syntax_getArgs(v_stx_853_);
lean_dec(v_stx_853_);
v___x_856_ = lean_box(0);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_858_ = lean_array_size(v___x_855_);
v___x_859_ = ((size_t)0ULL);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_852_, v___x_855_, v_sz_858_, v___x_859_, v___x_857_);
lean_dec_ref(v___x_855_);
v_fst_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_fst_861_);
lean_dec_ref(v___x_860_);
if (lean_obj_tag(v_fst_861_) == 0)
{
return v___x_856_;
}
else
{
lean_object* v_val_862_; 
v_val_862_ = lean_ctor_get(v_fst_861_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_fst_861_, 1);
return v_val_862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_863_, lean_object* v_as_864_, size_t v_sz_865_, size_t v_i_866_, lean_object* v_b_867_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = lean_usize_dec_lt(v_i_866_, v_sz_865_);
if (v___x_868_ == 0)
{
lean_dec_ref(v_range_863_);
lean_inc_ref(v_b_867_);
return v_b_867_;
}
else
{
lean_object* v___x_869_; lean_object* v_a_870_; lean_object* v___x_871_; 
v___x_869_ = lean_box(0);
v_a_870_ = lean_array_uget_borrowed(v_as_864_, v_i_866_);
lean_inc(v_a_870_);
lean_inc_ref(v_range_863_);
v___x_871_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_863_, v_a_870_);
if (lean_obj_tag(v___x_871_) == 1)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref(v_range_863_);
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_869_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; size_t v___x_875_; size_t v___x_876_; 
lean_dec(v___x_871_);
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_add(v_i_866_, v___x_875_);
v_i_866_ = v___x_876_;
v_b_867_ = v___x_874_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_878_, lean_object* v_as_879_, lean_object* v_sz_880_, lean_object* v_i_881_, lean_object* v_b_882_){
_start:
{
size_t v_sz_boxed_883_; size_t v_i_boxed_884_; lean_object* v_res_885_; 
v_sz_boxed_883_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v_i_boxed_884_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_res_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_878_, v_as_879_, v_sz_boxed_883_, v_i_boxed_884_, v_b_882_);
lean_dec_ref(v_b_882_);
lean_dec_ref(v_as_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_886_, lean_object* v_stx_887_){
_start:
{
uint8_t v___x_888_; lean_object* v___x_889_; 
v___x_888_ = 0;
v___x_889_ = l_Lean_Syntax_getRange_x3f(v_stx_887_, v___x_888_);
if (lean_obj_tag(v___x_889_) == 1)
{
lean_object* v_val_890_; uint8_t v___x_891_; 
v_val_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = l_Lean_Syntax_Range_includes(v_val_890_, v_range_886_, v___x_888_, v___x_888_);
lean_dec(v_val_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec(v_stx_887_);
lean_dec_ref(v_range_886_);
v___x_892_ = lean_box(0);
return v___x_892_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; size_t v_sz_895_; size_t v___x_896_; lean_object* v___x_897_; lean_object* v_fst_898_; 
v___x_893_ = l_Lean_Syntax_getArgs(v_stx_887_);
v___x_894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_895_ = lean_array_size(v___x_893_);
v___x_896_ = ((size_t)0ULL);
lean_inc_ref(v_range_886_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_886_, v___x_893_, v_sz_895_, v___x_896_, v___x_894_);
lean_dec_ref(v___x_893_);
v_fst_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_fst_898_);
lean_dec_ref(v___x_897_);
if (lean_obj_tag(v_fst_898_) == 0)
{
lean_object* v___x_899_; 
v___x_899_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_886_, v_stx_887_);
return v___x_899_;
}
else
{
lean_object* v_val_900_; 
lean_dec(v_stx_887_);
lean_dec_ref(v_range_886_);
v_val_900_ = lean_ctor_get(v_fst_898_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v_fst_898_, 1);
return v_val_900_;
}
}
}
else
{
lean_object* v___x_901_; 
lean_dec(v___x_889_);
lean_dec(v_stx_887_);
lean_dec_ref(v_range_886_);
v___x_901_ = lean_box(0);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_902_, lean_object* v_as_903_, size_t v_sz_904_, size_t v_i_905_, lean_object* v_b_906_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = lean_usize_dec_lt(v_i_905_, v_sz_904_);
if (v___x_907_ == 0)
{
lean_dec_ref(v_range_902_);
lean_inc_ref(v_b_906_);
return v_b_906_;
}
else
{
lean_object* v___x_908_; lean_object* v_a_909_; lean_object* v___x_910_; 
v___x_908_ = lean_box(0);
v_a_909_ = lean_array_uget_borrowed(v_as_903_, v_i_905_);
lean_inc(v_a_909_);
lean_inc_ref(v_range_902_);
v___x_910_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_902_, v_a_909_);
if (lean_obj_tag(v___x_910_) == 1)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v_range_902_);
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_908_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; 
lean_dec(v___x_910_);
v___x_913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_add(v_i_905_, v___x_914_);
v_i_905_ = v___x_915_;
v_b_906_ = v___x_913_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_917_, lean_object* v_as_918_, lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_b_921_){
_start:
{
size_t v_sz_boxed_922_; size_t v_i_boxed_923_; lean_object* v_res_924_; 
v_sz_boxed_922_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_923_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_917_, v_as_918_, v_sz_boxed_922_, v_i_boxed_923_, v_b_921_);
lean_dec_ref(v_b_921_);
lean_dec_ref(v_as_918_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_925_, lean_object* v_range_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_926_, v_cmd_925_);
return v___x_927_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_opts_928_, lean_object* v_opt_929_){
_start:
{
lean_object* v_name_930_; lean_object* v_defValue_931_; lean_object* v_map_932_; lean_object* v___x_933_; 
v_name_930_ = lean_ctor_get(v_opt_929_, 0);
v_defValue_931_ = lean_ctor_get(v_opt_929_, 1);
v_map_932_ = lean_ctor_get(v_opts_928_, 0);
v___x_933_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_932_, v_name_930_);
if (lean_obj_tag(v___x_933_) == 0)
{
uint8_t v___x_934_; 
v___x_934_ = lean_unbox(v_defValue_931_);
return v___x_934_;
}
else
{
lean_object* v_val_935_; 
v_val_935_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v___x_933_, 1);
if (lean_obj_tag(v_val_935_) == 1)
{
uint8_t v_v_936_; 
v_v_936_ = lean_ctor_get_uint8(v_val_935_, 0);
lean_dec_ref_known(v_val_935_, 0);
return v_v_936_;
}
else
{
uint8_t v___x_937_; 
lean_dec(v_val_935_);
v___x_937_ = lean_unbox(v_defValue_931_);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_opts_938_, lean_object* v_opt_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_938_, v_opt_939_);
lean_dec_ref(v_opt_939_);
lean_dec_ref(v_opts_938_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(lean_object* v_x_977_){
_start:
{
lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1));
v___x_979_ = lean_name_eq(v_x_977_, v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___boxed(lean_object* v_x_980_){
_start:
{
uint8_t v_res_981_; lean_object* v_r_982_; 
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(v_x_980_);
lean_dec(v_x_980_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(lean_object* v_a_983_, lean_object* v_x_984_){
_start:
{
if (lean_obj_tag(v_x_984_) == 0)
{
uint8_t v___x_985_; 
v___x_985_ = 0;
return v___x_985_;
}
else
{
lean_object* v_key_986_; lean_object* v_tail_987_; lean_object* v_fst_988_; lean_object* v_snd_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; uint8_t v___x_992_; 
v_key_986_ = lean_ctor_get(v_x_984_, 0);
v_tail_987_ = lean_ctor_get(v_x_984_, 2);
v_fst_988_ = lean_ctor_get(v_key_986_, 0);
v_snd_989_ = lean_ctor_get(v_key_986_, 1);
v_fst_990_ = lean_ctor_get(v_a_983_, 0);
v_snd_991_ = lean_ctor_get(v_a_983_, 1);
v___x_992_ = l_Lean_Syntax_instBEqRange_beq(v_fst_988_, v_fst_990_);
if (v___x_992_ == 0)
{
v_x_984_ = v_tail_987_;
goto _start;
}
else
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_instBEqMVarId_beq(v_snd_989_, v_snd_991_);
if (v___x_994_ == 0)
{
v_x_984_ = v_tail_987_;
goto _start;
}
else
{
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg___boxed(lean_object* v_a_996_, lean_object* v_x_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_996_, v_x_997_);
lean_dec(v_x_997_);
lean_dec_ref(v_a_996_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
if (lean_obj_tag(v_x_1001_) == 0)
{
return v_x_1000_;
}
else
{
lean_object* v_key_1002_; lean_object* v_value_1003_; lean_object* v_tail_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1031_; 
v_key_1002_ = lean_ctor_get(v_x_1001_, 0);
v_value_1003_ = lean_ctor_get(v_x_1001_, 1);
v_tail_1004_ = lean_ctor_get(v_x_1001_, 2);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_x_1001_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1006_ = v_x_1001_;
v_isShared_1007_ = v_isSharedCheck_1031_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_tail_1004_);
lean_inc(v_value_1003_);
lean_inc(v_key_1002_);
lean_dec(v_x_1001_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1031_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_fst_1008_; lean_object* v_snd_1009_; lean_object* v___x_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; uint64_t v_fold_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v_fst_1008_ = lean_ctor_get(v_key_1002_, 0);
v_snd_1009_ = lean_ctor_get(v_key_1002_, 1);
v___x_1010_ = lean_array_get_size(v_x_1000_);
v___x_1011_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1008_);
v___x_1012_ = l_Lean_instHashableMVarId_hash(v_snd_1009_);
v___x_1013_ = lean_uint64_mix_hash(v___x_1011_, v___x_1012_);
v___x_1014_ = 32ULL;
v___x_1015_ = lean_uint64_shift_right(v___x_1013_, v___x_1014_);
v_fold_1016_ = lean_uint64_xor(v___x_1013_, v___x_1015_);
v___x_1017_ = 16ULL;
v___x_1018_ = lean_uint64_shift_right(v_fold_1016_, v___x_1017_);
v___x_1019_ = lean_uint64_xor(v_fold_1016_, v___x_1018_);
v___x_1020_ = lean_uint64_to_usize(v___x_1019_);
v___x_1021_ = lean_usize_of_nat(v___x_1010_);
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_sub(v___x_1021_, v___x_1022_);
v___x_1024_ = lean_usize_land(v___x_1020_, v___x_1023_);
v___x_1025_ = lean_array_uget_borrowed(v_x_1000_, v___x_1024_);
lean_inc(v___x_1025_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 2, v___x_1025_);
v___x_1027_ = v___x_1006_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_key_1002_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_value_1003_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_array_uset(v_x_1000_, v___x_1024_, v___x_1027_);
v_x_1000_ = v___x_1028_;
v_x_1001_ = v_tail_1004_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1032_, lean_object* v_source_1033_, lean_object* v_target_1034_){
_start:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = lean_array_get_size(v_source_1033_);
v___x_1036_ = lean_nat_dec_lt(v_i_1032_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_dec_ref(v_source_1033_);
lean_dec(v_i_1032_);
return v_target_1034_;
}
else
{
lean_object* v_es_1037_; lean_object* v___x_1038_; lean_object* v_source_1039_; lean_object* v_target_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_es_1037_ = lean_array_fget(v_source_1033_, v_i_1032_);
v___x_1038_ = lean_box(0);
v_source_1039_ = lean_array_fset(v_source_1033_, v_i_1032_, v___x_1038_);
v_target_1040_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1034_, v_es_1037_);
v___x_1041_ = lean_unsigned_to_nat(1u);
v___x_1042_ = lean_nat_add(v_i_1032_, v___x_1041_);
lean_dec(v_i_1032_);
v_i_1032_ = v___x_1042_;
v_source_1033_ = v_source_1039_;
v_target_1034_ = v_target_1040_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(lean_object* v_data_1044_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_nbuckets_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1045_ = lean_array_get_size(v_data_1044_);
v___x_1046_ = lean_unsigned_to_nat(2u);
v_nbuckets_1047_ = lean_nat_mul(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_mk_array(v_nbuckets_1047_, v___x_1049_);
v___x_1051_ = lean_array_propagate_mark(v_data_1044_, v___x_1050_);
v___x_1052_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v___x_1048_, v_data_1044_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v_m_1053_, lean_object* v_a_1054_, lean_object* v_b_1055_){
_start:
{
lean_object* v_size_1056_; lean_object* v_buckets_1057_; lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; uint64_t v___x_1063_; uint64_t v___x_1064_; uint64_t v___x_1065_; uint64_t v_fold_1066_; uint64_t v___x_1067_; uint64_t v___x_1068_; uint64_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; lean_object* v_bkt_1075_; uint8_t v___x_1076_; 
v_size_1056_ = lean_ctor_get(v_m_1053_, 0);
v_buckets_1057_ = lean_ctor_get(v_m_1053_, 1);
v_fst_1058_ = lean_ctor_get(v_a_1054_, 0);
v_snd_1059_ = lean_ctor_get(v_a_1054_, 1);
v___x_1060_ = lean_array_get_size(v_buckets_1057_);
v___x_1061_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1058_);
v___x_1062_ = l_Lean_instHashableMVarId_hash(v_snd_1059_);
v___x_1063_ = lean_uint64_mix_hash(v___x_1061_, v___x_1062_);
v___x_1064_ = 32ULL;
v___x_1065_ = lean_uint64_shift_right(v___x_1063_, v___x_1064_);
v_fold_1066_ = lean_uint64_xor(v___x_1063_, v___x_1065_);
v___x_1067_ = 16ULL;
v___x_1068_ = lean_uint64_shift_right(v_fold_1066_, v___x_1067_);
v___x_1069_ = lean_uint64_xor(v_fold_1066_, v___x_1068_);
v___x_1070_ = lean_uint64_to_usize(v___x_1069_);
v___x_1071_ = lean_usize_of_nat(v___x_1060_);
v___x_1072_ = ((size_t)1ULL);
v___x_1073_ = lean_usize_sub(v___x_1071_, v___x_1072_);
v___x_1074_ = lean_usize_land(v___x_1070_, v___x_1073_);
v_bkt_1075_ = lean_array_uget_borrowed(v_buckets_1057_, v___x_1074_);
v___x_1076_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1054_, v_bkt_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1097_; 
lean_inc_ref(v_buckets_1057_);
lean_inc(v_size_1056_);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_m_1053_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; lean_object* v_unused_1099_; 
v_unused_1098_ = lean_ctor_get(v_m_1053_, 1);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_m_1053_, 0);
lean_dec(v_unused_1099_);
v___x_1078_ = v_m_1053_;
v_isShared_1079_ = v_isSharedCheck_1097_;
goto v_resetjp_1077_;
}
else
{
lean_dec(v_m_1053_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1097_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v_size_x27_1081_; lean_object* v___x_1082_; lean_object* v_buckets_x27_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v_size_x27_1081_ = lean_nat_add(v_size_1056_, v___x_1080_);
lean_dec(v_size_1056_);
lean_inc(v_bkt_1075_);
v___x_1082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1082_, 0, v_a_1054_);
lean_ctor_set(v___x_1082_, 1, v_b_1055_);
lean_ctor_set(v___x_1082_, 2, v_bkt_1075_);
v_buckets_x27_1083_ = lean_array_uset(v_buckets_1057_, v___x_1074_, v___x_1082_);
v___x_1084_ = lean_unsigned_to_nat(4u);
v___x_1085_ = lean_nat_mul(v_size_x27_1081_, v___x_1084_);
v___x_1086_ = lean_unsigned_to_nat(3u);
v___x_1087_ = lean_nat_div(v___x_1085_, v___x_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_array_get_size(v_buckets_x27_1083_);
v___x_1089_ = lean_nat_dec_le(v___x_1087_, v___x_1088_);
lean_dec(v___x_1087_);
if (v___x_1089_ == 0)
{
lean_object* v_val_1090_; lean_object* v___x_1092_; 
v_val_1090_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_buckets_x27_1083_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v_val_1090_);
lean_ctor_set(v___x_1078_, 0, v_size_x27_1081_);
v___x_1092_ = v___x_1078_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_size_x27_1081_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_val_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
else
{
lean_object* v___x_1095_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v_buckets_x27_1083_);
lean_ctor_set(v___x_1078_, 0, v_size_x27_1081_);
v___x_1095_ = v___x_1078_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_size_x27_1081_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_buckets_x27_1083_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_dec(v_b_1055_);
lean_dec_ref(v_a_1054_);
return v_m_1053_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_buckets_1102_; lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v_fold_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_buckets_1102_ = lean_ctor_get(v_m_1100_, 1);
v_fst_1103_ = lean_ctor_get(v_a_1101_, 0);
v_snd_1104_ = lean_ctor_get(v_a_1101_, 1);
v___x_1105_ = lean_array_get_size(v_buckets_1102_);
v___x_1106_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1103_);
v___x_1107_ = l_Lean_instHashableMVarId_hash(v_snd_1104_);
v___x_1108_ = lean_uint64_mix_hash(v___x_1106_, v___x_1107_);
v___x_1109_ = 32ULL;
v___x_1110_ = lean_uint64_shift_right(v___x_1108_, v___x_1109_);
v_fold_1111_ = lean_uint64_xor(v___x_1108_, v___x_1110_);
v___x_1112_ = 16ULL;
v___x_1113_ = lean_uint64_shift_right(v_fold_1111_, v___x_1112_);
v___x_1114_ = lean_uint64_xor(v_fold_1111_, v___x_1113_);
v___x_1115_ = lean_uint64_to_usize(v___x_1114_);
v___x_1116_ = lean_usize_of_nat(v___x_1105_);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_sub(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_usize_land(v___x_1115_, v___x_1118_);
v___x_1120_ = lean_array_uget_borrowed(v_buckets_1102_, v___x_1119_);
v___x_1121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1101_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object* v_m_1122_, lean_object* v_a_1123_){
_start:
{
uint8_t v_res_1124_; lean_object* v_r_1125_; 
v_res_1124_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1122_, v_a_1123_);
lean_dec_ref(v_a_1123_);
lean_dec_ref(v_m_1122_);
v_r_1125_ = lean_box(v_res_1124_);
return v_r_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object* v___x_1126_, lean_object* v_fst_1127_, lean_object* v_snd_1128_, lean_object* v___x_1129_, lean_object* v_as_1130_, size_t v_sz_1131_, size_t v_i_1132_, lean_object* v_b_1133_){
_start:
{
lean_object* v_a_1136_; uint8_t v___x_1140_; 
v___x_1140_ = lean_usize_dec_lt(v_i_1132_, v_sz_1131_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec(v___x_1129_);
lean_dec(v_snd_1128_);
lean_dec(v_fst_1127_);
lean_dec_ref(v___x_1126_);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_b_1133_);
return v___x_1141_;
}
else
{
lean_object* v_a_1142_; lean_object* v_snd_1143_; lean_object* v_fst_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1180_; 
v_a_1142_ = lean_array_uget(v_as_1130_, v_i_1132_);
v_snd_1143_ = lean_ctor_get(v_a_1142_, 1);
v_fst_1144_ = lean_ctor_get(v_a_1142_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_a_1142_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1146_ = v_a_1142_;
v_isShared_1147_ = v_isSharedCheck_1180_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1143_);
lean_inc(v_fst_1144_);
lean_dec(v_a_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1180_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_fst_1148_; lean_object* v_snd_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1179_; 
v_fst_1148_ = lean_ctor_get(v_snd_1143_, 0);
v_snd_1149_ = lean_ctor_get(v_snd_1143_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_snd_1143_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1151_ = v_snd_1143_;
v_isShared_1152_ = v_isSharedCheck_1179_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_snd_1149_);
lean_inc(v_fst_1148_);
lean_dec(v_snd_1143_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1179_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_fst_1153_; lean_object* v_snd_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1178_; 
v_fst_1153_ = lean_ctor_get(v_b_1133_, 0);
v_snd_1154_ = lean_ctor_get(v_b_1133_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_b_1133_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1156_ = v_b_1133_;
v_isShared_1157_ = v_isSharedCheck_1178_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snd_1154_);
lean_inc(v_fst_1153_);
lean_dec(v_b_1133_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1178_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
lean_inc(v_snd_1149_);
lean_inc_ref(v___x_1126_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v_snd_1149_);
lean_ctor_set(v___x_1156_, 0, v___x_1126_);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_snd_1149_);
v___x_1159_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
uint8_t v___x_1160_; 
v___x_1160_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1154_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v_env_1161_; lean_object* v_mctx_1162_; lean_object* v_opts_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v_env_1161_ = lean_ctor_get(v_fst_1144_, 0);
lean_inc_ref(v_env_1161_);
v_mctx_1162_ = lean_ctor_get(v_fst_1144_, 1);
lean_inc_ref(v_mctx_1162_);
v_opts_1163_ = lean_ctor_get(v_fst_1144_, 3);
lean_inc_ref(v_opts_1163_);
lean_dec(v_fst_1144_);
v___x_1164_ = lean_box(0);
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1154_, v___x_1159_, v___x_1164_);
lean_inc(v_snd_1128_);
lean_inc(v_fst_1127_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v_snd_1128_);
lean_ctor_set(v___x_1146_, 0, v_fst_1127_);
v___x_1167_ = v___x_1146_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_fst_1127_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_snd_1128_);
v___x_1167_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_inc(v___x_1129_);
v___x_1168_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1129_);
lean_ctor_set(v___x_1168_, 2, v_env_1161_);
lean_ctor_set(v___x_1168_, 3, v_mctx_1162_);
lean_ctor_set(v___x_1168_, 4, v_opts_1163_);
lean_ctor_set(v___x_1168_, 5, v_fst_1148_);
lean_ctor_set(v___x_1168_, 6, v_snd_1149_);
v___x_1169_ = lean_array_push(v_fst_1153_, v___x_1168_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v___x_1165_);
lean_ctor_set(v___x_1151_, 0, v___x_1169_);
v___x_1171_ = v___x_1151_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1165_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
v_a_1136_ = v___x_1171_;
goto v___jp_1135_;
}
}
}
else
{
lean_object* v___x_1175_; 
lean_dec_ref(v___x_1159_);
lean_dec(v_snd_1149_);
lean_dec(v_fst_1148_);
lean_del_object(v___x_1146_);
lean_dec(v_fst_1144_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 1, v_snd_1154_);
lean_ctor_set(v___x_1151_, 0, v_fst_1153_);
v___x_1175_ = v___x_1151_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_fst_1153_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_snd_1154_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
v_a_1136_ = v___x_1175_;
goto v___jp_1135_;
}
}
}
}
}
}
}
v___jp_1135_:
{
size_t v___x_1137_; size_t v___x_1138_; 
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = lean_usize_add(v_i_1132_, v___x_1137_);
v_i_1132_ = v___x_1138_;
v_b_1133_ = v_a_1136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object* v___x_1181_, lean_object* v_fst_1182_, lean_object* v_snd_1183_, lean_object* v___x_1184_, lean_object* v_as_1185_, lean_object* v_sz_1186_, lean_object* v_i_1187_, lean_object* v_b_1188_, lean_object* v___y_1189_){
_start:
{
size_t v_sz_boxed_1190_; size_t v_i_boxed_1191_; lean_object* v_res_1192_; 
v_sz_boxed_1190_ = lean_unbox_usize(v_sz_1186_);
lean_dec(v_sz_1186_);
v_i_boxed_1191_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_res_1192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1181_, v_fst_1182_, v_snd_1183_, v___x_1184_, v_as_1185_, v_sz_boxed_1190_, v_i_boxed_1191_, v_b_1188_);
lean_dec_ref(v_as_1185_);
return v_res_1192_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1196_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
lean_ctor_set(v___x_1198_, 2, v___x_1197_);
lean_ctor_set(v___x_1198_, 3, v___x_1197_);
lean_ctor_set(v___x_1198_, 4, v___x_1196_);
lean_ctor_set(v___x_1198_, 5, v___x_1196_);
lean_ctor_set(v___x_1198_, 6, v___x_1196_);
lean_ctor_set(v___x_1198_, 7, v___x_1196_);
lean_ctor_set(v___x_1198_, 8, v___x_1196_);
lean_ctor_set(v___x_1198_, 9, v___x_1196_);
lean_ctor_set(v___x_1198_, 10, v___x_1196_);
lean_ctor_set(v___x_1198_, 11, v___x_1195_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_unsigned_to_nat(32u);
v___x_1200_ = lean_mk_empty_array_with_capacity(v___x_1199_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1202_ = ((size_t)5ULL);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_unsigned_to_nat(32u);
v___x_1205_ = lean_mk_empty_array_with_capacity(v___x_1204_);
v___x_1206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2);
v___x_1207_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v___x_1205_);
lean_ctor_set(v___x_1207_, 2, v___x_1203_);
lean_ctor_set(v___x_1207_, 3, v___x_1203_);
lean_ctor_set_usize(v___x_1207_, 4, v___x_1202_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1208_ = lean_box(1);
v___x_1209_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3);
v___x_1210_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1209_);
lean_ctor_set(v___x_1211_, 2, v___x_1208_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(lean_object* v_msgData_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v_env_1216_; uint8_t v___x_1217_; lean_object* v_env_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_scopes_1221_; lean_object* v___x_1222_; lean_object* v_opts_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1215_ = lean_st_ref_get(v___y_1213_);
v_env_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_ref(v_env_1216_);
lean_dec(v___x_1215_);
v___x_1217_ = 0;
v_env_1218_ = l_Lean_Environment_setRecordingDeps(v_env_1216_, v___x_1217_);
v___x_1219_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1220_ = lean_st_ref_get(v___y_1213_);
v_scopes_1221_ = lean_ctor_get(v___x_1220_, 2);
lean_inc(v_scopes_1221_);
lean_dec(v___x_1220_);
v___x_1222_ = l_List_head_x21___redArg(v___x_1219_, v_scopes_1221_);
lean_dec(v_scopes_1221_);
v_opts_1223_ = lean_ctor_get(v___x_1222_, 1);
lean_inc_ref(v_opts_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1);
v___x_1225_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4);
v___x_1226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1226_, 0, v_env_1218_);
lean_ctor_set(v___x_1226_, 1, v___x_1224_);
lean_ctor_set(v___x_1226_, 2, v___x_1225_);
lean_ctor_set(v___x_1226_, 3, v_opts_1223_);
v___x_1227_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_msgData_1212_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_1229_, v___y_1230_);
lean_dec(v___y_1230_);
return v_res_1232_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1233_; double v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_float_of_nat(v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v_cls_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Elab_Command_getRef___redArg(v___y_1239_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1293_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msg_1238_, v___y_1240_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1293_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1293_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v_traceState_1250_; lean_object* v_env_1251_; lean_object* v_messages_1252_; lean_object* v_scopes_1253_; lean_object* v_usedQuotCtxts_1254_; lean_object* v_nextMacroScope_1255_; lean_object* v_maxRecDepth_1256_; lean_object* v_ngen_1257_; lean_object* v_auxDeclNGen_1258_; lean_object* v_infoState_1259_; lean_object* v_snapshotTasks_1260_; lean_object* v_prevLinterStates_1261_; lean_object* v_codeQualityEntryTasks_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1292_; 
v___x_1249_ = lean_st_ref_take(v___y_1240_);
v_traceState_1250_ = lean_ctor_get(v___x_1249_, 9);
v_env_1251_ = lean_ctor_get(v___x_1249_, 0);
v_messages_1252_ = lean_ctor_get(v___x_1249_, 1);
v_scopes_1253_ = lean_ctor_get(v___x_1249_, 2);
v_usedQuotCtxts_1254_ = lean_ctor_get(v___x_1249_, 3);
v_nextMacroScope_1255_ = lean_ctor_get(v___x_1249_, 4);
v_maxRecDepth_1256_ = lean_ctor_get(v___x_1249_, 5);
v_ngen_1257_ = lean_ctor_get(v___x_1249_, 6);
v_auxDeclNGen_1258_ = lean_ctor_get(v___x_1249_, 7);
v_infoState_1259_ = lean_ctor_get(v___x_1249_, 8);
v_snapshotTasks_1260_ = lean_ctor_get(v___x_1249_, 10);
v_prevLinterStates_1261_ = lean_ctor_get(v___x_1249_, 11);
v_codeQualityEntryTasks_1262_ = lean_ctor_get(v___x_1249_, 12);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1264_ = v___x_1249_;
v_isShared_1265_ = v_isSharedCheck_1292_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1262_);
lean_inc(v_prevLinterStates_1261_);
lean_inc(v_snapshotTasks_1260_);
lean_inc(v_traceState_1250_);
lean_inc(v_infoState_1259_);
lean_inc(v_auxDeclNGen_1258_);
lean_inc(v_ngen_1257_);
lean_inc(v_maxRecDepth_1256_);
lean_inc(v_nextMacroScope_1255_);
lean_inc(v_usedQuotCtxts_1254_);
lean_inc(v_scopes_1253_);
lean_inc(v_messages_1252_);
lean_inc(v_env_1251_);
lean_dec(v___x_1249_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1292_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
uint64_t v_tid_1266_; lean_object* v_traces_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1291_; 
v_tid_1266_ = lean_ctor_get_uint64(v_traceState_1250_, sizeof(void*)*1);
v_traces_1267_ = lean_ctor_get(v_traceState_1250_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_traceState_1250_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1269_ = v_traceState_1250_;
v_isShared_1270_ = v_isSharedCheck_1291_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_traces_1267_);
lean_dec(v_traceState_1250_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1291_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; double v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_box(0);
v___x_1273_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_1274_ = 0;
v___x_1275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1276_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1276_, 0, v_cls_1237_);
lean_ctor_set(v___x_1276_, 1, v___x_1272_);
lean_ctor_set(v___x_1276_, 2, v___x_1275_);
lean_ctor_set_float(v___x_1276_, sizeof(void*)*3, v___x_1273_);
lean_ctor_set_float(v___x_1276_, sizeof(void*)*3 + 8, v___x_1273_);
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*3 + 16, v___x_1274_);
v___x_1277_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_1278_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v_a_1245_);
lean_ctor_set(v___x_1278_, 2, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_a_1243_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_PersistentArray_push___redArg(v_traces_1267_, v___x_1279_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1280_);
v___x_1282_ = v___x_1269_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1280_);
lean_ctor_set_uint64(v_reuseFailAlloc_1290_, sizeof(void*)*1, v_tid_1266_);
v___x_1282_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1284_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 9, v___x_1282_);
v___x_1284_ = v___x_1264_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_env_1251_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_messages_1252_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_scopes_1253_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_usedQuotCtxts_1254_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_nextMacroScope_1255_);
lean_ctor_set(v_reuseFailAlloc_1289_, 5, v_maxRecDepth_1256_);
lean_ctor_set(v_reuseFailAlloc_1289_, 6, v_ngen_1257_);
lean_ctor_set(v_reuseFailAlloc_1289_, 7, v_auxDeclNGen_1258_);
lean_ctor_set(v_reuseFailAlloc_1289_, 8, v_infoState_1259_);
lean_ctor_set(v_reuseFailAlloc_1289_, 9, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1289_, 10, v_snapshotTasks_1260_);
lean_ctor_set(v_reuseFailAlloc_1289_, 11, v_prevLinterStates_1261_);
lean_ctor_set(v_reuseFailAlloc_1289_, 12, v_codeQualityEntryTasks_1262_);
v___x_1284_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_st_ref_put(v___y_1240_, v___x_1284_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1271_);
v___x_1287_ = v___x_1247_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1271_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_msg_1238_);
lean_dec(v_cls_1237_);
v_a_1294_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1242_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1242_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v_cls_1302_, lean_object* v_msg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_cls_1302_, v_msg_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1307_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2));
v___x_1314_ = l_Lean_Name_append(v___x_1313_, v___x_1312_);
return v___x_1314_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6));
v___x_1320_ = l_Lean_stringToMessageData(v___x_1319_);
return v___x_1320_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8));
v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
return v___x_1323_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10));
v___x_1326_ = l_Lean_stringToMessageData(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(lean_object* v___x_1327_, lean_object* v_val_1328_, lean_object* v_cmd_1329_, uint8_t v_onUnsolved_1330_, uint8_t v___y_1331_, lean_object* v_as_1332_, size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_dec(v_cmd_1329_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_b_1335_);
return v___x_1340_;
}
else
{
lean_object* v_snd_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1489_; 
v_snd_1341_ = lean_ctor_get(v_b_1335_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_b_1335_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_b_1335_, 0);
lean_dec(v_unused_1490_);
v___x_1343_ = v_b_1335_;
v_isShared_1344_ = v_isSharedCheck_1489_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_snd_1341_);
lean_dec(v_b_1335_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1489_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1488_; 
v_fst_1345_ = lean_ctor_get(v_snd_1341_, 0);
v_snd_1346_ = lean_ctor_get(v_snd_1341_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_snd_1341_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1348_ = v_snd_1341_;
v_isShared_1349_ = v_isSharedCheck_1488_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snd_1346_);
lean_inc(v_fst_1345_);
lean_dec(v_snd_1341_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1488_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_a_1350_; lean_object* v_pos_1351_; lean_object* v_endPos_1352_; uint8_t v_severity_1353_; lean_object* v_data_1354_; lean_object* v___x_1355_; lean_object* v_a_1357_; 
v_a_1350_ = lean_array_uget_borrowed(v_as_1332_, v_i_1334_);
v_pos_1351_ = lean_ctor_get(v_a_1350_, 1);
v_endPos_1352_ = lean_ctor_get(v_a_1350_, 2);
lean_inc(v_endPos_1352_);
v_severity_1353_ = lean_ctor_get_uint8(v_a_1350_, sizeof(void*)*5 + 1);
v_data_1354_ = lean_ctor_get(v_a_1350_, 4);
v___x_1355_ = lean_box(0);
if (v_severity_1353_ == 2)
{
lean_object* v___f_1370_; uint8_t v___x_1371_; 
v___f_1370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1354_);
v___x_1371_ = l_Lean_MessageData_hasTag(v___f_1370_, v_data_1354_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec(v_endPos_1352_);
lean_del_object(v___x_1343_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_fst_1345_);
lean_ctor_set(v___x_1372_, 1, v_snd_1346_);
v_a_1357_ = v___x_1372_;
goto v___jp_1356_;
}
else
{
if (lean_obj_tag(v_endPos_1352_) == 1)
{
lean_object* v_val_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1485_; 
v_val_1373_ = lean_ctor_get(v_endPos_1352_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_endPos_1352_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1375_ = v_endPos_1352_;
v_isShared_1376_ = v_isSharedCheck_1485_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_val_1373_);
lean_dec(v_endPos_1352_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1485_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; 
lean_inc_ref(v_pos_1351_);
v___x_1377_ = l_Lean_FileMap_ofPosition(v___x_1327_, v_pos_1351_);
v___x_1378_ = l_Lean_FileMap_ofPosition(v___x_1327_, v_val_1373_);
lean_inc(v___x_1378_);
lean_inc(v___x_1377_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = 0;
v___x_1381_ = l_Lean_Syntax_Range_includes(v_val_1328_, v___x_1379_, v___x_1380_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec_ref_known(v___x_1379_, 2);
lean_dec(v___x_1378_);
lean_dec(v___x_1377_);
lean_del_object(v___x_1375_);
lean_del_object(v___x_1343_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_fst_1345_);
lean_ctor_set(v___x_1382_, 1, v_snd_1346_);
v_a_1357_ = v___x_1382_;
goto v___jp_1356_;
}
else
{
lean_object* v___x_1383_; 
lean_inc(v_cmd_1329_);
lean_inc_ref(v___x_1379_);
v___x_1383_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1379_, v_cmd_1329_);
if (lean_obj_tag(v___x_1383_) == 1)
{
lean_object* v_val_1384_; lean_object* v_fst_1385_; lean_object* v_snd_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v___x_1378_);
lean_dec(v___x_1377_);
lean_del_object(v___x_1375_);
v_val_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_val_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v_fst_1385_ = lean_ctor_get(v_val_1384_, 0);
v_snd_1386_ = lean_ctor_get(v_val_1384_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_val_1384_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1388_ = v_val_1384_;
v_isShared_1389_ = v_isSharedCheck_1449_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_snd_1386_);
lean_inc(v_fst_1385_);
lean_dec(v_val_1384_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1449_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; uint8_t v___y_1447_; lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Syntax_getPos_x3f(v_fst_1385_, v___x_1380_);
if (lean_obj_tag(v___x_1448_) == 0)
{
v___y_1447_ = v___x_1381_;
goto v___jp_1446_;
}
else
{
lean_dec_ref_known(v___x_1448_, 1);
v___y_1447_ = v___x_1380_;
goto v___jp_1446_;
}
v___jp_1390_:
{
lean_object* v___x_1396_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 1, v_snd_1346_);
lean_ctor_set(v___x_1388_, 0, v_fst_1345_);
v___x_1396_ = v___x_1388_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_fst_1345_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_snd_1346_);
v___x_1396_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_sz_1397_ = lean_array_size(v___y_1392_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1379_, v_fst_1385_, v_snd_1386_, v___y_1391_, v___y_1392_, v_sz_1397_, v___x_1398_, v___x_1396_);
lean_dec_ref(v___y_1392_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v_fst_1401_ = lean_ctor_get(v_a_1400_, 0);
v_snd_1402_ = lean_ctor_get(v_a_1400_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_a_1400_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v_a_1400_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snd_1402_);
lean_inc(v_fst_1401_);
lean_dec(v_a_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_fst_1401_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_snd_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
v_a_1357_ = v___x_1407_;
goto v___jp_1356_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_del_object(v___x_1348_);
lean_dec(v_cmd_1329_);
v_a_1410_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1399_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1399_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
v___jp_1419_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
lean_inc_ref(v___x_1379_);
v___x_1420_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1379_);
v___x_1421_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1354_);
v___x_1422_ = lean_array_get_size(v___x_1421_);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_nat_dec_eq(v___x_1422_, v___x_1423_);
if (v___x_1424_ == 0)
{
v___y_1391_ = v___x_1420_;
v___y_1392_ = v___x_1421_;
v___y_1393_ = v___y_1336_;
v___y_1394_ = v___y_1337_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_scopes_1430_; lean_object* v___x_1431_; lean_object* v_opts_1432_; uint8_t v_hasTrace_1433_; 
v___x_1425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1426_ = l_Lean_inheritedTraceOptions;
v___x_1427_ = lean_st_ref_get(v___x_1426_);
v___x_1428_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1429_ = lean_st_ref_get(v___y_1337_);
v_scopes_1430_ = lean_ctor_get(v___x_1429_, 2);
lean_inc(v_scopes_1430_);
lean_dec(v___x_1429_);
v___x_1431_ = l_List_head_x21___redArg(v___x_1428_, v_scopes_1430_);
lean_dec(v_scopes_1430_);
v_opts_1432_ = lean_ctor_get(v___x_1431_, 1);
lean_inc_ref(v_opts_1432_);
lean_dec(v___x_1431_);
v_hasTrace_1433_ = lean_ctor_get_uint8(v_opts_1432_, sizeof(void*)*1);
if (v_hasTrace_1433_ == 0)
{
lean_dec_ref(v_opts_1432_);
lean_dec(v___x_1427_);
v___y_1391_ = v___x_1420_;
v___y_1392_ = v___x_1421_;
v___y_1393_ = v___y_1336_;
v___y_1394_ = v___y_1337_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1435_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1427_, v_opts_1432_, v___x_1434_);
lean_dec_ref(v_opts_1432_);
lean_dec(v___x_1427_);
if (v___x_1435_ == 0)
{
v___y_1391_ = v___x_1420_;
v___y_1392_ = v___x_1421_;
v___y_1393_ = v___y_1336_;
v___y_1394_ = v___y_1337_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1437_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1425_, v___x_1436_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_dec_ref_known(v___x_1437_, 1);
v___y_1391_ = v___x_1420_;
v___y_1392_ = v___x_1421_;
v___y_1393_ = v___y_1336_;
v___y_1394_ = v___y_1337_;
goto v___jp_1390_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v___x_1421_);
lean_dec(v___x_1420_);
lean_del_object(v___x_1388_);
lean_dec(v_snd_1386_);
lean_dec(v_fst_1385_);
lean_dec_ref_known(v___x_1379_, 2);
lean_del_object(v___x_1348_);
lean_dec(v_snd_1346_);
lean_dec(v_fst_1345_);
lean_dec(v_cmd_1329_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
}
}
v___jp_1446_:
{
if (v_onUnsolved_1330_ == 0)
{
if (v___y_1331_ == 0)
{
lean_del_object(v___x_1388_);
lean_dec(v_snd_1386_);
lean_dec(v_fst_1385_);
lean_dec_ref_known(v___x_1379_, 2);
goto v___jp_1364_;
}
else
{
if (v___y_1447_ == 0)
{
lean_del_object(v___x_1388_);
lean_dec(v_snd_1386_);
lean_dec(v_fst_1385_);
lean_dec_ref_known(v___x_1379_, 2);
goto v___jp_1364_;
}
else
{
lean_del_object(v___x_1343_);
goto v___jp_1419_;
}
}
}
else
{
lean_del_object(v___x_1343_);
goto v___jp_1419_;
}
}
}
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_scopes_1455_; lean_object* v___x_1456_; lean_object* v_opts_1457_; uint8_t v_hasTrace_1458_; 
lean_dec(v___x_1383_);
lean_dec_ref_known(v___x_1379_, 2);
lean_del_object(v___x_1343_);
v___x_1450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1451_ = l_Lean_inheritedTraceOptions;
v___x_1452_ = lean_st_ref_get(v___x_1451_);
v___x_1453_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1454_ = lean_st_ref_get(v___y_1337_);
v_scopes_1455_ = lean_ctor_get(v___x_1454_, 2);
lean_inc(v_scopes_1455_);
lean_dec(v___x_1454_);
v___x_1456_ = l_List_head_x21___redArg(v___x_1453_, v_scopes_1455_);
lean_dec(v_scopes_1455_);
v_opts_1457_ = lean_ctor_get(v___x_1456_, 1);
lean_inc_ref(v_opts_1457_);
lean_dec(v___x_1456_);
v_hasTrace_1458_ = lean_ctor_get_uint8(v_opts_1457_, sizeof(void*)*1);
if (v_hasTrace_1458_ == 0)
{
lean_dec_ref(v_opts_1457_);
lean_dec(v___x_1452_);
lean_dec(v___x_1378_);
lean_dec(v___x_1377_);
lean_del_object(v___x_1375_);
goto v___jp_1368_;
}
else
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1460_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1452_, v_opts_1457_, v___x_1459_);
lean_dec_ref(v_opts_1457_);
lean_dec(v___x_1452_);
if (v___x_1460_ == 0)
{
lean_dec(v___x_1378_);
lean_dec(v___x_1377_);
lean_del_object(v___x_1375_);
goto v___jp_1368_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1462_ = l_Nat_reprFast(v___x_1377_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 3);
lean_ctor_set(v___x_1375_, 0, v___x_1462_);
v___x_1464_ = v___x_1375_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1465_ = l_Lean_MessageData_ofFormat(v___x_1464_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1461_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Nat_reprFast(v___x_1378_);
v___x_1470_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
v___x_1471_ = l_Lean_MessageData_ofFormat(v___x_1470_);
v___x_1472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1468_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1450_, v___x_1474_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_dec_ref_known(v___x_1475_, 1);
goto v___jp_1368_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_del_object(v___x_1348_);
lean_dec(v_snd_1346_);
lean_dec(v_fst_1345_);
lean_dec(v_cmd_1329_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
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
lean_object* v___x_1486_; 
lean_dec(v_endPos_1352_);
lean_del_object(v___x_1343_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_fst_1345_);
lean_ctor_set(v___x_1486_, 1, v_snd_1346_);
v_a_1357_ = v___x_1486_;
goto v___jp_1356_;
}
}
}
else
{
lean_object* v___x_1487_; 
lean_dec(v_endPos_1352_);
lean_del_object(v___x_1343_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_fst_1345_);
lean_ctor_set(v___x_1487_, 1, v_snd_1346_);
v_a_1357_ = v___x_1487_;
goto v___jp_1356_;
}
v___jp_1356_:
{
lean_object* v___x_1359_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v_a_1357_);
lean_ctor_set(v___x_1348_, 0, v___x_1355_);
v___x_1359_ = v___x_1348_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_a_1357_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
size_t v___x_1360_; size_t v___x_1361_; 
v___x_1360_ = ((size_t)1ULL);
v___x_1361_ = lean_usize_add(v_i_1334_, v___x_1360_);
v_i_1334_ = v___x_1361_;
v_b_1335_ = v___x_1359_;
goto _start;
}
}
v___jp_1364_:
{
lean_object* v___x_1366_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v_snd_1346_);
lean_ctor_set(v___x_1343_, 0, v_fst_1345_);
v___x_1366_ = v___x_1343_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_fst_1345_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_snd_1346_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
v_a_1357_ = v___x_1366_;
goto v___jp_1356_;
}
}
v___jp_1368_:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_fst_1345_);
lean_ctor_set(v___x_1369_, 1, v_snd_1346_);
v_a_1357_ = v___x_1369_;
goto v___jp_1356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___boxed(lean_object* v___x_1491_, lean_object* v_val_1492_, lean_object* v_cmd_1493_, lean_object* v_onUnsolved_1494_, lean_object* v___y_1495_, lean_object* v_as_1496_, lean_object* v_sz_1497_, lean_object* v_i_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_onUnsolved_boxed_1503_; uint8_t v___y_12284__boxed_1504_; size_t v_sz_boxed_1505_; size_t v_i_boxed_1506_; lean_object* v_res_1507_; 
v_onUnsolved_boxed_1503_ = lean_unbox(v_onUnsolved_1494_);
v___y_12284__boxed_1504_ = lean_unbox(v___y_1495_);
v_sz_boxed_1505_ = lean_unbox_usize(v_sz_1497_);
lean_dec(v_sz_1497_);
v_i_boxed_1506_ = lean_unbox_usize(v_i_1498_);
lean_dec(v_i_1498_);
v_res_1507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1491_, v_val_1492_, v_cmd_1493_, v_onUnsolved_boxed_1503_, v___y_12284__boxed_1504_, v_as_1496_, v_sz_boxed_1505_, v_i_boxed_1506_, v_b_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v_as_1496_);
lean_dec_ref(v_val_1492_);
lean_dec_ref(v___x_1491_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object* v___x_1508_, lean_object* v_val_1509_, lean_object* v_cmd_1510_, uint8_t v_onUnsolved_1511_, uint8_t v___y_1512_, lean_object* v_as_1513_, size_t v_sz_1514_, size_t v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_usize_dec_lt(v_i_1515_, v_sz_1514_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; 
lean_dec(v_cmd_1510_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_b_1516_);
return v___x_1521_;
}
else
{
lean_object* v_snd_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1670_; 
v_snd_1522_ = lean_ctor_get(v_b_1516_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_b_1516_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_b_1516_, 0);
lean_dec(v_unused_1671_);
v___x_1524_ = v_b_1516_;
v_isShared_1525_ = v_isSharedCheck_1670_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_snd_1522_);
lean_dec(v_b_1516_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1670_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_fst_1526_; lean_object* v_snd_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1669_; 
v_fst_1526_ = lean_ctor_get(v_snd_1522_, 0);
v_snd_1527_ = lean_ctor_get(v_snd_1522_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_snd_1522_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1529_ = v_snd_1522_;
v_isShared_1530_ = v_isSharedCheck_1669_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_snd_1527_);
lean_inc(v_fst_1526_);
lean_dec(v_snd_1522_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1669_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v_a_1531_; lean_object* v_pos_1532_; lean_object* v_endPos_1533_; uint8_t v_severity_1534_; lean_object* v_data_1535_; lean_object* v___x_1536_; lean_object* v_a_1538_; 
v_a_1531_ = lean_array_uget_borrowed(v_as_1513_, v_i_1515_);
v_pos_1532_ = lean_ctor_get(v_a_1531_, 1);
v_endPos_1533_ = lean_ctor_get(v_a_1531_, 2);
lean_inc(v_endPos_1533_);
v_severity_1534_ = lean_ctor_get_uint8(v_a_1531_, sizeof(void*)*5 + 1);
v_data_1535_ = lean_ctor_get(v_a_1531_, 4);
v___x_1536_ = lean_box(0);
if (v_severity_1534_ == 2)
{
lean_object* v___f_1551_; uint8_t v___x_1552_; 
v___f_1551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1535_);
v___x_1552_ = l_Lean_MessageData_hasTag(v___f_1551_, v_data_1535_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec(v_endPos_1533_);
lean_del_object(v___x_1524_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_fst_1526_);
lean_ctor_set(v___x_1553_, 1, v_snd_1527_);
v_a_1538_ = v___x_1553_;
goto v___jp_1537_;
}
else
{
if (lean_obj_tag(v_endPos_1533_) == 1)
{
lean_object* v_val_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1666_; 
v_val_1554_ = lean_ctor_get(v_endPos_1533_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_endPos_1533_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1556_ = v_endPos_1533_;
v_isShared_1557_ = v_isSharedCheck_1666_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_val_1554_);
lean_dec(v_endPos_1533_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1666_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; uint8_t v___x_1562_; 
lean_inc_ref(v_pos_1532_);
v___x_1558_ = l_Lean_FileMap_ofPosition(v___x_1508_, v_pos_1532_);
v___x_1559_ = l_Lean_FileMap_ofPosition(v___x_1508_, v_val_1554_);
lean_inc(v___x_1559_);
lean_inc(v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = 0;
v___x_1562_ = l_Lean_Syntax_Range_includes(v_val_1509_, v___x_1560_, v___x_1561_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_dec_ref_known(v___x_1560_, 2);
lean_dec(v___x_1559_);
lean_dec(v___x_1558_);
lean_del_object(v___x_1556_);
lean_del_object(v___x_1524_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_fst_1526_);
lean_ctor_set(v___x_1563_, 1, v_snd_1527_);
v_a_1538_ = v___x_1563_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1564_; 
lean_inc(v_cmd_1510_);
lean_inc_ref(v___x_1560_);
v___x_1564_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1560_, v_cmd_1510_);
if (lean_obj_tag(v___x_1564_) == 1)
{
lean_object* v_val_1565_; lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v___x_1559_);
lean_dec(v___x_1558_);
lean_del_object(v___x_1556_);
v_val_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v_fst_1566_ = lean_ctor_get(v_val_1565_, 0);
v_snd_1567_ = lean_ctor_get(v_val_1565_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_val_1565_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1569_ = v_val_1565_;
v_isShared_1570_ = v_isSharedCheck_1630_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snd_1567_);
lean_inc(v_fst_1566_);
lean_dec(v_val_1565_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1630_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; uint8_t v___y_1628_; lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Syntax_getPos_x3f(v_fst_1566_, v___x_1561_);
if (lean_obj_tag(v___x_1629_) == 0)
{
v___y_1628_ = v___x_1562_;
goto v___jp_1627_;
}
else
{
lean_dec_ref_known(v___x_1629_, 1);
v___y_1628_ = v___x_1561_;
goto v___jp_1627_;
}
v___jp_1571_:
{
lean_object* v___x_1577_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 1, v_snd_1527_);
lean_ctor_set(v___x_1569_, 0, v_fst_1526_);
v___x_1577_ = v___x_1569_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_fst_1526_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_snd_1527_);
v___x_1577_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_1580_; 
v_sz_1578_ = lean_array_size(v___y_1573_);
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1560_, v_fst_1566_, v_snd_1567_, v___y_1572_, v___y_1573_, v_sz_1578_, v___x_1579_, v___x_1577_);
lean_dec_ref(v___y_1573_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v_fst_1582_; lean_object* v_snd_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v_fst_1582_ = lean_ctor_get(v_a_1581_, 0);
v_snd_1583_ = lean_ctor_get(v_a_1581_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_a_1581_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v_a_1581_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snd_1583_);
lean_inc(v_fst_1582_);
lean_dec(v_a_1581_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_fst_1582_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_snd_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
v_a_1538_ = v___x_1588_;
goto v___jp_1537_;
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_del_object(v___x_1529_);
lean_dec(v_cmd_1510_);
v_a_1591_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1580_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1580_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
v___jp_1600_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
lean_inc_ref(v___x_1560_);
v___x_1601_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1560_);
v___x_1602_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1535_);
v___x_1603_ = lean_array_get_size(v___x_1602_);
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_nat_dec_eq(v___x_1603_, v___x_1604_);
if (v___x_1605_ == 0)
{
v___y_1572_ = v___x_1601_;
v___y_1573_ = v___x_1602_;
v___y_1574_ = v___y_1517_;
v___y_1575_ = v___y_1518_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_scopes_1611_; lean_object* v___x_1612_; lean_object* v_opts_1613_; uint8_t v_hasTrace_1614_; 
v___x_1606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1607_ = l_Lean_inheritedTraceOptions;
v___x_1608_ = lean_st_ref_get(v___x_1607_);
v___x_1609_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1610_ = lean_st_ref_get(v___y_1518_);
v_scopes_1611_ = lean_ctor_get(v___x_1610_, 2);
lean_inc(v_scopes_1611_);
lean_dec(v___x_1610_);
v___x_1612_ = l_List_head_x21___redArg(v___x_1609_, v_scopes_1611_);
lean_dec(v_scopes_1611_);
v_opts_1613_ = lean_ctor_get(v___x_1612_, 1);
lean_inc_ref(v_opts_1613_);
lean_dec(v___x_1612_);
v_hasTrace_1614_ = lean_ctor_get_uint8(v_opts_1613_, sizeof(void*)*1);
if (v_hasTrace_1614_ == 0)
{
lean_dec_ref(v_opts_1613_);
lean_dec(v___x_1608_);
v___y_1572_ = v___x_1601_;
v___y_1573_ = v___x_1602_;
v___y_1574_ = v___y_1517_;
v___y_1575_ = v___y_1518_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1616_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1608_, v_opts_1613_, v___x_1615_);
lean_dec_ref(v_opts_1613_);
lean_dec(v___x_1608_);
if (v___x_1616_ == 0)
{
v___y_1572_ = v___x_1601_;
v___y_1573_ = v___x_1602_;
v___y_1574_ = v___y_1517_;
v___y_1575_ = v___y_1518_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1618_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1606_, v___x_1617_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_dec_ref_known(v___x_1618_, 1);
v___y_1572_ = v___x_1601_;
v___y_1573_ = v___x_1602_;
v___y_1574_ = v___y_1517_;
v___y_1575_ = v___y_1518_;
goto v___jp_1571_;
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v___x_1602_);
lean_dec(v___x_1601_);
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref_known(v___x_1560_, 2);
lean_del_object(v___x_1529_);
lean_dec(v_snd_1527_);
lean_dec(v_fst_1526_);
lean_dec(v_cmd_1510_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
}
v___jp_1627_:
{
if (v_onUnsolved_1511_ == 0)
{
if (v___y_1512_ == 0)
{
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref_known(v___x_1560_, 2);
goto v___jp_1545_;
}
else
{
if (v___y_1628_ == 0)
{
lean_del_object(v___x_1569_);
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref_known(v___x_1560_, 2);
goto v___jp_1545_;
}
else
{
lean_del_object(v___x_1524_);
goto v___jp_1600_;
}
}
}
else
{
lean_del_object(v___x_1524_);
goto v___jp_1600_;
}
}
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_scopes_1636_; lean_object* v___x_1637_; lean_object* v_opts_1638_; uint8_t v_hasTrace_1639_; 
lean_dec(v___x_1564_);
lean_dec_ref_known(v___x_1560_, 2);
lean_del_object(v___x_1524_);
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1632_ = l_Lean_inheritedTraceOptions;
v___x_1633_ = lean_st_ref_get(v___x_1632_);
v___x_1634_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1635_ = lean_st_ref_get(v___y_1518_);
v_scopes_1636_ = lean_ctor_get(v___x_1635_, 2);
lean_inc(v_scopes_1636_);
lean_dec(v___x_1635_);
v___x_1637_ = l_List_head_x21___redArg(v___x_1634_, v_scopes_1636_);
lean_dec(v_scopes_1636_);
v_opts_1638_ = lean_ctor_get(v___x_1637_, 1);
lean_inc_ref(v_opts_1638_);
lean_dec(v___x_1637_);
v_hasTrace_1639_ = lean_ctor_get_uint8(v_opts_1638_, sizeof(void*)*1);
if (v_hasTrace_1639_ == 0)
{
lean_dec_ref(v_opts_1638_);
lean_dec(v___x_1633_);
lean_dec(v___x_1559_);
lean_dec(v___x_1558_);
lean_del_object(v___x_1556_);
goto v___jp_1549_;
}
else
{
lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1641_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1633_, v_opts_1638_, v___x_1640_);
lean_dec_ref(v_opts_1638_);
lean_dec(v___x_1633_);
if (v___x_1641_ == 0)
{
lean_dec(v___x_1559_);
lean_dec(v___x_1558_);
lean_del_object(v___x_1556_);
goto v___jp_1549_;
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1643_ = l_Nat_reprFast(v___x_1558_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 3);
lean_ctor_set(v___x_1556_, 0, v___x_1643_);
v___x_1645_ = v___x_1556_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1646_ = l_Lean_MessageData_ofFormat(v___x_1645_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1642_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Nat_reprFast(v___x_1559_);
v___x_1651_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
v___x_1652_ = l_Lean_MessageData_ofFormat(v___x_1651_);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1649_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1631_, v___x_1655_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_dec_ref_known(v___x_1656_, 1);
goto v___jp_1549_;
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1529_);
lean_dec(v_snd_1527_);
lean_dec(v_fst_1526_);
lean_dec(v_cmd_1510_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
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
lean_object* v___x_1667_; 
lean_dec(v_endPos_1533_);
lean_del_object(v___x_1524_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_fst_1526_);
lean_ctor_set(v___x_1667_, 1, v_snd_1527_);
v_a_1538_ = v___x_1667_;
goto v___jp_1537_;
}
}
}
else
{
lean_object* v___x_1668_; 
lean_dec(v_endPos_1533_);
lean_del_object(v___x_1524_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v_fst_1526_);
lean_ctor_set(v___x_1668_, 1, v_snd_1527_);
v_a_1538_ = v___x_1668_;
goto v___jp_1537_;
}
v___jp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 1, v_a_1538_);
lean_ctor_set(v___x_1529_, 0, v___x_1536_);
v___x_1540_ = v___x_1529_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_a_1538_);
v___x_1540_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = ((size_t)1ULL);
v___x_1542_ = lean_usize_add(v_i_1515_, v___x_1541_);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1508_, v_val_1509_, v_cmd_1510_, v_onUnsolved_1511_, v___y_1512_, v_as_1513_, v_sz_1514_, v___x_1542_, v___x_1540_, v___y_1517_, v___y_1518_);
return v___x_1543_;
}
}
v___jp_1545_:
{
lean_object* v___x_1547_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 1, v_snd_1527_);
lean_ctor_set(v___x_1524_, 0, v_fst_1526_);
v___x_1547_ = v___x_1524_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_fst_1526_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_snd_1527_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
v_a_1538_ = v___x_1547_;
goto v___jp_1537_;
}
}
v___jp_1549_:
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_fst_1526_);
lean_ctor_set(v___x_1550_, 1, v_snd_1527_);
v_a_1538_ = v___x_1550_;
goto v___jp_1537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object* v___x_1672_, lean_object* v_val_1673_, lean_object* v_cmd_1674_, lean_object* v_onUnsolved_1675_, lean_object* v___y_1676_, lean_object* v_as_1677_, lean_object* v_sz_1678_, lean_object* v_i_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
uint8_t v_onUnsolved_boxed_1684_; uint8_t v___y_12625__boxed_1685_; size_t v_sz_boxed_1686_; size_t v_i_boxed_1687_; lean_object* v_res_1688_; 
v_onUnsolved_boxed_1684_ = lean_unbox(v_onUnsolved_1675_);
v___y_12625__boxed_1685_ = lean_unbox(v___y_1676_);
v_sz_boxed_1686_ = lean_unbox_usize(v_sz_1678_);
lean_dec(v_sz_1678_);
v_i_boxed_1687_ = lean_unbox_usize(v_i_1679_);
lean_dec(v_i_1679_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_1672_, v_val_1673_, v_cmd_1674_, v_onUnsolved_boxed_1684_, v___y_12625__boxed_1685_, v_as_1677_, v_sz_boxed_1686_, v_i_boxed_1687_, v_b_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v_as_1677_);
lean_dec_ref(v_val_1673_);
lean_dec_ref(v___x_1672_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(lean_object* v___x_1689_, lean_object* v_val_1690_, lean_object* v_cmd_1691_, uint8_t v_onUnsolved_1692_, uint8_t v___y_1693_, lean_object* v_as_1694_, size_t v_sz_1695_, size_t v_i_1696_, lean_object* v_b_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_usize_dec_lt(v_i_1696_, v_sz_1695_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
lean_dec(v_cmd_1691_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_b_1697_);
return v___x_1702_;
}
else
{
lean_object* v_snd_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1851_; 
v_snd_1703_ = lean_ctor_get(v_b_1697_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_b_1697_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v_b_1697_, 0);
lean_dec(v_unused_1852_);
v___x_1705_ = v_b_1697_;
v_isShared_1706_ = v_isSharedCheck_1851_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_snd_1703_);
lean_dec(v_b_1697_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1851_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_fst_1707_; lean_object* v_snd_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1850_; 
v_fst_1707_ = lean_ctor_get(v_snd_1703_, 0);
v_snd_1708_ = lean_ctor_get(v_snd_1703_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_snd_1703_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1710_ = v_snd_1703_;
v_isShared_1711_ = v_isSharedCheck_1850_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_snd_1708_);
lean_inc(v_fst_1707_);
lean_dec(v_snd_1703_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1850_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_a_1712_; lean_object* v_pos_1713_; lean_object* v_endPos_1714_; uint8_t v_severity_1715_; lean_object* v_data_1716_; lean_object* v___x_1717_; lean_object* v_a_1719_; 
v_a_1712_ = lean_array_uget_borrowed(v_as_1694_, v_i_1696_);
v_pos_1713_ = lean_ctor_get(v_a_1712_, 1);
v_endPos_1714_ = lean_ctor_get(v_a_1712_, 2);
lean_inc(v_endPos_1714_);
v_severity_1715_ = lean_ctor_get_uint8(v_a_1712_, sizeof(void*)*5 + 1);
v_data_1716_ = lean_ctor_get(v_a_1712_, 4);
v___x_1717_ = lean_box(0);
if (v_severity_1715_ == 2)
{
lean_object* v___f_1732_; uint8_t v___x_1733_; 
v___f_1732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1716_);
v___x_1733_ = l_Lean_MessageData_hasTag(v___f_1732_, v_data_1716_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec(v_endPos_1714_);
lean_del_object(v___x_1705_);
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v_fst_1707_);
lean_ctor_set(v___x_1734_, 1, v_snd_1708_);
v_a_1719_ = v___x_1734_;
goto v___jp_1718_;
}
else
{
if (lean_obj_tag(v_endPos_1714_) == 1)
{
lean_object* v_val_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1847_; 
v_val_1735_ = lean_ctor_get(v_endPos_1714_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_endPos_1714_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1737_ = v_endPos_1714_;
v_isShared_1738_ = v_isSharedCheck_1847_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_val_1735_);
lean_dec(v_endPos_1714_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1847_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; uint8_t v___x_1743_; 
lean_inc_ref(v_pos_1713_);
v___x_1739_ = l_Lean_FileMap_ofPosition(v___x_1689_, v_pos_1713_);
v___x_1740_ = l_Lean_FileMap_ofPosition(v___x_1689_, v_val_1735_);
lean_inc(v___x_1740_);
lean_inc(v___x_1739_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = 0;
v___x_1743_ = l_Lean_Syntax_Range_includes(v_val_1690_, v___x_1741_, v___x_1742_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec_ref_known(v___x_1741_, 2);
lean_dec(v___x_1740_);
lean_dec(v___x_1739_);
lean_del_object(v___x_1737_);
lean_del_object(v___x_1705_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v_fst_1707_);
lean_ctor_set(v___x_1744_, 1, v_snd_1708_);
v_a_1719_ = v___x_1744_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1745_; 
lean_inc(v_cmd_1691_);
lean_inc_ref(v___x_1741_);
v___x_1745_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1741_, v_cmd_1691_);
if (lean_obj_tag(v___x_1745_) == 1)
{
lean_object* v_val_1746_; lean_object* v_fst_1747_; lean_object* v_snd_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v___x_1740_);
lean_dec(v___x_1739_);
lean_del_object(v___x_1737_);
v_val_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v_fst_1747_ = lean_ctor_get(v_val_1746_, 0);
v_snd_1748_ = lean_ctor_get(v_val_1746_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_val_1746_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1750_ = v_val_1746_;
v_isShared_1751_ = v_isSharedCheck_1811_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snd_1748_);
lean_inc(v_fst_1747_);
lean_dec(v_val_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1811_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; uint8_t v___y_1809_; lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Syntax_getPos_x3f(v_fst_1747_, v___x_1742_);
if (lean_obj_tag(v___x_1810_) == 0)
{
v___y_1809_ = v___x_1743_;
goto v___jp_1808_;
}
else
{
lean_dec_ref_known(v___x_1810_, 1);
v___y_1809_ = v___x_1742_;
goto v___jp_1808_;
}
v___jp_1752_:
{
lean_object* v___x_1758_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v_snd_1708_);
lean_ctor_set(v___x_1750_, 0, v_fst_1707_);
v___x_1758_ = v___x_1750_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_fst_1707_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_snd_1708_);
v___x_1758_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
size_t v_sz_1759_; size_t v___x_1760_; lean_object* v___x_1761_; 
v_sz_1759_ = lean_array_size(v___y_1753_);
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1741_, v_fst_1747_, v_snd_1748_, v___y_1754_, v___y_1753_, v_sz_1759_, v___x_1760_, v___x_1758_);
lean_dec_ref(v___y_1753_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v_fst_1763_ = lean_ctor_get(v_a_1762_, 0);
v_snd_1764_ = lean_ctor_get(v_a_1762_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v_a_1762_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snd_1764_);
lean_inc(v_fst_1763_);
lean_dec(v_a_1762_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_fst_1763_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_snd_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
v_a_1719_ = v___x_1769_;
goto v___jp_1718_;
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_del_object(v___x_1710_);
lean_dec(v_cmd_1691_);
v_a_1772_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1761_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1761_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
v___jp_1781_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
lean_inc_ref(v___x_1741_);
v___x_1782_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1741_);
v___x_1783_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1716_);
v___x_1784_ = lean_array_get_size(v___x_1783_);
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = lean_nat_dec_eq(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
v___y_1753_ = v___x_1783_;
v___y_1754_ = v___x_1782_;
v___y_1755_ = v___y_1698_;
v___y_1756_ = v___y_1699_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_scopes_1792_; lean_object* v___x_1793_; lean_object* v_opts_1794_; uint8_t v_hasTrace_1795_; 
v___x_1787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1788_ = l_Lean_inheritedTraceOptions;
v___x_1789_ = lean_st_ref_get(v___x_1788_);
v___x_1790_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1791_ = lean_st_ref_get(v___y_1699_);
v_scopes_1792_ = lean_ctor_get(v___x_1791_, 2);
lean_inc(v_scopes_1792_);
lean_dec(v___x_1791_);
v___x_1793_ = l_List_head_x21___redArg(v___x_1790_, v_scopes_1792_);
lean_dec(v_scopes_1792_);
v_opts_1794_ = lean_ctor_get(v___x_1793_, 1);
lean_inc_ref(v_opts_1794_);
lean_dec(v___x_1793_);
v_hasTrace_1795_ = lean_ctor_get_uint8(v_opts_1794_, sizeof(void*)*1);
if (v_hasTrace_1795_ == 0)
{
lean_dec_ref(v_opts_1794_);
lean_dec(v___x_1789_);
v___y_1753_ = v___x_1783_;
v___y_1754_ = v___x_1782_;
v___y_1755_ = v___y_1698_;
v___y_1756_ = v___y_1699_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1789_, v_opts_1794_, v___x_1796_);
lean_dec_ref(v_opts_1794_);
lean_dec(v___x_1789_);
if (v___x_1797_ == 0)
{
v___y_1753_ = v___x_1783_;
v___y_1754_ = v___x_1782_;
v___y_1755_ = v___y_1698_;
v___y_1756_ = v___y_1699_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1799_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1787_, v___x_1798_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_dec_ref_known(v___x_1799_, 1);
v___y_1753_ = v___x_1783_;
v___y_1754_ = v___x_1782_;
v___y_1755_ = v___y_1698_;
v___y_1756_ = v___y_1699_;
goto v___jp_1752_;
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v___x_1783_);
lean_dec(v___x_1782_);
lean_del_object(v___x_1750_);
lean_dec(v_snd_1748_);
lean_dec(v_fst_1747_);
lean_dec_ref_known(v___x_1741_, 2);
lean_del_object(v___x_1710_);
lean_dec(v_snd_1708_);
lean_dec(v_fst_1707_);
lean_dec(v_cmd_1691_);
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
}
v___jp_1808_:
{
if (v_onUnsolved_1692_ == 0)
{
if (v___y_1693_ == 0)
{
lean_del_object(v___x_1750_);
lean_dec(v_snd_1748_);
lean_dec(v_fst_1747_);
lean_dec_ref_known(v___x_1741_, 2);
goto v___jp_1726_;
}
else
{
if (v___y_1809_ == 0)
{
lean_del_object(v___x_1750_);
lean_dec(v_snd_1748_);
lean_dec(v_fst_1747_);
lean_dec_ref_known(v___x_1741_, 2);
goto v___jp_1726_;
}
else
{
lean_del_object(v___x_1705_);
goto v___jp_1781_;
}
}
}
else
{
lean_del_object(v___x_1705_);
goto v___jp_1781_;
}
}
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v_scopes_1817_; lean_object* v___x_1818_; lean_object* v_opts_1819_; uint8_t v_hasTrace_1820_; 
lean_dec(v___x_1745_);
lean_dec_ref_known(v___x_1741_, 2);
lean_del_object(v___x_1705_);
v___x_1812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1813_ = l_Lean_inheritedTraceOptions;
v___x_1814_ = lean_st_ref_get(v___x_1813_);
v___x_1815_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1816_ = lean_st_ref_get(v___y_1699_);
v_scopes_1817_ = lean_ctor_get(v___x_1816_, 2);
lean_inc(v_scopes_1817_);
lean_dec(v___x_1816_);
v___x_1818_ = l_List_head_x21___redArg(v___x_1815_, v_scopes_1817_);
lean_dec(v_scopes_1817_);
v_opts_1819_ = lean_ctor_get(v___x_1818_, 1);
lean_inc_ref(v_opts_1819_);
lean_dec(v___x_1818_);
v_hasTrace_1820_ = lean_ctor_get_uint8(v_opts_1819_, sizeof(void*)*1);
if (v_hasTrace_1820_ == 0)
{
lean_dec_ref(v_opts_1819_);
lean_dec(v___x_1814_);
lean_dec(v___x_1740_);
lean_dec(v___x_1739_);
lean_del_object(v___x_1737_);
goto v___jp_1730_;
}
else
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1822_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1814_, v_opts_1819_, v___x_1821_);
lean_dec_ref(v_opts_1819_);
lean_dec(v___x_1814_);
if (v___x_1822_ == 0)
{
lean_dec(v___x_1740_);
lean_dec(v___x_1739_);
lean_del_object(v___x_1737_);
goto v___jp_1730_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1824_ = l_Nat_reprFast(v___x_1739_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 3);
lean_ctor_set(v___x_1737_, 0, v___x_1824_);
v___x_1826_ = v___x_1737_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1827_ = l_Lean_MessageData_ofFormat(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1823_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = l_Nat_reprFast(v___x_1740_);
v___x_1832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
v___x_1833_ = l_Lean_MessageData_ofFormat(v___x_1832_);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1830_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1812_, v___x_1836_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_dec_ref_known(v___x_1837_, 1);
goto v___jp_1730_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_del_object(v___x_1710_);
lean_dec(v_snd_1708_);
lean_dec(v_fst_1707_);
lean_dec(v_cmd_1691_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
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
lean_object* v___x_1848_; 
lean_dec(v_endPos_1714_);
lean_del_object(v___x_1705_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_fst_1707_);
lean_ctor_set(v___x_1848_, 1, v_snd_1708_);
v_a_1719_ = v___x_1848_;
goto v___jp_1718_;
}
}
}
else
{
lean_object* v___x_1849_; 
lean_dec(v_endPos_1714_);
lean_del_object(v___x_1705_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v_fst_1707_);
lean_ctor_set(v___x_1849_, 1, v_snd_1708_);
v_a_1719_ = v___x_1849_;
goto v___jp_1718_;
}
v___jp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 1, v_a_1719_);
lean_ctor_set(v___x_1710_, 0, v___x_1717_);
v___x_1721_ = v___x_1710_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_a_1719_);
v___x_1721_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
size_t v___x_1722_; size_t v___x_1723_; 
v___x_1722_ = ((size_t)1ULL);
v___x_1723_ = lean_usize_add(v_i_1696_, v___x_1722_);
v_i_1696_ = v___x_1723_;
v_b_1697_ = v___x_1721_;
goto _start;
}
}
v___jp_1726_:
{
lean_object* v___x_1728_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v_snd_1708_);
lean_ctor_set(v___x_1705_, 0, v_fst_1707_);
v___x_1728_ = v___x_1705_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_fst_1707_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_snd_1708_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v_a_1719_ = v___x_1728_;
goto v___jp_1718_;
}
}
v___jp_1730_:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_fst_1707_);
lean_ctor_set(v___x_1731_, 1, v_snd_1708_);
v_a_1719_ = v___x_1731_;
goto v___jp_1718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v___x_1853_, lean_object* v_val_1854_, lean_object* v_cmd_1855_, lean_object* v_onUnsolved_1856_, lean_object* v___y_1857_, lean_object* v_as_1858_, lean_object* v_sz_1859_, lean_object* v_i_1860_, lean_object* v_b_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v_onUnsolved_boxed_1865_; uint8_t v___y_12957__boxed_1866_; size_t v_sz_boxed_1867_; size_t v_i_boxed_1868_; lean_object* v_res_1869_; 
v_onUnsolved_boxed_1865_ = lean_unbox(v_onUnsolved_1856_);
v___y_12957__boxed_1866_ = lean_unbox(v___y_1857_);
v_sz_boxed_1867_ = lean_unbox_usize(v_sz_1859_);
lean_dec(v_sz_1859_);
v_i_boxed_1868_ = lean_unbox_usize(v_i_1860_);
lean_dec(v_i_1860_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1853_, v_val_1854_, v_cmd_1855_, v_onUnsolved_boxed_1865_, v___y_12957__boxed_1866_, v_as_1858_, v_sz_boxed_1867_, v_i_boxed_1868_, v_b_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_as_1858_);
lean_dec_ref(v_val_1854_);
lean_dec_ref(v___x_1853_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(lean_object* v___x_1870_, lean_object* v_val_1871_, lean_object* v_cmd_1872_, uint8_t v_onUnsolved_1873_, uint8_t v___y_1874_, lean_object* v_as_1875_, size_t v_sz_1876_, size_t v_i_1877_, lean_object* v_b_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_usize_dec_lt(v_i_1877_, v_sz_1876_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; 
lean_dec(v_cmd_1872_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_b_1878_);
return v___x_1883_;
}
else
{
lean_object* v_snd_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_2032_; 
v_snd_1884_ = lean_ctor_get(v_b_1878_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_b_1878_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v_b_1878_, 0);
lean_dec(v_unused_2033_);
v___x_1886_ = v_b_1878_;
v_isShared_1887_ = v_isSharedCheck_2032_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_snd_1884_);
lean_dec(v_b_1878_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_2032_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_2031_; 
v_fst_1888_ = lean_ctor_get(v_snd_1884_, 0);
v_snd_1889_ = lean_ctor_get(v_snd_1884_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_snd_1884_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1891_ = v_snd_1884_;
v_isShared_1892_ = v_isSharedCheck_2031_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_inc(v_fst_1888_);
lean_dec(v_snd_1884_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_2031_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_a_1893_; lean_object* v_pos_1894_; lean_object* v_endPos_1895_; uint8_t v_severity_1896_; lean_object* v_data_1897_; lean_object* v___x_1898_; lean_object* v_a_1900_; 
v_a_1893_ = lean_array_uget_borrowed(v_as_1875_, v_i_1877_);
v_pos_1894_ = lean_ctor_get(v_a_1893_, 1);
v_endPos_1895_ = lean_ctor_get(v_a_1893_, 2);
lean_inc(v_endPos_1895_);
v_severity_1896_ = lean_ctor_get_uint8(v_a_1893_, sizeof(void*)*5 + 1);
v_data_1897_ = lean_ctor_get(v_a_1893_, 4);
v___x_1898_ = lean_box(0);
if (v_severity_1896_ == 2)
{
lean_object* v___f_1913_; uint8_t v___x_1914_; 
v___f_1913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1897_);
v___x_1914_ = l_Lean_MessageData_hasTag(v___f_1913_, v_data_1897_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec(v_endPos_1895_);
lean_del_object(v___x_1886_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_fst_1888_);
lean_ctor_set(v___x_1915_, 1, v_snd_1889_);
v_a_1900_ = v___x_1915_;
goto v___jp_1899_;
}
else
{
if (lean_obj_tag(v_endPos_1895_) == 1)
{
lean_object* v_val_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_2028_; 
v_val_1916_ = lean_ctor_get(v_endPos_1895_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_endPos_1895_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1918_ = v_endPos_1895_;
v_isShared_1919_ = v_isSharedCheck_2028_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_val_1916_);
lean_dec(v_endPos_1895_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_2028_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; uint8_t v___x_1924_; 
lean_inc_ref(v_pos_1894_);
v___x_1920_ = l_Lean_FileMap_ofPosition(v___x_1870_, v_pos_1894_);
v___x_1921_ = l_Lean_FileMap_ofPosition(v___x_1870_, v_val_1916_);
lean_inc(v___x_1921_);
lean_inc(v___x_1920_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = 0;
v___x_1924_ = l_Lean_Syntax_Range_includes(v_val_1871_, v___x_1922_, v___x_1923_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref_known(v___x_1922_, 2);
lean_dec(v___x_1921_);
lean_dec(v___x_1920_);
lean_del_object(v___x_1918_);
lean_del_object(v___x_1886_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_fst_1888_);
lean_ctor_set(v___x_1925_, 1, v_snd_1889_);
v_a_1900_ = v___x_1925_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1926_; 
lean_inc(v_cmd_1872_);
lean_inc_ref(v___x_1922_);
v___x_1926_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1922_, v_cmd_1872_);
if (lean_obj_tag(v___x_1926_) == 1)
{
lean_object* v_val_1927_; lean_object* v_fst_1928_; lean_object* v_snd_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v___x_1921_);
lean_dec(v___x_1920_);
lean_del_object(v___x_1918_);
v_val_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_val_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v_fst_1928_ = lean_ctor_get(v_val_1927_, 0);
v_snd_1929_ = lean_ctor_get(v_val_1927_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_val_1927_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1931_ = v_val_1927_;
v_isShared_1932_ = v_isSharedCheck_1992_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_snd_1929_);
lean_inc(v_fst_1928_);
lean_dec(v_val_1927_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1992_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; uint8_t v___y_1990_; lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Syntax_getPos_x3f(v_fst_1928_, v___x_1923_);
if (lean_obj_tag(v___x_1991_) == 0)
{
v___y_1990_ = v___x_1924_;
goto v___jp_1989_;
}
else
{
lean_dec_ref_known(v___x_1991_, 1);
v___y_1990_ = v___x_1923_;
goto v___jp_1989_;
}
v___jp_1933_:
{
lean_object* v___x_1939_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 1, v_snd_1889_);
lean_ctor_set(v___x_1931_, 0, v_fst_1888_);
v___x_1939_ = v___x_1931_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_fst_1888_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_snd_1889_);
v___x_1939_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
size_t v_sz_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v_sz_1940_ = lean_array_size(v___y_1934_);
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1922_, v_fst_1928_, v_snd_1929_, v___y_1935_, v___y_1934_, v_sz_1940_, v___x_1941_, v___x_1939_);
lean_dec_ref(v___y_1934_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v_fst_1944_ = lean_ctor_get(v_a_1943_, 0);
v_snd_1945_ = lean_ctor_get(v_a_1943_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_a_1943_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v_a_1943_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_snd_1945_);
lean_inc(v_fst_1944_);
lean_dec(v_a_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_fst_1944_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_snd_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
v_a_1900_ = v___x_1950_;
goto v___jp_1899_;
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_del_object(v___x_1891_);
lean_dec(v_cmd_1872_);
v_a_1953_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1942_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1942_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
v___jp_1962_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
lean_inc_ref(v___x_1922_);
v___x_1963_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1922_);
v___x_1964_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1897_);
v___x_1965_ = lean_array_get_size(v___x_1964_);
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = lean_nat_dec_eq(v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
v___y_1934_ = v___x_1964_;
v___y_1935_ = v___x_1963_;
v___y_1936_ = v___y_1879_;
v___y_1937_ = v___y_1880_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_scopes_1973_; lean_object* v___x_1974_; lean_object* v_opts_1975_; uint8_t v_hasTrace_1976_; 
v___x_1968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1969_ = l_Lean_inheritedTraceOptions;
v___x_1970_ = lean_st_ref_get(v___x_1969_);
v___x_1971_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1972_ = lean_st_ref_get(v___y_1880_);
v_scopes_1973_ = lean_ctor_get(v___x_1972_, 2);
lean_inc(v_scopes_1973_);
lean_dec(v___x_1972_);
v___x_1974_ = l_List_head_x21___redArg(v___x_1971_, v_scopes_1973_);
lean_dec(v_scopes_1973_);
v_opts_1975_ = lean_ctor_get(v___x_1974_, 1);
lean_inc_ref(v_opts_1975_);
lean_dec(v___x_1974_);
v_hasTrace_1976_ = lean_ctor_get_uint8(v_opts_1975_, sizeof(void*)*1);
if (v_hasTrace_1976_ == 0)
{
lean_dec_ref(v_opts_1975_);
lean_dec(v___x_1970_);
v___y_1934_ = v___x_1964_;
v___y_1935_ = v___x_1963_;
v___y_1936_ = v___y_1879_;
v___y_1937_ = v___y_1880_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1978_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1970_, v_opts_1975_, v___x_1977_);
lean_dec_ref(v_opts_1975_);
lean_dec(v___x_1970_);
if (v___x_1978_ == 0)
{
v___y_1934_ = v___x_1964_;
v___y_1935_ = v___x_1963_;
v___y_1936_ = v___y_1879_;
v___y_1937_ = v___y_1880_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1980_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1968_, v___x_1979_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_dec_ref_known(v___x_1980_, 1);
v___y_1934_ = v___x_1964_;
v___y_1935_ = v___x_1963_;
v___y_1936_ = v___y_1879_;
v___y_1937_ = v___y_1880_;
goto v___jp_1933_;
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v___x_1964_);
lean_dec(v___x_1963_);
lean_del_object(v___x_1931_);
lean_dec(v_snd_1929_);
lean_dec(v_fst_1928_);
lean_dec_ref_known(v___x_1922_, 2);
lean_del_object(v___x_1891_);
lean_dec(v_snd_1889_);
lean_dec(v_fst_1888_);
lean_dec(v_cmd_1872_);
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
}
}
v___jp_1989_:
{
if (v_onUnsolved_1873_ == 0)
{
if (v___y_1874_ == 0)
{
lean_del_object(v___x_1931_);
lean_dec(v_snd_1929_);
lean_dec(v_fst_1928_);
lean_dec_ref_known(v___x_1922_, 2);
goto v___jp_1907_;
}
else
{
if (v___y_1990_ == 0)
{
lean_del_object(v___x_1931_);
lean_dec(v_snd_1929_);
lean_dec(v_fst_1928_);
lean_dec_ref_known(v___x_1922_, 2);
goto v___jp_1907_;
}
else
{
lean_del_object(v___x_1886_);
goto v___jp_1962_;
}
}
}
else
{
lean_del_object(v___x_1886_);
goto v___jp_1962_;
}
}
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_scopes_1998_; lean_object* v___x_1999_; lean_object* v_opts_2000_; uint8_t v_hasTrace_2001_; 
lean_dec(v___x_1926_);
lean_dec_ref_known(v___x_1922_, 2);
lean_del_object(v___x_1886_);
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1994_ = l_Lean_inheritedTraceOptions;
v___x_1995_ = lean_st_ref_get(v___x_1994_);
v___x_1996_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1997_ = lean_st_ref_get(v___y_1880_);
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
lean_dec(v___x_1921_);
lean_dec(v___x_1920_);
lean_del_object(v___x_1918_);
goto v___jp_1911_;
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
lean_dec(v___x_1921_);
lean_dec(v___x_1920_);
lean_del_object(v___x_1918_);
goto v___jp_1911_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_2005_ = l_Nat_reprFast(v___x_1920_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 3);
lean_ctor_set(v___x_1918_, 0, v___x_2005_);
v___x_2007_ = v___x_1918_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2008_ = l_Lean_MessageData_ofFormat(v___x_2007_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2004_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = l_Nat_reprFast(v___x_1921_);
v___x_2013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
v___x_2014_ = l_Lean_MessageData_ofFormat(v___x_2013_);
v___x_2015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2011_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_2017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1993_, v___x_2017_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_dec_ref_known(v___x_2018_, 1);
goto v___jp_1911_;
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_del_object(v___x_1891_);
lean_dec(v_snd_1889_);
lean_dec(v_fst_1888_);
lean_dec(v_cmd_1872_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
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
lean_object* v___x_2029_; 
lean_dec(v_endPos_1895_);
lean_del_object(v___x_1886_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_fst_1888_);
lean_ctor_set(v___x_2029_, 1, v_snd_1889_);
v_a_1900_ = v___x_2029_;
goto v___jp_1899_;
}
}
}
else
{
lean_object* v___x_2030_; 
lean_dec(v_endPos_1895_);
lean_del_object(v___x_1886_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_fst_1888_);
lean_ctor_set(v___x_2030_, 1, v_snd_1889_);
v_a_1900_ = v___x_2030_;
goto v___jp_1899_;
}
v___jp_1899_:
{
lean_object* v___x_1902_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v_a_1900_);
lean_ctor_set(v___x_1891_, 0, v___x_1898_);
v___x_1902_ = v___x_1891_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_a_1900_);
v___x_1902_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = lean_usize_add(v_i_1877_, v___x_1903_);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1870_, v_val_1871_, v_cmd_1872_, v_onUnsolved_1873_, v___y_1874_, v_as_1875_, v_sz_1876_, v___x_1904_, v___x_1902_, v___y_1879_, v___y_1880_);
return v___x_1905_;
}
}
v___jp_1907_:
{
lean_object* v___x_1909_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v_snd_1889_);
lean_ctor_set(v___x_1886_, 0, v_fst_1888_);
v___x_1909_ = v___x_1886_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_fst_1888_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_snd_1889_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
v_a_1900_ = v___x_1909_;
goto v___jp_1899_;
}
}
v___jp_1911_:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v_fst_1888_);
lean_ctor_set(v___x_1912_, 1, v_snd_1889_);
v_a_1900_ = v___x_1912_;
goto v___jp_1899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11___boxed(lean_object* v___x_2034_, lean_object* v_val_2035_, lean_object* v_cmd_2036_, lean_object* v_onUnsolved_2037_, lean_object* v___y_2038_, lean_object* v_as_2039_, lean_object* v_sz_2040_, lean_object* v_i_2041_, lean_object* v_b_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v_onUnsolved_boxed_2046_; uint8_t v___y_13289__boxed_2047_; size_t v_sz_boxed_2048_; size_t v_i_boxed_2049_; lean_object* v_res_2050_; 
v_onUnsolved_boxed_2046_ = lean_unbox(v_onUnsolved_2037_);
v___y_13289__boxed_2047_ = lean_unbox(v___y_2038_);
v_sz_boxed_2048_ = lean_unbox_usize(v_sz_2040_);
lean_dec(v_sz_2040_);
v_i_boxed_2049_ = lean_unbox_usize(v_i_2041_);
lean_dec(v_i_2041_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2034_, v_val_2035_, v_cmd_2036_, v_onUnsolved_boxed_2046_, v___y_13289__boxed_2047_, v_as_2039_, v_sz_boxed_2048_, v_i_boxed_2049_, v_b_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec_ref(v_as_2039_);
lean_dec_ref(v_val_2035_);
lean_dec_ref(v___x_2034_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(lean_object* v_init_2051_, lean_object* v___x_2052_, lean_object* v_val_2053_, lean_object* v_cmd_2054_, uint8_t v_onUnsolved_2055_, uint8_t v___y_2056_, lean_object* v_n_2057_, lean_object* v_b_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
if (lean_obj_tag(v_n_2057_) == 0)
{
lean_object* v_cs_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; size_t v_sz_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
v_cs_2062_ = lean_ctor_get(v_n_2057_, 0);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v_b_2058_);
v_sz_2065_ = lean_array_size(v_cs_2062_);
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2051_, v___x_2052_, v_val_2053_, v_cmd_2054_, v_onUnsolved_2055_, v___y_2056_, v_cs_2062_, v_sz_2065_, v___x_2066_, v___x_2064_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2082_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2082_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2082_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_fst_2072_; 
v_fst_2072_ = lean_ctor_get(v_a_2068_, 0);
if (lean_obj_tag(v_fst_2072_) == 0)
{
lean_object* v_snd_2073_; lean_object* v___x_2074_; lean_object* v___x_2076_; 
v_snd_2073_ = lean_ctor_get(v_a_2068_, 1);
lean_inc(v_snd_2073_);
lean_dec(v_a_2068_);
v___x_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_snd_2073_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2074_);
v___x_2076_ = v___x_2070_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
else
{
lean_object* v_val_2078_; lean_object* v___x_2080_; 
lean_inc_ref(v_fst_2072_);
lean_dec(v_a_2068_);
v_val_2078_ = lean_ctor_get(v_fst_2072_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v_fst_2072_, 1);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v_val_2078_);
v___x_2080_ = v___x_2070_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_val_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_a_2083_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2067_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2067_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_vs_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; size_t v_sz_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
v_vs_2091_ = lean_ctor_get(v_n_2057_, 0);
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v_b_2058_);
v_sz_2094_ = lean_array_size(v_vs_2091_);
v___x_2095_ = ((size_t)0ULL);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2052_, v_val_2053_, v_cmd_2054_, v_onUnsolved_2055_, v___y_2056_, v_vs_2091_, v_sz_2094_, v___x_2095_, v___x_2093_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2111_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2111_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_fst_2101_; 
v_fst_2101_ = lean_ctor_get(v_a_2097_, 0);
if (lean_obj_tag(v_fst_2101_) == 0)
{
lean_object* v_snd_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v_snd_2102_ = lean_ctor_get(v_a_2097_, 1);
lean_inc(v_snd_2102_);
lean_dec(v_a_2097_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_snd_2102_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2103_);
v___x_2105_ = v___x_2099_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
else
{
lean_object* v_val_2107_; lean_object* v___x_2109_; 
lean_inc_ref(v_fst_2101_);
lean_dec(v_a_2097_);
v_val_2107_ = lean_ctor_get(v_fst_2101_, 0);
lean_inc(v_val_2107_);
lean_dec_ref_known(v_fst_2101_, 1);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v_val_2107_);
v___x_2109_ = v___x_2099_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_val_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2096_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2096_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(lean_object* v_init_2120_, lean_object* v___x_2121_, lean_object* v_val_2122_, lean_object* v_cmd_2123_, uint8_t v_onUnsolved_2124_, uint8_t v___y_2125_, lean_object* v_as_2126_, size_t v_sz_2127_, size_t v_i_2128_, lean_object* v_b_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_usize_dec_lt(v_i_2128_, v_sz_2127_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; 
lean_dec(v_cmd_2123_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v_b_2129_);
return v___x_2134_;
}
else
{
lean_object* v_snd_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2169_; 
v_snd_2135_ = lean_ctor_get(v_b_2129_, 1);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_b_2129_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v_b_2129_, 0);
lean_dec(v_unused_2170_);
v___x_2137_ = v_b_2129_;
v_isShared_2138_ = v_isSharedCheck_2169_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_snd_2135_);
lean_dec(v_b_2129_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2169_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v_a_2140_; lean_object* v___x_2141_; 
v___x_2139_ = lean_box(0);
v_a_2140_ = lean_array_uget_borrowed(v_as_2126_, v_i_2128_);
lean_inc(v_snd_2135_);
lean_inc(v_cmd_2123_);
v___x_2141_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2120_, v___x_2121_, v_val_2122_, v_cmd_2123_, v_onUnsolved_2124_, v___y_2125_, v_a_2140_, v_snd_2135_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2160_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2160_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2160_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
if (lean_obj_tag(v_a_2142_) == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v_cmd_2123_);
v___x_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_a_2142_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2146_);
v___x_2148_ = v___x_2137_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_snd_2135_);
v___x_2148_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2148_);
v___x_2150_ = v___x_2144_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; 
lean_del_object(v___x_2144_);
lean_dec(v_snd_2135_);
v_a_2153_ = lean_ctor_get(v_a_2142_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v_a_2142_, 1);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 1, v_a_2153_);
lean_ctor_set(v___x_2137_, 0, v___x_2139_);
v___x_2155_ = v___x_2137_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_a_2153_);
v___x_2155_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
size_t v___x_2156_; size_t v___x_2157_; 
v___x_2156_ = ((size_t)1ULL);
v___x_2157_ = lean_usize_add(v_i_2128_, v___x_2156_);
v_i_2128_ = v___x_2157_;
v_b_2129_ = v___x_2155_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_del_object(v___x_2137_);
lean_dec(v_snd_2135_);
lean_dec(v_cmd_2123_);
v_a_2161_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2141_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2141_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10___boxed(lean_object* v_init_2171_, lean_object* v___x_2172_, lean_object* v_val_2173_, lean_object* v_cmd_2174_, lean_object* v_onUnsolved_2175_, lean_object* v___y_2176_, lean_object* v_as_2177_, lean_object* v_sz_2178_, lean_object* v_i_2179_, lean_object* v_b_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v_onUnsolved_boxed_2184_; uint8_t v___y_13590__boxed_2185_; size_t v_sz_boxed_2186_; size_t v_i_boxed_2187_; lean_object* v_res_2188_; 
v_onUnsolved_boxed_2184_ = lean_unbox(v_onUnsolved_2175_);
v___y_13590__boxed_2185_ = lean_unbox(v___y_2176_);
v_sz_boxed_2186_ = lean_unbox_usize(v_sz_2178_);
lean_dec(v_sz_2178_);
v_i_boxed_2187_ = lean_unbox_usize(v_i_2179_);
lean_dec(v_i_2179_);
v_res_2188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2171_, v___x_2172_, v_val_2173_, v_cmd_2174_, v_onUnsolved_boxed_2184_, v___y_13590__boxed_2185_, v_as_2177_, v_sz_boxed_2186_, v_i_boxed_2187_, v_b_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec_ref(v_as_2177_);
lean_dec_ref(v_val_2173_);
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_init_2171_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8___boxed(lean_object* v_init_2189_, lean_object* v___x_2190_, lean_object* v_val_2191_, lean_object* v_cmd_2192_, lean_object* v_onUnsolved_2193_, lean_object* v___y_2194_, lean_object* v_n_2195_, lean_object* v_b_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v_onUnsolved_boxed_2200_; uint8_t v___y_13612__boxed_2201_; lean_object* v_res_2202_; 
v_onUnsolved_boxed_2200_ = lean_unbox(v_onUnsolved_2193_);
v___y_13612__boxed_2201_ = lean_unbox(v___y_2194_);
v_res_2202_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2189_, v___x_2190_, v_val_2191_, v_cmd_2192_, v_onUnsolved_boxed_2200_, v___y_13612__boxed_2201_, v_n_2195_, v_b_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec_ref(v_n_2195_);
lean_dec_ref(v_val_2191_);
lean_dec_ref(v___x_2190_);
lean_dec_ref(v_init_2189_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object* v___x_2203_, lean_object* v_val_2204_, lean_object* v_cmd_2205_, uint8_t v_onUnsolved_2206_, uint8_t v___y_2207_, lean_object* v_t_2208_, lean_object* v_init_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_root_2213_; lean_object* v_tail_2214_; lean_object* v___x_2215_; 
v_root_2213_ = lean_ctor_get(v_t_2208_, 0);
v_tail_2214_ = lean_ctor_get(v_t_2208_, 1);
lean_inc(v_cmd_2205_);
lean_inc_ref(v_init_2209_);
v___x_2215_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2209_, v___x_2203_, v_val_2204_, v_cmd_2205_, v_onUnsolved_2206_, v___y_2207_, v_root_2213_, v_init_2209_, v___y_2210_, v___y_2211_);
lean_dec_ref(v_init_2209_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2252_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2252_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2252_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
if (lean_obj_tag(v_a_2216_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; 
lean_dec(v_cmd_2205_);
v_a_2220_ = lean_ctor_get(v_a_2216_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v_a_2216_, 1);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v_a_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; size_t v_sz_2227_; size_t v___x_2228_; lean_object* v___x_2229_; 
lean_del_object(v___x_2218_);
v_a_2224_ = lean_ctor_get(v_a_2216_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v_a_2216_, 1);
v___x_2225_ = lean_box(0);
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v_a_2224_);
v_sz_2227_ = lean_array_size(v_tail_2214_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_2203_, v_val_2204_, v_cmd_2205_, v_onUnsolved_2206_, v___y_2207_, v_tail_2214_, v_sz_2227_, v___x_2228_, v___x_2226_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2243_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2243_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2243_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_fst_2234_; 
v_fst_2234_ = lean_ctor_get(v_a_2230_, 0);
if (lean_obj_tag(v_fst_2234_) == 0)
{
lean_object* v_snd_2235_; lean_object* v___x_2237_; 
v_snd_2235_ = lean_ctor_get(v_a_2230_, 1);
lean_inc(v_snd_2235_);
lean_dec(v_a_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_snd_2235_);
v___x_2237_ = v___x_2232_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_snd_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
else
{
lean_object* v_val_2239_; lean_object* v___x_2241_; 
lean_inc_ref(v_fst_2234_);
lean_dec(v_a_2230_);
v_val_2239_ = lean_ctor_get(v_fst_2234_, 0);
lean_inc(v_val_2239_);
lean_dec_ref_known(v_fst_2234_, 1);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_val_2239_);
v___x_2241_ = v___x_2232_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_val_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
v_a_2244_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2229_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2229_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_cmd_2205_);
v_a_2253_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2215_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2215_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object* v___x_2261_, lean_object* v_val_2262_, lean_object* v_cmd_2263_, lean_object* v_onUnsolved_2264_, lean_object* v___y_2265_, lean_object* v_t_2266_, lean_object* v_init_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v_onUnsolved_boxed_2271_; uint8_t v___y_13803__boxed_2272_; lean_object* v_res_2273_; 
v_onUnsolved_boxed_2271_ = lean_unbox(v_onUnsolved_2264_);
v___y_13803__boxed_2272_ = lean_unbox(v___y_2265_);
v_res_2273_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2261_, v_val_2262_, v_cmd_2263_, v_onUnsolved_boxed_2271_, v___y_13803__boxed_2272_, v_t_2266_, v_init_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec_ref(v_t_2266_);
lean_dec_ref(v_val_2262_);
lean_dec_ref(v___x_2261_);
return v_res_2273_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_box(0);
v___x_2275_ = lean_unsigned_to_nat(16u);
v___x_2276_ = lean_mk_array(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v___x_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2283_, lean_object* v_opts_2284_, lean_object* v_tree_2285_, lean_object* v_msgs_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v___y_2291_; uint8_t v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; uint8_t v___y_2295_; uint8_t v___y_2322_; uint8_t v___y_2323_; lean_object* v_acc_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___f_2328_; uint8_t v___y_2330_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___f_2328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2337_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2338_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2284_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2340_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2284_, v___x_2339_);
v___y_2330_ = v___x_2340_;
goto v___jp_2329_;
}
else
{
v___y_2330_ = v___x_2338_;
goto v___jp_2329_;
}
v___jp_2290_:
{
uint8_t v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = 1;
v___x_2297_ = l_Lean_Syntax_getRange_x3f(v_cmd_2283_, v___x_2296_);
if (lean_obj_tag(v___x_2297_) == 1)
{
lean_object* v_val_2298_; lean_object* v_fileMap_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_val_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_val_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v_fileMap_2299_ = lean_ctor_get(v___y_2294_, 1);
v___x_2300_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___y_2291_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v_fileMap_2299_, v_val_2298_, v_cmd_2283_, v___y_2295_, v___y_2292_, v_msgs_2286_, v___x_2301_, v___y_2294_, v___y_2293_);
lean_dec(v_val_2298_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2311_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2311_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2311_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_fst_2307_; lean_object* v___x_2309_; 
v_fst_2307_ = lean_ctor_get(v_a_2303_, 0);
lean_inc(v_fst_2307_);
lean_dec(v_a_2303_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v_fst_2307_);
v___x_2309_ = v___x_2305_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_fst_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
v_a_2312_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2302_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2302_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v___x_2320_; 
lean_dec(v___x_2297_);
lean_dec(v_cmd_2283_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___y_2291_);
return v___x_2320_;
}
}
v___jp_2321_:
{
if (v___y_2323_ == 0)
{
if (v___y_2322_ == 0)
{
lean_object* v___x_2327_; 
lean_dec(v_cmd_2283_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_acc_2324_);
return v___x_2327_;
}
else
{
v___y_2291_ = v_acc_2324_;
v___y_2292_ = v___y_2322_;
v___y_2293_ = v___y_2326_;
v___y_2294_ = v___y_2325_;
v___y_2295_ = v___y_2323_;
goto v___jp_2290_;
}
}
else
{
v___y_2291_ = v_acc_2324_;
v___y_2292_ = v___y_2322_;
v___y_2293_ = v___y_2326_;
v___y_2294_ = v___y_2325_;
v___y_2295_ = v___y_2323_;
goto v___jp_2290_;
}
}
v___jp_2329_:
{
lean_object* v___x_2331_; uint8_t v_onUnsolved_2332_; lean_object* v___x_2333_; uint8_t v_onSorry_2334_; lean_object* v_acc_2335_; 
v___x_2331_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2332_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2284_, v___x_2331_);
v___x_2333_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2334_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2284_, v___x_2333_);
v_acc_2335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2334_ == 0)
{
lean_dec_ref(v_tree_2285_);
v___y_2322_ = v___y_2330_;
v___y_2323_ = v_onUnsolved_2332_;
v_acc_2324_ = v_acc_2335_;
v___y_2325_ = v_a_2287_;
v___y_2326_ = v_a_2288_;
goto v___jp_2321_;
}
else
{
lean_object* v_acc_2336_; 
v_acc_2336_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2328_, v_acc_2335_, v_tree_2285_);
v___y_2322_ = v___y_2330_;
v___y_2323_ = v_onUnsolved_2332_;
v_acc_2324_ = v_acc_2336_;
v___y_2325_ = v_a_2287_;
v___y_2326_ = v_a_2288_;
goto v___jp_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2341_, lean_object* v_opts_2342_, lean_object* v_tree_2343_, lean_object* v_msgs_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2341_, v_opts_2342_, v_tree_2343_, v_msgs_2344_, v_a_2345_, v_a_2346_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec_ref(v_msgs_2344_);
lean_dec_ref(v_opts_2342_);
return v_res_2348_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2349_, lean_object* v_m_2350_, lean_object* v_a_2351_){
_start:
{
uint8_t v___x_2352_; 
v___x_2352_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2350_, v_a_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object* v_00_u03b2_2353_, lean_object* v_m_2354_, lean_object* v_a_2355_){
_start:
{
uint8_t v_res_2356_; lean_object* v_r_2357_; 
v_res_2356_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(v_00_u03b2_2353_, v_m_2354_, v_a_2355_);
lean_dec_ref(v_a_2355_);
lean_dec_ref(v_m_2354_);
v_r_2357_ = lean_box(v_res_2356_);
return v_r_2357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v_00_u03b2_2358_, lean_object* v_m_2359_, lean_object* v_a_2360_, lean_object* v_b_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_2359_, v_a_2360_, v_b_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v___x_2363_, lean_object* v_fst_2364_, lean_object* v_snd_2365_, lean_object* v___x_2366_, lean_object* v_as_2367_, size_t v_sz_2368_, size_t v_i_2369_, lean_object* v_b_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_2363_, v_fst_2364_, v_snd_2365_, v___x_2366_, v_as_2367_, v_sz_2368_, v_i_2369_, v_b_2370_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v___x_2375_, lean_object* v_fst_2376_, lean_object* v_snd_2377_, lean_object* v___x_2378_, lean_object* v_as_2379_, lean_object* v_sz_2380_, lean_object* v_i_2381_, lean_object* v_b_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
size_t v_sz_boxed_2386_; size_t v_i_boxed_2387_; lean_object* v_res_2388_; 
v_sz_boxed_2386_ = lean_unbox_usize(v_sz_2380_);
lean_dec(v_sz_2380_);
v_i_boxed_2387_ = lean_unbox_usize(v_i_2381_);
lean_dec(v_i_2381_);
v_res_2388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2375_, v_fst_2376_, v_snd_2377_, v___x_2378_, v_as_2379_, v_sz_boxed_2386_, v_i_boxed_2387_, v_b_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec_ref(v_as_2379_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(lean_object* v_msgData_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_2389_, v___y_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___boxed(lean_object* v_msgData_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(v_msgData_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2398_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_object* v_00_u03b2_2399_, lean_object* v_a_2400_, lean_object* v_x_2401_){
_start:
{
uint8_t v___x_2402_; 
v___x_2402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_2400_, v_x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2403_, lean_object* v_a_2404_, lean_object* v_x_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(v_00_u03b2_2403_, v_a_2404_, v_x_2405_);
lean_dec(v_x_2405_);
lean_dec_ref(v_a_2404_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3(lean_object* v_00_u03b2_2408_, lean_object* v_data_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_data_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2411_, lean_object* v_i_2412_, lean_object* v_source_2413_, lean_object* v_target_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v_i_2412_, v_source_2413_, v_target_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2416_, lean_object* v_x_2417_, lean_object* v_x_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_x_2417_, v_x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; 
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
v___x_2428_ = lean_apply_7(v_x_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, lean_box(0));
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2438_, lean_object* v_x_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___f_2447_; lean_object* v___x_2448_; 
lean_inc(v___y_2441_);
lean_inc_ref(v___y_2440_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2447_, 0, v_x_2439_);
lean_closure_set(v___f_2447_, 1, v___y_2440_);
lean_closure_set(v___f_2447_, 2, v___y_2441_);
v___x_2448_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2438_, v___f_2447_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2448_) == 0)
{
return v___x_2448_;
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2457_, lean_object* v_x_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2457_, v_x_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2467_, lean_object* v_mvarId_2468_, lean_object* v_x_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2468_, v_x_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2478_, lean_object* v_mvarId_2479_, lean_object* v_x_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2478_, v_mvarId_2479_, v_x_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
return v_res_2530_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2531_, lean_object* v_x_2532_){
_start:
{
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2533_, lean_object* v_x_2534_){
_start:
{
uint8_t v___x_10972__boxed_2535_; uint8_t v_res_2536_; lean_object* v_r_2537_; 
v___x_10972__boxed_2535_ = lean_unbox(v___x_2533_);
v_res_2536_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_10972__boxed_2535_, v_x_2534_);
lean_dec(v_x_2534_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; lean_object* v_env_2545_; uint8_t v___x_2546_; lean_object* v_env_2547_; lean_object* v___x_2548_; lean_object* v_toCold_2549_; lean_object* v_mctx_2550_; lean_object* v_lctx_2551_; lean_object* v_options_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2544_ = lean_st_ref_get(v___y_2542_);
v_env_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_ref(v_env_2545_);
lean_dec(v___x_2544_);
v___x_2546_ = 0;
v_env_2547_ = l_Lean_Environment_setRecordingDeps(v_env_2545_, v___x_2546_);
v___x_2548_ = lean_st_ref_get(v___y_2540_);
v_toCold_2549_ = lean_ctor_get(v___y_2541_, 0);
v_mctx_2550_ = lean_ctor_get(v___x_2548_, 0);
lean_inc_ref(v_mctx_2550_);
lean_dec(v___x_2548_);
v_lctx_2551_ = lean_ctor_get(v___y_2539_, 2);
v_options_2552_ = lean_ctor_get(v_toCold_2549_, 2);
lean_inc_ref(v_options_2552_);
lean_inc_ref(v_lctx_2551_);
v___x_2553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2553_, 0, v_env_2547_);
lean_ctor_set(v___x_2553_, 1, v_mctx_2550_);
lean_ctor_set(v___x_2553_, 2, v_lctx_2551_);
lean_ctor_set(v___x_2553_, 3, v_options_2552_);
v___x_2554_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v_msgData_2538_);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2563_, lean_object* v_msg_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_ref_2570_; lean_object* v___x_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2617_; 
v_ref_2570_ = lean_ctor_get(v___y_2567_, 2);
v___x_2571_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2617_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2617_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v_traceState_2577_; lean_object* v_env_2578_; lean_object* v_nextMacroScope_2579_; lean_object* v_ngen_2580_; lean_object* v_auxDeclNGen_2581_; lean_object* v_cache_2582_; lean_object* v_recordedDeps_2583_; lean_object* v_messages_2584_; lean_object* v_infoState_2585_; lean_object* v_snapshotTasks_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2616_; 
v___x_2576_ = lean_st_ref_take(v___y_2568_);
v_traceState_2577_ = lean_ctor_get(v___x_2576_, 4);
v_env_2578_ = lean_ctor_get(v___x_2576_, 0);
v_nextMacroScope_2579_ = lean_ctor_get(v___x_2576_, 1);
v_ngen_2580_ = lean_ctor_get(v___x_2576_, 2);
v_auxDeclNGen_2581_ = lean_ctor_get(v___x_2576_, 3);
v_cache_2582_ = lean_ctor_get(v___x_2576_, 5);
v_recordedDeps_2583_ = lean_ctor_get(v___x_2576_, 6);
v_messages_2584_ = lean_ctor_get(v___x_2576_, 7);
v_infoState_2585_ = lean_ctor_get(v___x_2576_, 8);
v_snapshotTasks_2586_ = lean_ctor_get(v___x_2576_, 9);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2588_ = v___x_2576_;
v_isShared_2589_ = v_isSharedCheck_2616_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_snapshotTasks_2586_);
lean_inc(v_infoState_2585_);
lean_inc(v_messages_2584_);
lean_inc(v_recordedDeps_2583_);
lean_inc(v_cache_2582_);
lean_inc(v_traceState_2577_);
lean_inc(v_auxDeclNGen_2581_);
lean_inc(v_ngen_2580_);
lean_inc(v_nextMacroScope_2579_);
lean_inc(v_env_2578_);
lean_dec(v___x_2576_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2616_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
uint64_t v_tid_2590_; lean_object* v_traces_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2615_; 
v_tid_2590_ = lean_ctor_get_uint64(v_traceState_2577_, sizeof(void*)*1);
v_traces_2591_ = lean_ctor_get(v_traceState_2577_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_traceState_2577_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2593_ = v_traceState_2577_;
v_isShared_2594_ = v_isSharedCheck_2615_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_traces_2591_);
lean_dec(v_traceState_2577_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2615_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; double v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_box(0);
v___x_2597_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2598_ = 0;
v___x_2599_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2600_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2600_, 0, v_cls_2563_);
lean_ctor_set(v___x_2600_, 1, v___x_2596_);
lean_ctor_set(v___x_2600_, 2, v___x_2599_);
lean_ctor_set_float(v___x_2600_, sizeof(void*)*3, v___x_2597_);
lean_ctor_set_float(v___x_2600_, sizeof(void*)*3 + 8, v___x_2597_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*3 + 16, v___x_2598_);
v___x_2601_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2602_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v_a_2572_);
lean_ctor_set(v___x_2602_, 2, v___x_2601_);
lean_inc(v_ref_2570_);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v_ref_2570_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = l_Lean_PersistentArray_push___redArg(v_traces_2591_, v___x_2603_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2604_);
v___x_2606_ = v___x_2593_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2604_);
lean_ctor_set_uint64(v_reuseFailAlloc_2614_, sizeof(void*)*1, v_tid_2590_);
v___x_2606_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2608_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 4, v___x_2606_);
v___x_2608_ = v___x_2588_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_env_2578_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_nextMacroScope_2579_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_ngen_2580_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_auxDeclNGen_2581_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2613_, 5, v_cache_2582_);
lean_ctor_set(v_reuseFailAlloc_2613_, 6, v_recordedDeps_2583_);
lean_ctor_set(v_reuseFailAlloc_2613_, 7, v_messages_2584_);
lean_ctor_set(v_reuseFailAlloc_2613_, 8, v_infoState_2585_);
lean_ctor_set(v_reuseFailAlloc_2613_, 9, v_snapshotTasks_2586_);
v___x_2608_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2609_ = lean_st_ref_put(v___y_2568_, v___x_2608_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2595_);
v___x_2611_ = v___x_2574_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2595_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2618_, lean_object* v_msg_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2618_, v_msg_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2625_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2629_, lean_object* v___f_2630_, lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; lean_object* v_a_2642_; lean_object* v___y_2646_; lean_object* v___x_2660_; 
v___x_2640_ = lean_st_mk_ref(v___x_2629_);
v___x_2660_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2640_, v___y_2634_, v___y_2636_, v___y_2638_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2662_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2660_, 1);
v___x_2662_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2632_, v___x_2631_, v___x_2640_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; 
lean_dec(v_a_2661_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v___f_2630_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v_a_2642_ = v_a_2663_;
goto v___jp_2641_;
}
else
{
lean_object* v_a_2664_; uint8_t v___x_2665_; 
v_a_2664_ = lean_ctor_get(v___x_2662_, 0);
v___x_2665_ = l_Lean_Exception_isInterrupt(v_a_2664_);
if (v___x_2665_ == 0)
{
uint8_t v___x_2666_; 
lean_inc(v_a_2664_);
v___x_2666_ = l_Lean_Exception_isRuntime(v_a_2664_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2667_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2661_, v___x_2666_, v___x_2640_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2696_; 
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v___x_2667_, 0);
lean_dec(v_unused_2697_);
v___x_2669_ = v___x_2667_;
v_isShared_2670_ = v_isSharedCheck_2696_;
goto v_resetjp_2668_;
}
else
{
lean_dec(v___x_2667_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2696_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
uint8_t v___x_2671_; 
lean_inc(v_a_2664_);
v___x_2671_ = l_Lean_Exception_isMaxRecDepth(v_a_2664_);
if (v___x_2671_ == 0)
{
lean_object* v_toCold_2672_; lean_object* v_options_2673_; uint8_t v_hasTrace_2674_; 
lean_del_object(v___x_2669_);
v_toCold_2672_ = lean_ctor_get(v___y_2637_, 0);
v_options_2673_ = lean_ctor_get(v_toCold_2672_, 2);
v_hasTrace_2674_ = lean_ctor_get_uint8(v_options_2673_, sizeof(void*)*1);
if (v_hasTrace_2674_ == 0)
{
lean_dec(v_a_2664_);
goto v___jp_2657_;
}
else
{
lean_object* v_inheritedTraceOptions_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_inheritedTraceOptions_2675_ = lean_ctor_get(v_toCold_2672_, 11);
v___x_2676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2677_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2675_, v_options_2673_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec(v_a_2664_);
goto v___jp_2657_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2679_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2680_ = l_Lean_Exception_toMessageData(v_a_2664_);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2676_, v___x_2681_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
lean_inc(v___x_2640_);
v___x_2684_ = lean_apply_10(v___f_2630_, v_a_2683_, v___x_2631_, v___x_2640_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, lean_box(0));
v___y_2646_ = v___x_2684_;
goto v___jp_2645_;
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v___x_2640_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v___f_2630_);
v_a_2685_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2682_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2682_);
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
}
}
}
else
{
lean_object* v___x_2694_; 
lean_dec(v___x_2640_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v___f_2630_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
lean_ctor_set(v___x_2669_, 0, v_a_2664_);
v___x_2694_ = v___x_2669_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2664_);
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
lean_dec(v_a_2664_);
lean_dec(v___x_2640_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v___f_2630_);
v_a_2698_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2667_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2667_);
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
lean_dec(v_a_2661_);
lean_dec(v___x_2640_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v___f_2630_);
return v___x_2662_;
}
}
else
{
lean_dec(v_a_2661_);
lean_dec(v___x_2640_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v___f_2630_);
return v___x_2662_;
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v___x_2640_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2632_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v___f_2630_);
v_a_2706_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2660_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2660_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
v___jp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_st_ref_get(v___x_2640_);
lean_dec(v___x_2640_);
lean_dec(v___x_2643_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_a_2642_);
return v___x_2644_;
}
v___jp_2645_:
{
if (lean_obj_tag(v___y_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v_a_2648_; 
v_a_2647_ = lean_ctor_get(v___y_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___y_2646_, 1);
v_a_2648_ = lean_ctor_get(v_a_2647_, 0);
lean_inc(v_a_2648_);
lean_dec(v_a_2647_);
v_a_2642_ = v_a_2648_;
goto v___jp_2641_;
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v___x_2640_);
v_a_2649_ = lean_ctor_get(v___y_2646_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___y_2646_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___y_2646_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___y_2646_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
v___jp_2657_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_box(0);
lean_inc(v___x_2640_);
v___x_2659_ = lean_apply_10(v___f_2630_, v___x_2658_, v___x_2631_, v___x_2640_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, lean_box(0));
v___y_2646_ = v___x_2659_;
goto v___jp_2645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2714_, lean_object* v___f_2715_, lean_object* v___x_2716_, lean_object* v___x_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2714_, v___f_2715_, v___x_2716_, v___x_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2726_, uint8_t v___x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2726_, v___x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2736_, lean_object* v___x_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
uint8_t v___x_11291__boxed_2745_; lean_object* v_res_2746_; 
v___x_11291__boxed_2745_ = lean_unbox(v___x_2737_);
v_res_2746_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2736_, v___x_11291__boxed_2745_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2747_, lean_object* v_msg_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_ref_2754_; lean_object* v___x_2755_; lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2801_; 
v_ref_2754_ = lean_ctor_get(v___y_2751_, 2);
v___x_2755_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2801_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2801_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v_traceState_2761_; lean_object* v_env_2762_; lean_object* v_nextMacroScope_2763_; lean_object* v_ngen_2764_; lean_object* v_auxDeclNGen_2765_; lean_object* v_cache_2766_; lean_object* v_recordedDeps_2767_; lean_object* v_messages_2768_; lean_object* v_infoState_2769_; lean_object* v_snapshotTasks_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2800_; 
v___x_2760_ = lean_st_ref_take(v___y_2752_);
v_traceState_2761_ = lean_ctor_get(v___x_2760_, 4);
v_env_2762_ = lean_ctor_get(v___x_2760_, 0);
v_nextMacroScope_2763_ = lean_ctor_get(v___x_2760_, 1);
v_ngen_2764_ = lean_ctor_get(v___x_2760_, 2);
v_auxDeclNGen_2765_ = lean_ctor_get(v___x_2760_, 3);
v_cache_2766_ = lean_ctor_get(v___x_2760_, 5);
v_recordedDeps_2767_ = lean_ctor_get(v___x_2760_, 6);
v_messages_2768_ = lean_ctor_get(v___x_2760_, 7);
v_infoState_2769_ = lean_ctor_get(v___x_2760_, 8);
v_snapshotTasks_2770_ = lean_ctor_get(v___x_2760_, 9);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2772_ = v___x_2760_;
v_isShared_2773_ = v_isSharedCheck_2800_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_snapshotTasks_2770_);
lean_inc(v_infoState_2769_);
lean_inc(v_messages_2768_);
lean_inc(v_recordedDeps_2767_);
lean_inc(v_cache_2766_);
lean_inc(v_traceState_2761_);
lean_inc(v_auxDeclNGen_2765_);
lean_inc(v_ngen_2764_);
lean_inc(v_nextMacroScope_2763_);
lean_inc(v_env_2762_);
lean_dec(v___x_2760_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2800_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
uint64_t v_tid_2774_; lean_object* v_traces_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2799_; 
v_tid_2774_ = lean_ctor_get_uint64(v_traceState_2761_, sizeof(void*)*1);
v_traces_2775_ = lean_ctor_get(v_traceState_2761_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_traceState_2761_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2777_ = v_traceState_2761_;
v_isShared_2778_ = v_isSharedCheck_2799_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_traces_2775_);
lean_dec(v_traceState_2761_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2799_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; double v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2779_ = lean_box(0);
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2782_ = 0;
v___x_2783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2784_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2784_, 0, v_cls_2747_);
lean_ctor_set(v___x_2784_, 1, v___x_2780_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
lean_ctor_set_float(v___x_2784_, sizeof(void*)*3, v___x_2781_);
lean_ctor_set_float(v___x_2784_, sizeof(void*)*3 + 8, v___x_2781_);
lean_ctor_set_uint8(v___x_2784_, sizeof(void*)*3 + 16, v___x_2782_);
v___x_2785_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2786_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v_a_2756_);
lean_ctor_set(v___x_2786_, 2, v___x_2785_);
lean_inc(v_ref_2754_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v_ref_2754_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = l_Lean_PersistentArray_push___redArg(v_traces_2775_, v___x_2787_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2788_);
v___x_2790_ = v___x_2777_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2788_);
lean_ctor_set_uint64(v_reuseFailAlloc_2798_, sizeof(void*)*1, v_tid_2774_);
v___x_2790_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2792_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 4, v___x_2790_);
v___x_2792_ = v___x_2772_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_env_2762_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_nextMacroScope_2763_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_ngen_2764_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_auxDeclNGen_2765_);
lean_ctor_set(v_reuseFailAlloc_2797_, 4, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2797_, 5, v_cache_2766_);
lean_ctor_set(v_reuseFailAlloc_2797_, 6, v_recordedDeps_2767_);
lean_ctor_set(v_reuseFailAlloc_2797_, 7, v_messages_2768_);
lean_ctor_set(v_reuseFailAlloc_2797_, 8, v_infoState_2769_);
lean_ctor_set(v_reuseFailAlloc_2797_, 9, v_snapshotTasks_2770_);
v___x_2792_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2793_ = lean_st_ref_put(v___y_2752_, v___x_2792_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2779_);
v___x_2795_ = v___x_2758_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2779_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v___f_2813_, lean_object* v_term_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___y_2823_; lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2814_, v___x_2815_, v___x_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2813_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2853_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2853_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v_fst_2849_; lean_object* v___x_2851_; 
v_fst_2849_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_fst_2849_);
lean_dec(v_a_2845_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v_fst_2849_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_fst_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2891_; 
v_a_2854_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2856_ = v___x_2844_;
v_isShared_2857_ = v_isSharedCheck_2891_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2844_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2891_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
uint8_t v___x_2858_; 
v___x_2858_ = l_Lean_Exception_isInterrupt(v_a_2854_);
if (v___x_2858_ == 0)
{
uint8_t v___x_2859_; 
lean_inc(v_a_2854_);
v___x_2859_ = l_Lean_Exception_isRuntime(v_a_2854_);
if (v___x_2859_ == 0)
{
uint8_t v___x_2860_; 
lean_inc(v_a_2854_);
v___x_2860_ = l_Lean_Exception_isMaxRecDepth(v_a_2854_);
if (v___x_2860_ == 0)
{
lean_object* v_toCold_2861_; lean_object* v_options_2862_; uint8_t v_hasTrace_2863_; 
lean_del_object(v___x_2856_);
v_toCold_2861_ = lean_ctor_get(v___y_2819_, 0);
v_options_2862_ = lean_ctor_get(v_toCold_2861_, 2);
v_hasTrace_2863_ = lean_ctor_get_uint8(v_options_2862_, sizeof(void*)*1);
if (v_hasTrace_2863_ == 0)
{
lean_dec(v_a_2854_);
goto v___jp_2841_;
}
else
{
lean_object* v_inheritedTraceOptions_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v_inheritedTraceOptions_2864_ = lean_ctor_get(v_toCold_2861_, 11);
v___x_2865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2866_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2864_, v_options_2862_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_dec(v_a_2854_);
goto v___jp_2841_;
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2868_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2869_ = l_Lean_Exception_toMessageData(v_a_2854_);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2865_, v___x_2870_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_apply_6(v___f_2813_, v_a_2872_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, lean_box(0));
v___y_2823_ = v___x_2873_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2813_);
v_a_2874_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2871_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2871_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
}
else
{
lean_object* v___x_2883_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2813_);
if (v_isShared_2857_ == 0)
{
v___x_2883_ = v___x_2856_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2854_);
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
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2813_);
if (v_isShared_2857_ == 0)
{
v___x_2886_ = v___x_2856_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2854_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
else
{
lean_object* v___x_2889_; 
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___f_2813_);
if (v_isShared_2857_ == 0)
{
v___x_2889_ = v___x_2856_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2854_);
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
v___jp_2841_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_apply_6(v___f_2813_, v___x_2842_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, lean_box(0));
v___y_2823_ = v___x_2843_;
goto v___jp_2822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v___f_2892_, lean_object* v_term_2893_, lean_object* v___x_2894_, lean_object* v___x_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v___f_2892_, v_term_2893_, v___x_2894_, v___x_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2902_, lean_object* v_vals_2903_, lean_object* v_i_2904_, lean_object* v_k_2905_){
_start:
{
lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2906_ = lean_array_get_size(v_keys_2902_);
v___x_2907_ = lean_nat_dec_lt(v_i_2904_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; 
lean_dec(v_i_2904_);
v___x_2908_ = lean_box(0);
return v___x_2908_;
}
else
{
lean_object* v_k_x27_2909_; uint8_t v___x_2910_; 
v_k_x27_2909_ = lean_array_fget_borrowed(v_keys_2902_, v_i_2904_);
v___x_2910_ = l_Lean_instBEqMVarId_beq(v_k_2905_, v_k_x27_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_unsigned_to_nat(1u);
v___x_2912_ = lean_nat_add(v_i_2904_, v___x_2911_);
lean_dec(v_i_2904_);
v_i_2904_ = v___x_2912_;
goto _start;
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_array_fget_borrowed(v_vals_2903_, v_i_2904_);
lean_dec(v_i_2904_);
lean_inc(v___x_2914_);
v___x_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2916_, lean_object* v_vals_2917_, lean_object* v_i_2918_, lean_object* v_k_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2916_, v_vals_2917_, v_i_2918_, v_k_2919_);
lean_dec(v_k_2919_);
lean_dec_ref(v_vals_2917_);
lean_dec_ref(v_keys_2916_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2921_, size_t v_x_2922_, lean_object* v_x_2923_){
_start:
{
if (lean_obj_tag(v_x_2921_) == 0)
{
lean_object* v_es_2924_; lean_object* v___x_2925_; size_t v___x_2926_; size_t v___x_2927_; lean_object* v_j_2928_; lean_object* v___x_2929_; 
v_es_2924_ = lean_ctor_get(v_x_2921_, 0);
v___x_2925_ = lean_box(2);
v___x_2926_ = ((size_t)31ULL);
v___x_2927_ = lean_usize_land(v_x_2922_, v___x_2926_);
v_j_2928_ = lean_usize_to_nat(v___x_2927_);
v___x_2929_ = lean_array_get_borrowed(v___x_2925_, v_es_2924_, v_j_2928_);
lean_dec(v_j_2928_);
switch(lean_obj_tag(v___x_2929_))
{
case 0:
{
lean_object* v_key_2930_; lean_object* v_val_2931_; uint8_t v___x_2932_; 
v_key_2930_ = lean_ctor_get(v___x_2929_, 0);
v_val_2931_ = lean_ctor_get(v___x_2929_, 1);
v___x_2932_ = l_Lean_instBEqMVarId_beq(v_x_2923_, v_key_2930_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_box(0);
return v___x_2933_;
}
else
{
lean_object* v___x_2934_; 
lean_inc(v_val_2931_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_val_2931_);
return v___x_2934_;
}
}
case 1:
{
lean_object* v_node_2935_; size_t v___x_2936_; size_t v___x_2937_; 
v_node_2935_ = lean_ctor_get(v___x_2929_, 0);
v___x_2936_ = ((size_t)5ULL);
v___x_2937_ = lean_usize_shift_right(v_x_2922_, v___x_2936_);
v_x_2921_ = v_node_2935_;
v_x_2922_ = v___x_2937_;
goto _start;
}
default: 
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_box(0);
return v___x_2939_;
}
}
}
else
{
lean_object* v_ks_2940_; lean_object* v_vs_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_ks_2940_ = lean_ctor_get(v_x_2921_, 0);
v_vs_2941_ = lean_ctor_get(v_x_2921_, 1);
v___x_2942_ = lean_unsigned_to_nat(0u);
v___x_2943_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2940_, v_vs_2941_, v___x_2942_, v_x_2923_);
return v___x_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_){
_start:
{
size_t v_x_11604__boxed_2947_; lean_object* v_res_2948_; 
v_x_11604__boxed_2947_ = lean_unbox_usize(v_x_2945_);
lean_dec(v_x_2945_);
v_res_2948_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2944_, v_x_11604__boxed_2947_, v_x_2946_);
lean_dec(v_x_2946_);
lean_dec_ref(v_x_2944_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2949_, lean_object* v_x_2950_){
_start:
{
uint64_t v___x_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = l_Lean_instHashableMVarId_hash(v_x_2950_);
v___x_2952_ = lean_uint64_to_usize(v___x_2951_);
v___x_2953_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2949_, v___x_2952_, v_x_2950_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2954_, v_x_2955_);
lean_dec(v_x_2955_);
lean_dec_ref(v_x_2954_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v_mctx_2986_; lean_object* v_env_2987_; lean_object* v_opts_2988_; lean_object* v_namingCtx_2989_; lean_object* v_goal_2990_; lean_object* v_decls_2991_; lean_object* v___x_2992_; 
v_mctx_2986_ = lean_ctor_get(v_c_2982_, 3);
lean_inc_ref(v_mctx_2986_);
v_env_2987_ = lean_ctor_get(v_c_2982_, 2);
lean_inc_ref(v_env_2987_);
v_opts_2988_ = lean_ctor_get(v_c_2982_, 4);
lean_inc_ref(v_opts_2988_);
v_namingCtx_2989_ = lean_ctor_get(v_c_2982_, 5);
lean_inc_ref(v_namingCtx_2989_);
v_goal_2990_ = lean_ctor_get(v_c_2982_, 6);
lean_inc(v_goal_2990_);
lean_dec_ref(v_c_2982_);
v_decls_2991_ = lean_ctor_get(v_mctx_2986_, 5);
v___x_2992_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_2991_, v_goal_2990_);
if (lean_obj_tag(v___x_2992_) == 1)
{
lean_object* v_val_2993_; lean_object* v_lctx_2994_; lean_object* v___f_2995_; lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; lean_object* v_term_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___f_3008_; lean_object* v___x_3009_; 
v_val_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_val_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v_lctx_2994_ = lean_ctor_get(v_val_2993_, 1);
lean_inc_ref(v_lctx_2994_);
lean_dec(v_val_2993_);
v___f_2995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_2996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_2997_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_2998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_2999_ = lean_box(0);
lean_inc(v_goal_2990_);
v___x_3000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3000_, 0, v_goal_2990_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___f_3001_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3001_, 0, v___x_3000_);
lean_closure_set(v___f_3001_, 1, v___f_2995_);
lean_closure_set(v___f_3001_, 2, v___x_2998_);
lean_closure_set(v___f_3001_, 3, v___x_2997_);
v___x_3002_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_3002_, 0, lean_box(0));
lean_closure_set(v___x_3002_, 1, v_goal_2990_);
lean_closure_set(v___x_3002_, 2, v___f_3001_);
v___x_3003_ = 1;
v___x_3004_ = lean_box(v___x_3003_);
v_term_3005_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3005_, 0, v___x_3002_);
lean_closure_set(v_term_3005_, 1, v___x_3004_);
v___x_3006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3008_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3008_, 0, v___f_2996_);
lean_closure_set(v___f_3008_, 1, v_term_3005_);
lean_closure_set(v___f_3008_, 2, v___x_3006_);
lean_closure_set(v___f_3008_, 3, v___x_3007_);
v___x_3009_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2987_, v_mctx_2986_, v_lctx_2994_, v_opts_2988_, v_namingCtx_2989_, v___f_3008_, v_a_2983_, v_a_2984_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_dec(v___x_2992_);
lean_dec(v_goal_2990_);
lean_dec_ref(v_namingCtx_2989_);
lean_dec_ref(v_opts_2988_);
lean_dec_ref(v_env_2987_);
lean_dec_ref(v_mctx_2986_);
v___x_3010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
return v___x_3011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3012_, v_a_3013_, v_a_3014_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3018_, v_x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3021_, lean_object* v_x_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3021_, v_x_3022_, v_x_3023_);
lean_dec(v_x_3023_);
lean_dec_ref(v_x_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3025_, lean_object* v_msg_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3025_, v_msg_3026_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3037_, lean_object* v_msg_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3037_, v_msg_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3049_, lean_object* v_x_3050_, size_t v_x_3051_, lean_object* v_x_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3050_, v_x_3051_, v_x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3054_, lean_object* v_x_3055_, lean_object* v_x_3056_, lean_object* v_x_3057_){
_start:
{
size_t v_x_11861__boxed_3058_; lean_object* v_res_3059_; 
v_x_11861__boxed_3058_ = lean_unbox_usize(v_x_3056_);
lean_dec(v_x_3056_);
v_res_3059_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3054_, v_x_3055_, v_x_11861__boxed_3058_, v_x_3057_);
lean_dec(v_x_3057_);
lean_dec_ref(v_x_3055_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3060_, lean_object* v_keys_3061_, lean_object* v_vals_3062_, lean_object* v_heq_3063_, lean_object* v_i_3064_, lean_object* v_k_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3061_, v_vals_3062_, v_i_3064_, v_k_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3067_, lean_object* v_keys_3068_, lean_object* v_vals_3069_, lean_object* v_heq_3070_, lean_object* v_i_3071_, lean_object* v_k_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3067_, v_keys_3068_, v_vals_3069_, v_heq_3070_, v_i_3071_, v_k_3072_);
lean_dec(v_k_3072_);
lean_dec_ref(v_vals_3069_);
lean_dec_ref(v_keys_3068_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3076_, lean_object* v___x_3077_, lean_object* v_ref_3078_, lean_object* v_a_3079_, lean_object* v___x_3080_, lean_object* v___x_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
if (v___x_3076_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3077_);
v___x_3086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3087_ = lean_box(0);
v___x_3088_ = 4;
v___x_3089_ = l_Lean_MessageData_nil;
v___x_3090_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3078_, v_a_3079_, v___x_3085_, v___x_3086_, v___x_3087_, v___x_3088_, v___x_3089_, v___y_3082_, v___y_3083_);
return v___x_3090_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3091_ = lean_array_get(v___x_3080_, v_a_3079_, v___x_3081_);
lean_dec_ref(v_a_3079_);
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3077_);
v___x_3093_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3094_ = lean_box(0);
v___x_3095_ = 4;
v___x_3096_ = l_Lean_MessageData_nil;
v___x_3097_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3078_, v___x_3091_, v___x_3092_, v___x_3093_, v___x_3094_, v___x_3095_, v___x_3096_, v___y_3082_, v___y_3083_);
return v___x_3097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3098_, lean_object* v___x_3099_, lean_object* v_ref_3100_, lean_object* v_a_3101_, lean_object* v___x_3102_, lean_object* v___x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
uint8_t v___x_3507__boxed_3107_; lean_object* v_res_3108_; 
v___x_3507__boxed_3107_ = lean_unbox(v___x_3098_);
v_res_3108_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3507__boxed_3107_, v___x_3099_, v_ref_3100_, v_a_3101_, v___x_3102_, v___x_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___x_3103_);
lean_dec_ref(v___x_3102_);
return v_res_3108_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3109_, lean_object* v_x_3110_){
_start:
{
if (lean_obj_tag(v_x_3110_) == 1)
{
lean_object* v_pre_3111_; 
v_pre_3111_ = lean_ctor_get(v_x_3110_, 0);
if (lean_obj_tag(v_pre_3111_) == 0)
{
lean_object* v_str_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_str_3112_ = lean_ctor_get(v_x_3110_, 1);
v___x_3113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1));
v___x_3114_ = lean_string_dec_eq(v_str_3112_, v___x_3113_);
if (v___x_3114_ == 0)
{
return v___x_3114_;
}
else
{
return v_suppressElabErrors_3109_;
}
}
else
{
uint8_t v___x_3115_; 
v___x_3115_ = 0;
return v___x_3115_;
}
}
else
{
uint8_t v___x_3116_; 
v___x_3116_ = 0;
return v___x_3116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3117_, lean_object* v_x_3118_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3119_; uint8_t v_res_3120_; lean_object* v_r_3121_; 
v_suppressElabErrors_boxed_3119_ = lean_unbox(v_suppressElabErrors_3117_);
v_res_3120_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3119_, v_x_3118_);
lean_dec(v_x_3118_);
v_r_3121_ = lean_box(v_res_3120_);
return v_r_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3122_, lean_object* v_msgData_3123_, uint8_t v_severity_3124_, uint8_t v_isSilent_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; uint8_t v___y_3133_; lean_object* v___y_3134_; uint8_t v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; uint8_t v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3221_; uint8_t v___y_3222_; uint8_t v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3228_; uint8_t v___y_3229_; uint8_t v___x_3244_; uint8_t v___y_3246_; uint8_t v___x_3256_; 
v___x_3244_ = 2;
v___x_3256_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3124_, v___x_3244_);
if (v___x_3256_ == 0)
{
v___y_3246_ = v___x_3256_;
goto v___jp_3245_;
}
else
{
uint8_t v___x_3257_; 
lean_inc_ref(v_msgData_3123_);
v___x_3257_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3123_);
if (v___x_3257_ == 0)
{
v___y_3246_ = v___x_3257_;
goto v___jp_3245_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec_ref(v_msgData_3123_);
v___x_3258_ = lean_box(0);
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
return v___x_3259_;
}
}
v___jp_3129_:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_Elab_Command_getScope___redArg(v___y_3137_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v_currNamespace_3140_; lean_object* v___x_3141_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3138_, 1);
v_currNamespace_3140_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_currNamespace_3140_);
lean_dec(v_a_3139_);
v___x_3141_ = l_Lean_Elab_Command_getScope___redArg(v___y_3137_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3177_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3177_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3177_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v_openDecls_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v_env_3151_; lean_object* v_messages_3152_; lean_object* v_scopes_3153_; lean_object* v_usedQuotCtxts_3154_; lean_object* v_nextMacroScope_3155_; lean_object* v_maxRecDepth_3156_; lean_object* v_ngen_3157_; lean_object* v_auxDeclNGen_3158_; lean_object* v_infoState_3159_; lean_object* v_traceState_3160_; lean_object* v_snapshotTasks_3161_; lean_object* v_prevLinterStates_3162_; lean_object* v_codeQualityEntryTasks_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3176_; 
v_openDecls_3146_ = lean_ctor_get(v_a_3142_, 3);
lean_inc(v_openDecls_3146_);
lean_dec(v_a_3142_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_currNamespace_3140_);
lean_ctor_set(v___x_3147_, 1, v_openDecls_3146_);
v___x_3148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___y_3130_);
lean_inc_ref(v___y_3132_);
lean_inc_ref(v___y_3131_);
v___x_3149_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3149_, 0, v___y_3131_);
lean_ctor_set(v___x_3149_, 1, v___y_3134_);
lean_ctor_set(v___x_3149_, 2, v___y_3136_);
lean_ctor_set(v___x_3149_, 3, v___y_3132_);
lean_ctor_set(v___x_3149_, 4, v___x_3148_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*5, v___y_3135_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*5 + 1, v___y_3133_);
lean_ctor_set_uint8(v___x_3149_, sizeof(void*)*5 + 2, v_isSilent_3125_);
v___x_3150_ = lean_st_ref_take(v___y_3137_);
v_env_3151_ = lean_ctor_get(v___x_3150_, 0);
v_messages_3152_ = lean_ctor_get(v___x_3150_, 1);
v_scopes_3153_ = lean_ctor_get(v___x_3150_, 2);
v_usedQuotCtxts_3154_ = lean_ctor_get(v___x_3150_, 3);
v_nextMacroScope_3155_ = lean_ctor_get(v___x_3150_, 4);
v_maxRecDepth_3156_ = lean_ctor_get(v___x_3150_, 5);
v_ngen_3157_ = lean_ctor_get(v___x_3150_, 6);
v_auxDeclNGen_3158_ = lean_ctor_get(v___x_3150_, 7);
v_infoState_3159_ = lean_ctor_get(v___x_3150_, 8);
v_traceState_3160_ = lean_ctor_get(v___x_3150_, 9);
v_snapshotTasks_3161_ = lean_ctor_get(v___x_3150_, 10);
v_prevLinterStates_3162_ = lean_ctor_get(v___x_3150_, 11);
v_codeQualityEntryTasks_3163_ = lean_ctor_get(v___x_3150_, 12);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3165_ = v___x_3150_;
v_isShared_3166_ = v_isSharedCheck_3176_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3163_);
lean_inc(v_prevLinterStates_3162_);
lean_inc(v_snapshotTasks_3161_);
lean_inc(v_traceState_3160_);
lean_inc(v_infoState_3159_);
lean_inc(v_auxDeclNGen_3158_);
lean_inc(v_ngen_3157_);
lean_inc(v_maxRecDepth_3156_);
lean_inc(v_nextMacroScope_3155_);
lean_inc(v_usedQuotCtxts_3154_);
lean_inc(v_scopes_3153_);
lean_inc(v_messages_3152_);
lean_inc(v_env_3151_);
lean_dec(v___x_3150_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3176_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3167_ = lean_box(0);
v___x_3168_ = l_Lean_MessageLog_add(v___x_3149_, v_messages_3152_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 1, v___x_3168_);
v___x_3170_ = v___x_3165_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_env_3151_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_scopes_3153_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_usedQuotCtxts_3154_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_nextMacroScope_3155_);
lean_ctor_set(v_reuseFailAlloc_3175_, 5, v_maxRecDepth_3156_);
lean_ctor_set(v_reuseFailAlloc_3175_, 6, v_ngen_3157_);
lean_ctor_set(v_reuseFailAlloc_3175_, 7, v_auxDeclNGen_3158_);
lean_ctor_set(v_reuseFailAlloc_3175_, 8, v_infoState_3159_);
lean_ctor_set(v_reuseFailAlloc_3175_, 9, v_traceState_3160_);
lean_ctor_set(v_reuseFailAlloc_3175_, 10, v_snapshotTasks_3161_);
lean_ctor_set(v_reuseFailAlloc_3175_, 11, v_prevLinterStates_3162_);
lean_ctor_set(v_reuseFailAlloc_3175_, 12, v_codeQualityEntryTasks_3163_);
v___x_3170_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3171_ = lean_st_ref_put(v___y_3137_, v___x_3170_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3167_);
v___x_3173_ = v___x_3144_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3167_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_currNamespace_3140_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3134_);
lean_dec_ref(v___y_3130_);
v_a_3178_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3141_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3141_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3134_);
lean_dec_ref(v___y_3130_);
v_a_3186_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3138_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3138_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
v___jp_3194_:
{
lean_object* v_fileName_3199_; lean_object* v_fileMap_3200_; uint8_t v_suppressElabErrors_3201_; lean_object* v___x_3202_; lean_object* v___f_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3219_; 
v_fileName_3199_ = lean_ctor_get(v___y_3126_, 0);
v_fileMap_3200_ = lean_ctor_get(v___y_3126_, 1);
v_suppressElabErrors_3201_ = lean_ctor_get_uint8(v___y_3126_, sizeof(void*)*10);
v___x_3202_ = lean_box(v_suppressElabErrors_3201_);
v___f_3203_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3203_, 0, v___x_3202_);
v___x_3204_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3123_);
v___x_3205_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v___x_3204_, v___y_3127_);
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3219_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3219_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_inc_ref_n(v_fileMap_3200_, 2);
v___x_3210_ = l_Lean_FileMap_toPosition(v_fileMap_3200_, v___y_3196_);
lean_dec(v___y_3196_);
v___x_3211_ = l_Lean_FileMap_toPosition(v_fileMap_3200_, v___y_3198_);
lean_dec(v___y_3198_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___x_3213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3201_ == 0)
{
lean_del_object(v___x_3208_);
lean_dec_ref(v___f_3203_);
v___y_3130_ = v_a_3206_;
v___y_3131_ = v_fileName_3199_;
v___y_3132_ = v___x_3213_;
v___y_3133_ = v___y_3195_;
v___y_3134_ = v___x_3210_;
v___y_3135_ = v___y_3197_;
v___y_3136_ = v___x_3212_;
v___y_3137_ = v___y_3127_;
goto v___jp_3129_;
}
else
{
uint8_t v___x_3214_; 
lean_inc(v_a_3206_);
v___x_3214_ = l_Lean_MessageData_hasTag(v___f_3203_, v_a_3206_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
lean_dec_ref_known(v___x_3212_, 1);
lean_dec_ref(v___x_3210_);
lean_dec(v_a_3206_);
v___x_3215_ = lean_box(0);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3215_);
v___x_3217_ = v___x_3208_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
else
{
lean_del_object(v___x_3208_);
v___y_3130_ = v_a_3206_;
v___y_3131_ = v_fileName_3199_;
v___y_3132_ = v___x_3213_;
v___y_3133_ = v___y_3195_;
v___y_3134_ = v___x_3210_;
v___y_3135_ = v___y_3197_;
v___y_3136_ = v___x_3212_;
v___y_3137_ = v___y_3127_;
goto v___jp_3129_;
}
}
}
}
v___jp_3220_:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Syntax_getTailPos_x3f(v___y_3221_, v___y_3223_);
lean_dec(v___y_3221_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_inc(v___y_3224_);
v___y_3195_ = v___y_3222_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v___y_3224_;
goto v___jp_3194_;
}
else
{
lean_object* v_val_3226_; 
v_val_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_val_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v___y_3195_ = v___y_3222_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v_val_3226_;
goto v___jp_3194_;
}
}
v___jp_3227_:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Elab_Command_getRef___redArg(v___y_3126_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v_ref_3232_; lean_object* v___x_3233_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v_ref_3232_ = l_Lean_replaceRef(v_ref_3122_, v_a_3231_);
lean_dec(v_a_3231_);
v___x_3233_ = l_Lean_Syntax_getPos_x3f(v_ref_3232_, v___y_3228_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_unsigned_to_nat(0u);
v___y_3221_ = v_ref_3232_;
v___y_3222_ = v___y_3229_;
v___y_3223_ = v___y_3228_;
v___y_3224_ = v___x_3234_;
goto v___jp_3220_;
}
else
{
lean_object* v_val_3235_; 
v_val_3235_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_val_3235_);
lean_dec_ref_known(v___x_3233_, 1);
v___y_3221_ = v_ref_3232_;
v___y_3222_ = v___y_3229_;
v___y_3223_ = v___y_3228_;
v___y_3224_ = v_val_3235_;
goto v___jp_3220_;
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v_msgData_3123_);
v_a_3236_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3230_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3230_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
v___jp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v_scopes_3249_; lean_object* v___x_3250_; lean_object* v_opts_3251_; uint8_t v___x_3252_; uint8_t v___x_3253_; 
v___x_3247_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3248_ = lean_st_ref_get(v___y_3127_);
v_scopes_3249_ = lean_ctor_get(v___x_3248_, 2);
lean_inc(v_scopes_3249_);
lean_dec(v___x_3248_);
v___x_3250_ = l_List_head_x21___redArg(v___x_3247_, v_scopes_3249_);
lean_dec(v_scopes_3249_);
v_opts_3251_ = lean_ctor_get(v___x_3250_, 1);
lean_inc_ref(v_opts_3251_);
lean_dec(v___x_3250_);
v___x_3252_ = 1;
v___x_3253_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3124_, v___x_3252_);
if (v___x_3253_ == 0)
{
lean_dec_ref(v_opts_3251_);
v___y_3228_ = v___y_3246_;
v___y_3229_ = v_severity_3124_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = l_Lean_warningAsError;
v___x_3255_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3251_, v___x_3254_);
lean_dec_ref(v_opts_3251_);
if (v___x_3255_ == 0)
{
v___y_3228_ = v___y_3246_;
v___y_3229_ = v_severity_3124_;
goto v___jp_3227_;
}
else
{
v___y_3228_ = v___y_3246_;
v___y_3229_ = v___x_3244_;
goto v___jp_3227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3260_, lean_object* v_msgData_3261_, lean_object* v_severity_3262_, lean_object* v_isSilent_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
uint8_t v_severity_boxed_3267_; uint8_t v_isSilent_boxed_3268_; lean_object* v_res_3269_; 
v_severity_boxed_3267_ = lean_unbox(v_severity_3262_);
v_isSilent_boxed_3268_ = lean_unbox(v_isSilent_3263_);
v_res_3269_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3260_, v_msgData_3261_, v_severity_boxed_3267_, v_isSilent_boxed_3268_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v_ref_3260_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3270_, lean_object* v_msgData_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v___x_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = 0;
v___x_3276_ = 0;
v___x_3277_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3270_, v_msgData_3271_, v___x_3275_, v___x_3276_, v___y_3272_, v___y_3273_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3278_, lean_object* v_msgData_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3278_, v_msgData_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v_ref_3278_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3288_ = lean_string_append(v___x_3287_, v___x_3285_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3289_, v_x_3290_);
lean_dec_ref(v_x_3290_);
lean_dec_ref(v___x_3289_);
return v_res_3291_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3294_ = l_Lean_stringToMessageData(v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3297_ = l_Lean_stringToMessageData(v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3300_ = l_Lean_stringToMessageData(v___x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3301_, uint8_t v___x_3302_, lean_object* v___x_3303_, lean_object* v_insertPos_3304_, lean_object* v_cmdLine_3305_, lean_object* v_ref_3306_, size_t v_sz_3307_, size_t v_i_3308_, lean_object* v_bs_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
uint8_t v___x_3313_; 
v___x_3313_ = lean_usize_dec_lt(v_i_3308_, v_sz_3307_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3301_);
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_bs_3309_);
return v___x_3314_;
}
else
{
lean_object* v_v_3315_; lean_object* v___x_3316_; lean_object* v_bs_x27_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_v_3315_ = lean_array_uget(v_bs_3309_, v_i_3308_);
v___x_3316_ = lean_unsigned_to_nat(0u);
v_bs_x27_3317_ = lean_array_uset(v_bs_3309_, v_i_3308_, v___x_3316_);
lean_inc(v_v_3315_);
v___x_3318_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3318_, 0, v_v_3315_);
v___x_3319_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3318_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___f_3323_; lean_object* v___x_3324_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v___x_3321_ = l_Std_Format_defWidth;
v___x_3322_ = l_Std_Format_pretty(v_a_3320_, v___x_3321_, v___x_3316_, v___x_3316_);
lean_inc_ref(v___x_3322_);
v___f_3323_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3323_, 0, v___x_3322_);
lean_inc_ref(v___x_3301_);
v___x_3324_ = lean_string_append(v___x_3301_, v___x_3322_);
lean_dec_ref(v___x_3322_);
if (v___x_3302_ == 0)
{
goto v___jp_3325_;
}
else
{
lean_object* v___x_3336_; lean_object* v_line_3337_; lean_object* v_column_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3373_; 
lean_inc_ref(v___x_3303_);
v___x_3336_ = l_Lean_FileMap_toPosition(v___x_3303_, v_insertPos_3304_);
v_line_3337_ = lean_ctor_get(v___x_3336_, 0);
v_column_3338_ = lean_ctor_get(v___x_3336_, 1);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3340_ = v___x_3336_;
v_isShared_3341_ = v_isSharedCheck_3373_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_column_3338_);
lean_inc(v_line_3337_);
lean_dec(v___x_3336_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3373_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3342_ = lean_nat_sub(v_line_3337_, v_cmdLine_3305_);
lean_dec(v_line_3337_);
v___x_3343_ = lean_unsigned_to_nat(1u);
v___x_3344_ = lean_nat_add(v___x_3342_, v___x_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3324_);
v___x_3346_ = l_String_quote(v___x_3324_);
v___x_3347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
v___x_3348_ = l_Lean_MessageData_ofFormat(v___x_3347_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 7);
lean_ctor_set(v___x_3340_, 1, v___x_3348_);
lean_ctor_set(v___x_3340_, 0, v___x_3345_);
v___x_3350_ = v___x_3340_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v___x_3348_);
v___x_3350_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3351_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = l_Nat_reprFast(v___x_3344_);
v___x_3354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
v___x_3355_ = l_Lean_MessageData_ofFormat(v___x_3354_);
v___x_3356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3352_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = l_Nat_reprFast(v_column_3338_);
v___x_3360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
v___x_3361_ = l_Lean_MessageData_ofFormat(v___x_3360_);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3358_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3306_, v___x_3362_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_dec_ref_known(v___x_3363_, 1);
goto v___jp_3325_;
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec_ref(v___x_3324_);
lean_dec_ref(v___f_3323_);
lean_dec_ref(v_bs_x27_3317_);
lean_dec(v_v_3315_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3301_);
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
}
v___jp_3325_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; size_t v___x_3332_; size_t v___x_3333_; lean_object* v___x_3334_; 
v___x_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
v___x_3327_ = lean_box(0);
v___x_3328_ = l_Lean_MessageData_ofSyntax(v_v_3315_);
v___x_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___f_3323_);
v___x_3331_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3326_);
lean_ctor_set(v___x_3331_, 1, v___x_3327_);
lean_ctor_set(v___x_3331_, 2, v___x_3327_);
lean_ctor_set(v___x_3331_, 3, v___x_3327_);
lean_ctor_set(v___x_3331_, 4, v___x_3329_);
lean_ctor_set(v___x_3331_, 5, v___x_3330_);
v___x_3332_ = ((size_t)1ULL);
v___x_3333_ = lean_usize_add(v_i_3308_, v___x_3332_);
v___x_3334_ = lean_array_uset(v_bs_x27_3317_, v_i_3308_, v___x_3331_);
v_i_3308_ = v___x_3333_;
v_bs_3309_ = v___x_3334_;
goto _start;
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec_ref(v_bs_x27_3317_);
lean_dec(v_v_3315_);
lean_dec_ref(v___x_3303_);
lean_dec_ref(v___x_3301_);
v_a_3374_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3319_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3319_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3382_, lean_object* v___x_3383_, lean_object* v___x_3384_, lean_object* v_insertPos_3385_, lean_object* v_cmdLine_3386_, lean_object* v_ref_3387_, lean_object* v_sz_3388_, lean_object* v_i_3389_, lean_object* v_bs_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
uint8_t v___x_3853__boxed_3394_; size_t v_sz_boxed_3395_; size_t v_i_boxed_3396_; lean_object* v_res_3397_; 
v___x_3853__boxed_3394_ = lean_unbox(v___x_3383_);
v_sz_boxed_3395_ = lean_unbox_usize(v_sz_3388_);
lean_dec(v_sz_3388_);
v_i_boxed_3396_ = lean_unbox_usize(v_i_3389_);
lean_dec(v_i_3389_);
v_res_3397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3382_, v___x_3853__boxed_3394_, v___x_3384_, v_insertPos_3385_, v_cmdLine_3386_, v_ref_3387_, v_sz_boxed_3395_, v_i_boxed_3396_, v_bs_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v_ref_3387_);
lean_dec(v_cmdLine_3386_);
lean_dec(v_insertPos_3385_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3398_, lean_object* v_ref_3399_, lean_object* v_insertPos_3400_, lean_object* v_suggs_3401_, lean_object* v_cmdLine_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3406_ = lean_array_get_size(v_suggs_3401_);
v___x_3407_ = lean_unsigned_to_nat(0u);
v___x_3408_ = lean_nat_dec_eq(v___x_3406_, v___x_3407_);
if (v___x_3408_ == 0)
{
lean_object* v_fileMap_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v_scopes_3415_; lean_object* v___x_3416_; lean_object* v_opts_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; size_t v_sz_3420_; size_t v___x_3421_; lean_object* v___x_3422_; 
v_fileMap_3409_ = lean_ctor_get(v_a_3403_, 1);
v___x_3410_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_inc_ref_n(v_fileMap_3409_, 2);
v___x_3411_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3398_, v_fileMap_3409_);
lean_inc(v_insertPos_3400_);
v___x_3412_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3400_);
v___x_3413_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3414_ = lean_st_ref_get(v_a_3404_);
v_scopes_3415_ = lean_ctor_get(v___x_3414_, 2);
lean_inc(v_scopes_3415_);
lean_dec(v___x_3414_);
v___x_3416_ = l_List_head_x21___redArg(v___x_3413_, v_scopes_3415_);
lean_dec(v_scopes_3415_);
v_opts_3417_ = lean_ctor_get(v___x_3416_, 1);
lean_inc_ref(v_opts_3417_);
lean_dec(v___x_3416_);
v___x_3418_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3419_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3417_, v___x_3418_);
lean_dec_ref(v_opts_3417_);
v_sz_3420_ = lean_array_size(v_suggs_3401_);
v___x_3421_ = ((size_t)0ULL);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3411_, v___x_3419_, v_fileMap_3409_, v_insertPos_3400_, v_cmdLine_3402_, v_ref_3399_, v_sz_3420_, v___x_3421_, v_suggs_3401_, v_a_3403_, v_a_3404_);
lean_dec(v_insertPos_3400_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; lean_object* v___x_3427_; lean_object* v___y_3428_; lean_object* v___x_3429_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3422_, 1);
v___x_3424_ = lean_array_get_size(v_a_3423_);
v___x_3425_ = lean_unsigned_to_nat(1u);
v___x_3426_ = lean_nat_dec_eq(v___x_3424_, v___x_3425_);
v___x_3427_ = lean_box(v___x_3426_);
v___y_3428_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3428_, 0, v___x_3427_);
lean_closure_set(v___y_3428_, 1, v___x_3412_);
lean_closure_set(v___y_3428_, 2, v_ref_3399_);
lean_closure_set(v___y_3428_, 3, v_a_3423_);
lean_closure_set(v___y_3428_, 4, v___x_3410_);
lean_closure_set(v___y_3428_, 5, v___x_3407_);
v___x_3429_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3428_, v_a_3403_, v_a_3404_);
return v___x_3429_;
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v___x_3412_);
lean_dec(v_ref_3399_);
v_a_3430_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3422_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3422_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_dec_ref(v_suggs_3401_);
lean_dec(v_insertPos_3400_);
lean_dec(v_ref_3399_);
v___x_3438_ = lean_box(0);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3440_, lean_object* v_ref_3441_, lean_object* v_insertPos_3442_, lean_object* v_suggs_3443_, lean_object* v_cmdLine_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3440_, v_ref_3441_, v_insertPos_3442_, v_suggs_3443_, v_cmdLine_3444_, v_a_3445_, v_a_3446_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_cmdLine_3444_);
lean_dec(v_tacticSeq_3440_);
return v_res_3448_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3449_){
_start:
{
uint8_t v___x_3450_; 
v___x_3450_ = 0;
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3451_){
_start:
{
uint8_t v_res_3452_; lean_object* v_r_3453_; 
v_res_3452_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3451_);
lean_dec(v_x_3451_);
v_r_3453_ = lean_box(v_res_3452_);
return v_r_3453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Array_mkArray0___redArg();
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3474_, lean_object* v_ref_3475_, lean_object* v_goal_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_toCold_3485_; lean_object* v_currRecDepth_3486_; lean_object* v_ref_3487_; uint16_t v_optionFlags_3488_; uint8_t v_suppressElabErrors_3489_; uint8_t v_checkDeprecated_3490_; uint8_t v_isRecordingDeps_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v_ref_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_toCold_3485_ = lean_ctor_get(v___y_3479_, 0);
v_currRecDepth_3486_ = lean_ctor_get(v___y_3479_, 1);
v_ref_3487_ = lean_ctor_get(v___y_3479_, 2);
v_optionFlags_3488_ = lean_ctor_get_uint16(v___y_3479_, sizeof(void*)*3);
v_suppressElabErrors_3489_ = lean_ctor_get_uint8(v___y_3479_, sizeof(void*)*3 + 2);
v_checkDeprecated_3490_ = lean_ctor_get_uint8(v___y_3479_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3491_ = lean_ctor_get_uint8(v___y_3479_, sizeof(void*)*3 + 4);
v___x_3492_ = 0;
v___x_3493_ = l_Lean_SourceInfo_fromRef(v_ref_3487_, v___x_3492_);
v___x_3494_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0));
lean_inc_n(v___x_3493_, 3);
v___x_3495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
v___x_3497_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3498_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5);
v___x_3499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3493_);
lean_ctor_set(v___x_3499_, 1, v___x_3497_);
lean_ctor_set(v___x_3499_, 2, v___x_3498_);
v___x_3500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7));
v___x_3501_ = l_Lean_Syntax_node1(v___x_3493_, v___x_3500_, v___x_3499_);
v___x_3502_ = l_Lean_Syntax_node2(v___x_3493_, v___x_3496_, v___x_3495_, v___x_3501_);
v___x_3503_ = lean_box(0);
v___x_3504_ = lean_box(0);
v___x_3505_ = 1;
v___x_3506_ = lean_box(1);
v___x_3507_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3508_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_3508_, 0, v___x_3503_);
lean_ctor_set(v___x_3508_, 1, v___x_3504_);
lean_ctor_set(v___x_3508_, 2, v___x_3503_);
lean_ctor_set(v___x_3508_, 3, v___f_3474_);
lean_ctor_set(v___x_3508_, 4, v___x_3506_);
lean_ctor_set(v___x_3508_, 5, v___x_3506_);
lean_ctor_set(v___x_3508_, 6, v___x_3503_);
lean_ctor_set(v___x_3508_, 7, v___x_3507_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8, v___x_3505_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 1, v___x_3505_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 2, v___x_3505_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 3, v___x_3505_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 4, v___x_3492_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 5, v___x_3492_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 6, v___x_3492_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 7, v___x_3492_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 8, v___x_3505_);
lean_ctor_set_uint8(v___x_3508_, sizeof(void*)*8 + 9, v___x_3492_);
v___x_3509_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v___x_3510_ = lean_box(0);
v_ref_3511_ = l_Lean_replaceRef(v_ref_3475_, v_ref_3487_);
lean_inc(v_currRecDepth_3486_);
lean_inc_ref(v_toCold_3485_);
v___x_3512_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3512_, 0, v_toCold_3485_);
lean_ctor_set(v___x_3512_, 1, v_currRecDepth_3486_);
lean_ctor_set(v___x_3512_, 2, v_ref_3511_);
lean_ctor_set_uint16(v___x_3512_, sizeof(void*)*3, v_optionFlags_3488_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 2, v_suppressElabErrors_3489_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 3, v_checkDeprecated_3490_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 4, v_isRecordingDeps_3491_);
v___x_3513_ = l_Lean_Elab_runTactic(v_goal_3476_, v___x_3502_, v___x_3508_, v___x_3509_, v___y_3477_, v___y_3478_, v___x_3512_, v___y_3480_);
lean_dec_ref_known(v___x_3512_, 3);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3520_ == 0)
{
lean_object* v_unused_3521_; 
v_unused_3521_ = lean_ctor_get(v___x_3513_, 0);
lean_dec(v_unused_3521_);
v___x_3515_ = v___x_3513_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_dec(v___x_3513_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3510_);
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3510_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3542_; 
v_a_3522_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3524_ = v___x_3513_;
v_isShared_3525_ = v_isSharedCheck_3542_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3513_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3542_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
lean_inc(v_a_3522_);
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
uint8_t v___x_3528_; 
v___x_3528_ = l_Lean_Exception_isInterrupt(v_a_3522_);
if (v___x_3528_ == 0)
{
uint8_t v___x_3529_; 
lean_inc(v_a_3522_);
v___x_3529_ = l_Lean_Exception_isRuntime(v_a_3522_);
if (v___x_3529_ == 0)
{
uint8_t v___x_3530_; 
lean_inc(v_a_3522_);
v___x_3530_ = l_Lean_Exception_isMaxRecDepth(v_a_3522_);
if (v___x_3530_ == 0)
{
lean_object* v_options_3531_; uint8_t v_hasTrace_3532_; 
lean_dec_ref(v___x_3527_);
v_options_3531_ = lean_ctor_get(v_toCold_3485_, 2);
v_hasTrace_3532_ = lean_ctor_get_uint8(v_options_3531_, sizeof(void*)*1);
if (v_hasTrace_3532_ == 0)
{
lean_dec(v_a_3522_);
goto v___jp_3482_;
}
else
{
lean_object* v_inheritedTraceOptions_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v_inheritedTraceOptions_3533_ = lean_ctor_get(v_toCold_3485_, 11);
v___x_3534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3536_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3533_, v_options_3531_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_dec(v_a_3522_);
goto v___jp_3482_;
}
else
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3537_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3538_ = l_Lean_Exception_toMessageData(v_a_3522_);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3537_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3534_, v___x_3539_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
return v___x_3540_;
}
}
}
else
{
lean_dec(v_a_3522_);
return v___x_3527_;
}
}
else
{
lean_dec(v_a_3522_);
return v___x_3527_;
}
}
else
{
lean_dec(v_a_3522_);
return v___x_3527_;
}
}
}
}
v___jp_3482_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_box(0);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3543_, lean_object* v_ref_3544_, lean_object* v_goal_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3543_, v_ref_3544_, v_goal_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v_ref_3544_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_mctx_3557_; lean_object* v_ref_3558_; lean_object* v_env_3559_; lean_object* v_opts_3560_; lean_object* v_namingCtx_3561_; lean_object* v_goal_3562_; lean_object* v_decls_3563_; lean_object* v___x_3564_; 
v_mctx_3557_ = lean_ctor_get(v_c_3553_, 3);
lean_inc_ref(v_mctx_3557_);
v_ref_3558_ = lean_ctor_get(v_c_3553_, 1);
lean_inc(v_ref_3558_);
v_env_3559_ = lean_ctor_get(v_c_3553_, 2);
lean_inc_ref(v_env_3559_);
v_opts_3560_ = lean_ctor_get(v_c_3553_, 4);
lean_inc_ref(v_opts_3560_);
v_namingCtx_3561_ = lean_ctor_get(v_c_3553_, 5);
lean_inc_ref(v_namingCtx_3561_);
v_goal_3562_ = lean_ctor_get(v_c_3553_, 6);
lean_inc(v_goal_3562_);
lean_dec_ref(v_c_3553_);
v_decls_3563_ = lean_ctor_get(v_mctx_3557_, 5);
v___x_3564_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3563_, v_goal_3562_);
if (lean_obj_tag(v___x_3564_) == 1)
{
lean_object* v_val_3565_; lean_object* v_lctx_3566_; lean_object* v___f_3567_; lean_object* v___f_3568_; lean_object* v___x_3569_; 
v_val_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_val_3565_);
lean_dec_ref_known(v___x_3564_, 1);
v_lctx_3566_ = lean_ctor_get(v_val_3565_, 1);
lean_inc_ref(v_lctx_3566_);
lean_dec(v_val_3565_);
v___f_3567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3568_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3568_, 0, v___f_3567_);
lean_closure_set(v___f_3568_, 1, v_ref_3558_);
lean_closure_set(v___f_3568_, 2, v_goal_3562_);
v___x_3569_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3559_, v_mctx_3557_, v_lctx_3566_, v_opts_3560_, v_namingCtx_3561_, v___f_3568_, v_a_3554_, v_a_3555_);
return v___x_3569_;
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_dec(v___x_3564_);
lean_dec(v_goal_3562_);
lean_dec_ref(v_namingCtx_3561_);
lean_dec_ref(v_opts_3560_);
lean_dec_ref(v_env_3559_);
lean_dec(v_ref_3558_);
lean_dec_ref(v_mctx_3557_);
v___x_3570_ = lean_box(0);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
return v___x_3571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3572_, v_a_3573_, v_a_3574_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
return v_res_3576_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3577_, lean_object* v_val_3578_, lean_object* v_as_3579_, size_t v_i_3580_, size_t v_stop_3581_){
_start:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_usize_dec_eq(v_i_3580_, v_stop_3581_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v_pos_3588_; uint8_t v_severity_3589_; lean_object* v_data_3590_; lean_object* v___f_3591_; uint8_t v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; uint8_t v___y_3596_; 
v___x_3587_ = lean_array_uget_borrowed(v_as_3579_, v_i_3580_);
v_pos_3588_ = lean_ctor_get(v___x_3587_, 1);
v_severity_3589_ = lean_ctor_get_uint8(v___x_3587_, sizeof(void*)*5 + 1);
v_data_3590_ = lean_ctor_get(v___x_3587_, 4);
v___f_3591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
v___x_3592_ = 1;
lean_inc_ref(v_pos_3588_);
v___x_3593_ = l_Lean_FileMap_ofPosition(v___x_3577_, v_pos_3588_);
v___x_3594_ = l_Lean_Syntax_Range_contains(v_val_3578_, v___x_3593_, v___x_3592_);
lean_dec(v___x_3593_);
if (v_severity_3589_ == 2)
{
v___y_3596_ = v___x_3592_;
goto v___jp_3595_;
}
else
{
v___y_3596_ = v___x_3586_;
goto v___jp_3595_;
}
v___jp_3595_:
{
if (v___x_3594_ == 0)
{
goto v___jp_3582_;
}
else
{
if (v___y_3596_ == 0)
{
goto v___jp_3582_;
}
else
{
uint8_t v___x_3597_; 
lean_inc(v_data_3590_);
v___x_3597_ = l_Lean_MessageData_hasTag(v___f_3591_, v_data_3590_);
if (v___x_3597_ == 0)
{
return v___x_3592_;
}
else
{
goto v___jp_3582_;
}
}
}
}
}
else
{
uint8_t v___x_3598_; 
v___x_3598_ = 0;
return v___x_3598_;
}
v___jp_3582_:
{
size_t v___x_3583_; size_t v___x_3584_; 
v___x_3583_ = ((size_t)1ULL);
v___x_3584_ = lean_usize_add(v_i_3580_, v___x_3583_);
v_i_3580_ = v___x_3584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3599_, lean_object* v_val_3600_, lean_object* v_as_3601_, lean_object* v_i_3602_, lean_object* v_stop_3603_){
_start:
{
size_t v_i_boxed_3604_; size_t v_stop_boxed_3605_; uint8_t v_res_3606_; lean_object* v_r_3607_; 
v_i_boxed_3604_ = lean_unbox_usize(v_i_3602_);
lean_dec(v_i_3602_);
v_stop_boxed_3605_ = lean_unbox_usize(v_stop_3603_);
lean_dec(v_stop_3603_);
v_res_3606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3599_, v_val_3600_, v_as_3601_, v_i_boxed_3604_, v_stop_boxed_3605_);
lean_dec_ref(v_as_3601_);
lean_dec_ref(v_val_3600_);
lean_dec_ref(v___x_3599_);
v_r_3607_ = lean_box(v_res_3606_);
return v_r_3607_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3608_, lean_object* v_val_3609_, lean_object* v_x_3610_){
_start:
{
if (lean_obj_tag(v_x_3610_) == 0)
{
lean_object* v_cs_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v_cs_3611_ = lean_ctor_get(v_x_3610_, 0);
v___x_3612_ = lean_unsigned_to_nat(0u);
v___x_3613_ = lean_array_get_size(v_cs_3611_);
v___x_3614_ = lean_nat_dec_lt(v___x_3612_, v___x_3613_);
if (v___x_3614_ == 0)
{
return v___x_3614_;
}
else
{
size_t v___x_3615_; size_t v___x_3616_; uint8_t v___x_3617_; 
v___x_3615_ = ((size_t)0ULL);
v___x_3616_ = lean_usize_of_nat(v___x_3613_);
v___x_3617_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3608_, v_val_3609_, v_cs_3611_, v___x_3615_, v___x_3616_);
return v___x_3617_;
}
}
else
{
lean_object* v_vs_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; 
v_vs_3618_ = lean_ctor_get(v_x_3610_, 0);
v___x_3619_ = lean_unsigned_to_nat(0u);
v___x_3620_ = lean_array_get_size(v_vs_3618_);
v___x_3621_ = lean_nat_dec_lt(v___x_3619_, v___x_3620_);
if (v___x_3621_ == 0)
{
return v___x_3621_;
}
else
{
size_t v___x_3622_; size_t v___x_3623_; uint8_t v___x_3624_; 
v___x_3622_ = ((size_t)0ULL);
v___x_3623_ = lean_usize_of_nat(v___x_3620_);
v___x_3624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3608_, v_val_3609_, v_vs_3618_, v___x_3622_, v___x_3623_);
return v___x_3624_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3625_, lean_object* v_val_3626_, lean_object* v_as_3627_, size_t v_i_3628_, size_t v_stop_3629_){
_start:
{
uint8_t v___x_3630_; 
v___x_3630_ = lean_usize_dec_eq(v_i_3628_, v_stop_3629_);
if (v___x_3630_ == 0)
{
lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3631_ = lean_array_uget_borrowed(v_as_3627_, v_i_3628_);
v___x_3632_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3625_, v_val_3626_, v___x_3631_);
if (v___x_3632_ == 0)
{
size_t v___x_3633_; size_t v___x_3634_; 
v___x_3633_ = ((size_t)1ULL);
v___x_3634_ = lean_usize_add(v_i_3628_, v___x_3633_);
v_i_3628_ = v___x_3634_;
goto _start;
}
else
{
return v___x_3632_;
}
}
else
{
uint8_t v___x_3636_; 
v___x_3636_ = 0;
return v___x_3636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3637_, lean_object* v_val_3638_, lean_object* v_as_3639_, lean_object* v_i_3640_, lean_object* v_stop_3641_){
_start:
{
size_t v_i_boxed_3642_; size_t v_stop_boxed_3643_; uint8_t v_res_3644_; lean_object* v_r_3645_; 
v_i_boxed_3642_ = lean_unbox_usize(v_i_3640_);
lean_dec(v_i_3640_);
v_stop_boxed_3643_ = lean_unbox_usize(v_stop_3641_);
lean_dec(v_stop_3641_);
v_res_3644_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3637_, v_val_3638_, v_as_3639_, v_i_boxed_3642_, v_stop_boxed_3643_);
lean_dec_ref(v_as_3639_);
lean_dec_ref(v_val_3638_);
lean_dec_ref(v___x_3637_);
v_r_3645_ = lean_box(v_res_3644_);
return v_r_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3646_, lean_object* v_val_3647_, lean_object* v_x_3648_){
_start:
{
uint8_t v_res_3649_; lean_object* v_r_3650_; 
v_res_3649_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3646_, v_val_3647_, v_x_3648_);
lean_dec_ref(v_x_3648_);
lean_dec_ref(v_val_3647_);
lean_dec_ref(v___x_3646_);
v_r_3650_ = lean_box(v_res_3649_);
return v_r_3650_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3651_, lean_object* v_val_3652_, lean_object* v_t_3653_){
_start:
{
lean_object* v_root_3654_; lean_object* v_tail_3655_; uint8_t v___x_3656_; 
v_root_3654_ = lean_ctor_get(v_t_3653_, 0);
v_tail_3655_ = lean_ctor_get(v_t_3653_, 1);
v___x_3656_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3651_, v_val_3652_, v_root_3654_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; 
v___x_3657_ = lean_unsigned_to_nat(0u);
v___x_3658_ = lean_array_get_size(v_tail_3655_);
v___x_3659_ = lean_nat_dec_lt(v___x_3657_, v___x_3658_);
if (v___x_3659_ == 0)
{
return v___x_3659_;
}
else
{
size_t v___x_3660_; size_t v___x_3661_; uint8_t v___x_3662_; 
v___x_3660_ = ((size_t)0ULL);
v___x_3661_ = lean_usize_of_nat(v___x_3658_);
v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3651_, v_val_3652_, v_tail_3655_, v___x_3660_, v___x_3661_);
return v___x_3662_;
}
}
else
{
return v___x_3656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3663_, lean_object* v_val_3664_, lean_object* v_t_3665_){
_start:
{
uint8_t v_res_3666_; lean_object* v_r_3667_; 
v_res_3666_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3663_, v_val_3664_, v_t_3665_);
lean_dec_ref(v_t_3665_);
lean_dec_ref(v_val_3664_);
lean_dec_ref(v___x_3663_);
v_r_3667_ = lean_box(v_res_3666_);
return v_r_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
uint8_t v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = 0;
v___x_3673_ = l_Lean_Syntax_getRange_x3f(v_stx_3668_, v___x_3672_);
if (lean_obj_tag(v___x_3673_) == 1)
{
lean_object* v_val_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3687_; 
v_val_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3687_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_val_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3687_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_fileMap_3678_; lean_object* v___x_3679_; lean_object* v_messages_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v_fileMap_3678_ = lean_ctor_get(v_a_3669_, 1);
v___x_3679_ = lean_st_ref_get(v_a_3670_);
v_messages_3680_ = lean_ctor_get(v___x_3679_, 1);
lean_inc_ref(v_messages_3680_);
lean_dec(v___x_3679_);
v___x_3681_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3680_);
v___x_3682_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3678_, v_val_3674_, v___x_3681_);
lean_dec_ref(v___x_3681_);
lean_dec(v_val_3674_);
v___x_3683_ = lean_box(v___x_3682_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set_tag(v___x_3676_, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3683_);
v___x_3685_ = v___x_3676_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_dec(v___x_3673_);
v___x_3688_ = lean_box(v___x_3672_);
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3690_, v_a_3691_, v_a_3692_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_stx_3690_);
return v_res_3694_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3695_, lean_object* v_fileMap_3696_, lean_object* v_c_3697_){
_start:
{
lean_object* v___y_3699_; lean_object* v_kind_3703_; lean_object* v_ref_3704_; lean_object* v___y_3706_; 
v_kind_3703_ = lean_ctor_get(v_c_3697_, 0);
lean_inc(v_kind_3703_);
v_ref_3704_ = lean_ctor_get(v_c_3697_, 1);
lean_inc(v_ref_3704_);
lean_dec_ref(v_c_3697_);
if (lean_obj_tag(v_kind_3703_) == 0)
{
lean_object* v_insertPos_3722_; 
lean_dec(v_ref_3704_);
v_insertPos_3722_ = lean_ctor_get(v_kind_3703_, 1);
lean_inc(v_insertPos_3722_);
v___y_3706_ = v_insertPos_3722_;
goto v___jp_3705_;
}
else
{
uint8_t v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = 0;
v___x_3724_ = l_Lean_Syntax_getPos_x3f(v_ref_3704_, v___x_3723_);
lean_dec(v_ref_3704_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_unsigned_to_nat(0u);
v___y_3706_ = v___x_3725_;
goto v___jp_3705_;
}
else
{
lean_object* v_val_3726_; 
v_val_3726_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_val_3726_);
lean_dec_ref_known(v___x_3724_, 1);
v___y_3706_ = v_val_3726_;
goto v___jp_3705_;
}
}
v___jp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3700_ = l_List_lengthTR___redArg(v___y_3699_);
lean_dec(v___y_3699_);
v___x_3701_ = lean_unsigned_to_nat(1u);
v___x_3702_ = lean_nat_dec_eq(v___x_3700_, v___x_3701_);
lean_dec(v___x_3700_);
return v___x_3702_;
}
v___jp_3705_:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3696_, v_tree_3695_, v___y_3706_);
if (lean_obj_tag(v___x_3707_) == 1)
{
lean_object* v_tail_3708_; 
v_tail_3708_ = lean_ctor_get(v___x_3707_, 1);
if (lean_obj_tag(v_tail_3708_) == 0)
{
if (lean_obj_tag(v_kind_3703_) == 0)
{
lean_object* v_head_3709_; lean_object* v_tacticSeq_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; 
v_head_3709_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_head_3709_);
lean_dec_ref_known(v___x_3707_, 2);
v_tacticSeq_3710_ = lean_ctor_get(v_kind_3703_, 0);
lean_inc(v_tacticSeq_3710_);
lean_dec_ref_known(v_kind_3703_, 2);
v___x_3711_ = 0;
v___x_3712_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3710_, v___x_3711_);
lean_dec(v_tacticSeq_3710_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_tacticInfo_3713_; lean_object* v_goalsBefore_3714_; 
v_tacticInfo_3713_ = lean_ctor_get(v_head_3709_, 1);
lean_inc_ref(v_tacticInfo_3713_);
lean_dec(v_head_3709_);
v_goalsBefore_3714_ = lean_ctor_get(v_tacticInfo_3713_, 2);
lean_inc(v_goalsBefore_3714_);
lean_dec_ref(v_tacticInfo_3713_);
v___y_3699_ = v_goalsBefore_3714_;
goto v___jp_3698_;
}
else
{
lean_object* v_tacticInfo_3715_; lean_object* v_goalsAfter_3716_; 
lean_dec_ref_known(v___x_3712_, 1);
v_tacticInfo_3715_ = lean_ctor_get(v_head_3709_, 1);
lean_inc_ref(v_tacticInfo_3715_);
lean_dec(v_head_3709_);
v_goalsAfter_3716_ = lean_ctor_get(v_tacticInfo_3715_, 4);
lean_inc(v_goalsAfter_3716_);
lean_dec_ref(v_tacticInfo_3715_);
v___y_3699_ = v_goalsAfter_3716_;
goto v___jp_3698_;
}
}
else
{
lean_object* v_head_3717_; lean_object* v_tacticInfo_3718_; lean_object* v_goalsBefore_3719_; 
v_head_3717_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_head_3717_);
lean_dec_ref_known(v___x_3707_, 2);
v_tacticInfo_3718_ = lean_ctor_get(v_head_3717_, 1);
lean_inc_ref(v_tacticInfo_3718_);
lean_dec(v_head_3717_);
v_goalsBefore_3719_ = lean_ctor_get(v_tacticInfo_3718_, 2);
lean_inc(v_goalsBefore_3719_);
lean_dec_ref(v_tacticInfo_3718_);
v___y_3699_ = v_goalsBefore_3719_;
goto v___jp_3698_;
}
}
else
{
uint8_t v___x_3720_; 
lean_dec_ref_known(v___x_3707_, 2);
lean_dec(v_kind_3703_);
v___x_3720_ = 0;
return v___x_3720_;
}
}
else
{
uint8_t v___x_3721_; 
lean_dec(v___x_3707_);
lean_dec(v_kind_3703_);
v___x_3721_ = 0;
return v___x_3721_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3727_, lean_object* v_fileMap_3728_, lean_object* v_c_3729_){
_start:
{
uint8_t v_res_3730_; lean_object* v_r_3731_; 
v_res_3730_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3727_, v_fileMap_3728_, v_c_3729_);
v_r_3731_ = lean_box(v_res_3730_);
return v_r_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3732_){
_start:
{
lean_object* v___x_3734_; lean_object* v_infoState_3735_; lean_object* v_trees_3736_; lean_object* v___x_3737_; 
v___x_3734_ = lean_st_ref_get(v___y_3732_);
v_infoState_3735_ = lean_ctor_get(v___x_3734_, 8);
lean_inc_ref(v_infoState_3735_);
lean_dec(v___x_3734_);
v_trees_3736_ = lean_ctor_get(v_infoState_3735_, 2);
lean_inc_ref(v_trees_3736_);
lean_dec_ref(v_infoState_3735_);
v___x_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3737_, 0, v_trees_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3738_);
lean_dec(v___y_3738_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3742_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
return v_res_3748_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3751_ = l_Lean_stringToMessageData(v___x_3750_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3752_, lean_object* v___x_3753_, lean_object* v___x_3754_, lean_object* v_as_3755_, size_t v_sz_3756_, size_t v_i_3757_, lean_object* v_b_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_a_3763_; uint8_t v___x_3767_; 
v___x_3767_ = lean_usize_dec_lt(v_i_3757_, v_sz_3756_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; 
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_tree_3752_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_b_3758_);
return v___x_3768_;
}
else
{
lean_object* v___x_3769_; lean_object* v_a_3770_; uint8_t v___x_3771_; 
v___x_3769_ = lean_box(0);
v_a_3770_ = lean_array_uget_borrowed(v_as_3755_, v_i_3757_);
lean_inc(v_a_3770_);
lean_inc_ref(v___x_3753_);
lean_inc_ref(v_tree_3752_);
v___x_3771_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3752_, v___x_3753_, v_a_3770_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v_scopes_3777_; lean_object* v___x_3778_; lean_object* v_opts_3779_; uint8_t v_hasTrace_3780_; 
v___x_3772_ = l_Lean_inheritedTraceOptions;
v___x_3773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3774_ = lean_st_ref_get(v___x_3772_);
v___x_3775_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3776_ = lean_st_ref_get(v___y_3760_);
v_scopes_3777_ = lean_ctor_get(v___x_3776_, 2);
lean_inc(v_scopes_3777_);
lean_dec(v___x_3776_);
v___x_3778_ = l_List_head_x21___redArg(v___x_3775_, v_scopes_3777_);
lean_dec(v_scopes_3777_);
v_opts_3779_ = lean_ctor_get(v___x_3778_, 1);
lean_inc_ref(v_opts_3779_);
lean_dec(v___x_3778_);
v_hasTrace_3780_ = lean_ctor_get_uint8(v_opts_3779_, sizeof(void*)*1);
if (v_hasTrace_3780_ == 0)
{
lean_dec_ref(v_opts_3779_);
lean_dec(v___x_3774_);
v_a_3763_ = v___x_3769_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3781_; uint8_t v___x_3782_; 
v___x_3781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3782_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3774_, v_opts_3779_, v___x_3781_);
lean_dec_ref(v_opts_3779_);
lean_dec(v___x_3774_);
if (v___x_3782_ == 0)
{
v_a_3763_ = v___x_3769_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3784_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3773_, v___x_3783_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_dec_ref_known(v___x_3784_, 1);
v_a_3763_ = v___x_3769_;
goto v___jp_3762_;
}
else
{
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_tree_3752_);
return v___x_3784_;
}
}
}
}
else
{
lean_object* v_kind_3785_; 
v_kind_3785_ = lean_ctor_get(v_a_3770_, 0);
if (lean_obj_tag(v_kind_3785_) == 0)
{
lean_object* v_ref_3786_; lean_object* v_tacticSeq_3787_; lean_object* v_insertPos_3788_; lean_object* v___x_3789_; 
v_ref_3786_ = lean_ctor_get(v_a_3770_, 1);
v_tacticSeq_3787_ = lean_ctor_get(v_kind_3785_, 0);
v_insertPos_3788_ = lean_ctor_get(v_kind_3785_, 1);
lean_inc(v_a_3770_);
v___x_3789_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3770_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3791_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
lean_inc(v_insertPos_3788_);
lean_inc(v_ref_3786_);
v___x_3791_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3787_, v_ref_3786_, v_insertPos_3788_, v_a_3790_, v___x_3754_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_dec_ref_known(v___x_3791_, 1);
v_a_3763_ = v___x_3769_;
goto v___jp_3762_;
}
else
{
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_tree_3752_);
return v___x_3791_;
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_tree_3752_);
v_a_3792_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3789_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3789_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_object* v___x_3800_; 
lean_inc(v_a_3770_);
v___x_3800_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3770_, v___y_3759_, v___y_3760_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_dec_ref_known(v___x_3800_, 1);
v_a_3763_ = v___x_3769_;
goto v___jp_3762_;
}
else
{
lean_dec_ref(v___x_3753_);
lean_dec_ref(v_tree_3752_);
return v___x_3800_;
}
}
}
}
v___jp_3762_:
{
size_t v___x_3764_; size_t v___x_3765_; 
v___x_3764_ = ((size_t)1ULL);
v___x_3765_ = lean_usize_add(v_i_3757_, v___x_3764_);
v_i_3757_ = v___x_3765_;
v_b_3758_ = v_a_3763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3801_, lean_object* v___x_3802_, lean_object* v___x_3803_, lean_object* v_as_3804_, lean_object* v_sz_3805_, lean_object* v_i_3806_, lean_object* v_b_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
size_t v_sz_boxed_3811_; size_t v_i_boxed_3812_; lean_object* v_res_3813_; 
v_sz_boxed_3811_ = lean_unbox_usize(v_sz_3805_);
lean_dec(v_sz_3805_);
v_i_boxed_3812_ = lean_unbox_usize(v_i_3806_);
lean_dec(v_i_3806_);
v_res_3813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3801_, v___x_3802_, v___x_3803_, v_as_3804_, v_sz_boxed_3811_, v_i_boxed_3812_, v_b_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec_ref(v_as_3804_);
lean_dec(v___x_3803_);
return v_res_3813_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3819_ = l_Lean_stringToMessageData(v___x_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3820_, lean_object* v___x_3821_, lean_object* v___x_3822_, lean_object* v___x_3823_, lean_object* v___x_3824_, lean_object* v_as_3825_, size_t v_sz_3826_, size_t v_i_3827_, lean_object* v_b_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
uint8_t v___x_3832_; 
v___x_3832_ = lean_usize_dec_lt(v_i_3827_, v_sz_3826_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; 
lean_dec_ref(v___x_3823_);
lean_dec(v_stx_3820_);
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v_b_3828_);
return v___x_3833_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v_a_3837_; lean_object* v___x_3838_; 
lean_dec_ref(v_b_3828_);
v___x_3834_ = lean_box(0);
v___x_3835_ = l_Lean_inheritedTraceOptions;
v___x_3836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3837_ = lean_array_uget_borrowed(v_as_3825_, v_i_3827_);
lean_inc(v_a_3837_);
lean_inc(v_stx_3820_);
v___x_3838_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3820_, v___x_3821_, v_a_3837_, v___x_3822_, v___y_3829_, v___y_3830_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v_scopes_3861_; lean_object* v___x_3862_; lean_object* v_opts_3863_; uint8_t v_hasTrace_3864_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v___x_3858_ = lean_st_ref_get(v___x_3835_);
v___x_3859_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3860_ = lean_st_ref_get(v___y_3830_);
v_scopes_3861_ = lean_ctor_get(v___x_3860_, 2);
lean_inc(v_scopes_3861_);
lean_dec(v___x_3860_);
v___x_3862_ = l_List_head_x21___redArg(v___x_3859_, v_scopes_3861_);
lean_dec(v_scopes_3861_);
v_opts_3863_ = lean_ctor_get(v___x_3862_, 1);
lean_inc_ref(v_opts_3863_);
lean_dec(v___x_3862_);
v_hasTrace_3864_ = lean_ctor_get_uint8(v_opts_3863_, sizeof(void*)*1);
if (v_hasTrace_3864_ == 0)
{
lean_dec_ref(v_opts_3863_);
lean_dec(v___x_3858_);
v___y_3841_ = v___y_3829_;
v___y_3842_ = v___y_3830_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3865_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3866_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3858_, v_opts_3863_, v___x_3865_);
lean_dec_ref(v_opts_3863_);
lean_dec(v___x_3858_);
if (v___x_3866_ == 0)
{
v___y_3841_ = v___y_3829_;
v___y_3842_ = v___y_3830_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3868_ = lean_array_get_size(v_a_3839_);
v___x_3869_ = l_Nat_reprFast(v___x_3868_);
v___x_3870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
v___x_3871_ = l_Lean_MessageData_ofFormat(v___x_3870_);
v___x_3872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3867_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
v___x_3873_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3836_, v___x_3872_, v___y_3829_, v___y_3830_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_dec_ref_known(v___x_3873_, 1);
v___y_3841_ = v___y_3829_;
v___y_3842_ = v___y_3830_;
goto v___jp_3840_;
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_a_3839_);
lean_dec_ref(v___x_3823_);
lean_dec(v_stx_3820_);
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
v___jp_3840_:
{
size_t v_sz_3843_; size_t v___x_3844_; lean_object* v___x_3845_; 
v_sz_3843_ = lean_array_size(v_a_3839_);
v___x_3844_ = ((size_t)0ULL);
lean_inc_ref(v___x_3823_);
lean_inc(v_a_3837_);
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3837_, v___x_3823_, v___x_3824_, v_a_3839_, v_sz_3843_, v___x_3844_, v___x_3834_, v___y_3841_, v___y_3842_);
lean_dec(v_a_3839_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v___x_3846_; size_t v___x_3847_; size_t v___x_3848_; 
lean_dec_ref_known(v___x_3845_, 1);
v___x_3846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3847_ = ((size_t)1ULL);
v___x_3848_ = lean_usize_add(v_i_3827_, v___x_3847_);
v_i_3827_ = v___x_3848_;
v_b_3828_ = v___x_3846_;
goto _start;
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v___x_3823_);
lean_dec(v_stx_3820_);
v_a_3850_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3845_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3845_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec_ref(v___x_3823_);
lean_dec(v_stx_3820_);
v_a_3882_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3838_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3838_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3890_, lean_object* v___x_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v___x_3894_, lean_object* v_as_3895_, lean_object* v_sz_3896_, lean_object* v_i_3897_, lean_object* v_b_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
size_t v_sz_boxed_3902_; size_t v_i_boxed_3903_; lean_object* v_res_3904_; 
v_sz_boxed_3902_ = lean_unbox_usize(v_sz_3896_);
lean_dec(v_sz_3896_);
v_i_boxed_3903_ = lean_unbox_usize(v_i_3897_);
lean_dec(v_i_3897_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3890_, v___x_3891_, v___x_3892_, v___x_3893_, v___x_3894_, v_as_3895_, v_sz_boxed_3902_, v_i_boxed_3903_, v_b_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec_ref(v_as_3895_);
lean_dec(v___x_3894_);
lean_dec_ref(v___x_3892_);
lean_dec_ref(v___x_3891_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3905_, lean_object* v___x_3906_, lean_object* v___x_3907_, lean_object* v___x_3908_, lean_object* v___x_3909_, lean_object* v_as_3910_, size_t v_sz_3911_, size_t v_i_3912_, lean_object* v_b_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
uint8_t v___x_3917_; 
v___x_3917_ = lean_usize_dec_lt(v_i_3912_, v_sz_3911_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; 
lean_dec_ref(v___x_3908_);
lean_dec(v_stx_3905_);
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_b_3913_);
return v___x_3918_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v_a_3922_; lean_object* v___x_3923_; 
lean_dec_ref(v_b_3913_);
v___x_3919_ = lean_box(0);
v___x_3920_ = l_Lean_inheritedTraceOptions;
v___x_3921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3922_ = lean_array_uget_borrowed(v_as_3910_, v_i_3912_);
lean_inc(v_a_3922_);
lean_inc(v_stx_3905_);
v___x_3923_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3905_, v___x_3906_, v_a_3922_, v___x_3907_, v___y_3914_, v___y_3915_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v_scopes_3946_; lean_object* v___x_3947_; lean_object* v_opts_3948_; uint8_t v_hasTrace_3949_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3943_ = lean_st_ref_get(v___x_3920_);
v___x_3944_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3945_ = lean_st_ref_get(v___y_3915_);
v_scopes_3946_ = lean_ctor_get(v___x_3945_, 2);
lean_inc(v_scopes_3946_);
lean_dec(v___x_3945_);
v___x_3947_ = l_List_head_x21___redArg(v___x_3944_, v_scopes_3946_);
lean_dec(v_scopes_3946_);
v_opts_3948_ = lean_ctor_get(v___x_3947_, 1);
lean_inc_ref(v_opts_3948_);
lean_dec(v___x_3947_);
v_hasTrace_3949_ = lean_ctor_get_uint8(v_opts_3948_, sizeof(void*)*1);
if (v_hasTrace_3949_ == 0)
{
lean_dec_ref(v_opts_3948_);
lean_dec(v___x_3943_);
v___y_3926_ = v___y_3914_;
v___y_3927_ = v___y_3915_;
goto v___jp_3925_;
}
else
{
lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3950_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3951_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3943_, v_opts_3948_, v___x_3950_);
lean_dec_ref(v_opts_3948_);
lean_dec(v___x_3943_);
if (v___x_3951_ == 0)
{
v___y_3926_ = v___y_3914_;
v___y_3927_ = v___y_3915_;
goto v___jp_3925_;
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3952_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3953_ = lean_array_get_size(v_a_3924_);
v___x_3954_ = l_Nat_reprFast(v___x_3953_);
v___x_3955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
v___x_3956_ = l_Lean_MessageData_ofFormat(v___x_3955_);
v___x_3957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3952_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3921_, v___x_3957_, v___y_3914_, v___y_3915_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_dec_ref_known(v___x_3958_, 1);
v___y_3926_ = v___y_3914_;
v___y_3927_ = v___y_3915_;
goto v___jp_3925_;
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_dec(v_a_3924_);
lean_dec_ref(v___x_3908_);
lean_dec(v_stx_3905_);
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3958_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3958_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
v___jp_3925_:
{
size_t v_sz_3928_; size_t v___x_3929_; lean_object* v___x_3930_; 
v_sz_3928_ = lean_array_size(v_a_3924_);
v___x_3929_ = ((size_t)0ULL);
lean_inc_ref(v___x_3908_);
lean_inc(v_a_3922_);
v___x_3930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3922_, v___x_3908_, v___x_3909_, v_a_3924_, v_sz_3928_, v___x_3929_, v___x_3919_, v___y_3926_, v___y_3927_);
lean_dec(v_a_3924_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v___x_3931_; size_t v___x_3932_; size_t v___x_3933_; lean_object* v___x_3934_; 
lean_dec_ref_known(v___x_3930_, 1);
v___x_3931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3932_ = ((size_t)1ULL);
v___x_3933_ = lean_usize_add(v_i_3912_, v___x_3932_);
v___x_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3905_, v___x_3906_, v___x_3907_, v___x_3908_, v___x_3909_, v_as_3910_, v_sz_3911_, v___x_3933_, v___x_3931_, v___y_3914_, v___y_3915_);
return v___x_3934_;
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v___x_3908_);
lean_dec(v_stx_3905_);
v_a_3935_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3930_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3930_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec_ref(v___x_3908_);
lean_dec(v_stx_3905_);
v_a_3967_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3923_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3923_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3975_, lean_object* v___x_3976_, lean_object* v___x_3977_, lean_object* v___x_3978_, lean_object* v___x_3979_, lean_object* v_as_3980_, lean_object* v_sz_3981_, lean_object* v_i_3982_, lean_object* v_b_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
size_t v_sz_boxed_3987_; size_t v_i_boxed_3988_; lean_object* v_res_3989_; 
v_sz_boxed_3987_ = lean_unbox_usize(v_sz_3981_);
lean_dec(v_sz_3981_);
v_i_boxed_3988_ = lean_unbox_usize(v_i_3982_);
lean_dec(v_i_3982_);
v_res_3989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3975_, v___x_3976_, v___x_3977_, v___x_3978_, v___x_3979_, v_as_3980_, v_sz_boxed_3987_, v_i_boxed_3988_, v_b_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec_ref(v_as_3980_);
lean_dec(v___x_3979_);
lean_dec_ref(v___x_3977_);
lean_dec_ref(v___x_3976_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_3993_, lean_object* v___x_3994_, lean_object* v___x_3995_, lean_object* v___x_3996_, lean_object* v___x_3997_, lean_object* v_as_3998_, size_t v_sz_3999_, size_t v_i_4000_, lean_object* v_b_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
uint8_t v___x_4005_; 
v___x_4005_ = lean_usize_dec_lt(v_i_4000_, v_sz_3999_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; 
lean_dec_ref(v___x_3996_);
lean_dec(v_stx_3993_);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v_b_4001_);
return v___x_4006_;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v_a_4010_; lean_object* v___x_4011_; 
lean_dec_ref(v_b_4001_);
v___x_4007_ = lean_box(0);
v___x_4008_ = l_Lean_inheritedTraceOptions;
v___x_4009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4010_ = lean_array_uget_borrowed(v_as_3998_, v_i_4000_);
lean_inc(v_a_4010_);
lean_inc(v_stx_3993_);
v___x_4011_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3993_, v___x_3994_, v_a_4010_, v___x_3995_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v_scopes_4034_; lean_object* v___x_4035_; lean_object* v_opts_4036_; uint8_t v_hasTrace_4037_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v___x_4031_ = lean_st_ref_get(v___x_4008_);
v___x_4032_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4033_ = lean_st_ref_get(v___y_4003_);
v_scopes_4034_ = lean_ctor_get(v___x_4033_, 2);
lean_inc(v_scopes_4034_);
lean_dec(v___x_4033_);
v___x_4035_ = l_List_head_x21___redArg(v___x_4032_, v_scopes_4034_);
lean_dec(v_scopes_4034_);
v_opts_4036_ = lean_ctor_get(v___x_4035_, 1);
lean_inc_ref(v_opts_4036_);
lean_dec(v___x_4035_);
v_hasTrace_4037_ = lean_ctor_get_uint8(v_opts_4036_, sizeof(void*)*1);
if (v_hasTrace_4037_ == 0)
{
lean_dec_ref(v_opts_4036_);
lean_dec(v___x_4031_);
v___y_4014_ = v___y_4002_;
v___y_4015_ = v___y_4003_;
goto v___jp_4013_;
}
else
{
lean_object* v___x_4038_; uint8_t v___x_4039_; 
v___x_4038_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4031_, v_opts_4036_, v___x_4038_);
lean_dec_ref(v_opts_4036_);
lean_dec(v___x_4031_);
if (v___x_4039_ == 0)
{
v___y_4014_ = v___y_4002_;
v___y_4015_ = v___y_4003_;
goto v___jp_4013_;
}
else
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4041_ = lean_array_get_size(v_a_4012_);
v___x_4042_ = l_Nat_reprFast(v___x_4041_);
v___x_4043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
v___x_4044_ = l_Lean_MessageData_ofFormat(v___x_4043_);
v___x_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4040_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4009_, v___x_4045_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_dec_ref_known(v___x_4046_, 1);
v___y_4014_ = v___y_4002_;
v___y_4015_ = v___y_4003_;
goto v___jp_4013_;
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v_a_4012_);
lean_dec_ref(v___x_3996_);
lean_dec(v_stx_3993_);
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
v___jp_4013_:
{
size_t v_sz_4016_; size_t v___x_4017_; lean_object* v___x_4018_; 
v_sz_4016_ = lean_array_size(v_a_4012_);
v___x_4017_ = ((size_t)0ULL);
lean_inc_ref(v___x_3996_);
lean_inc(v_a_4010_);
v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4010_, v___x_3996_, v___x_3997_, v_a_4012_, v_sz_4016_, v___x_4017_, v___x_4007_, v___y_4014_, v___y_4015_);
lean_dec(v_a_4012_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v___x_4019_; size_t v___x_4020_; size_t v___x_4021_; 
lean_dec_ref_known(v___x_4018_, 1);
v___x_4019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4020_ = ((size_t)1ULL);
v___x_4021_ = lean_usize_add(v_i_4000_, v___x_4020_);
v_i_4000_ = v___x_4021_;
v_b_4001_ = v___x_4019_;
goto _start;
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec_ref(v___x_3996_);
lean_dec(v_stx_3993_);
v_a_4023_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4018_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4018_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v___x_3996_);
lean_dec(v_stx_3993_);
v_a_4055_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4011_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4011_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4063_, lean_object* v___x_4064_, lean_object* v___x_4065_, lean_object* v___x_4066_, lean_object* v___x_4067_, lean_object* v_as_4068_, lean_object* v_sz_4069_, lean_object* v_i_4070_, lean_object* v_b_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
size_t v_sz_boxed_4075_; size_t v_i_boxed_4076_; lean_object* v_res_4077_; 
v_sz_boxed_4075_ = lean_unbox_usize(v_sz_4069_);
lean_dec(v_sz_4069_);
v_i_boxed_4076_ = lean_unbox_usize(v_i_4070_);
lean_dec(v_i_4070_);
v_res_4077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4063_, v___x_4064_, v___x_4065_, v___x_4066_, v___x_4067_, v_as_4068_, v_sz_boxed_4075_, v_i_boxed_4076_, v_b_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec_ref(v_as_4068_);
lean_dec(v___x_4067_);
lean_dec_ref(v___x_4065_);
lean_dec_ref(v___x_4064_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4078_, lean_object* v___x_4079_, lean_object* v___x_4080_, lean_object* v___x_4081_, lean_object* v___x_4082_, lean_object* v_as_4083_, size_t v_sz_4084_, size_t v_i_4085_, lean_object* v_b_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
uint8_t v___x_4090_; 
v___x_4090_ = lean_usize_dec_lt(v_i_4085_, v_sz_4084_);
if (v___x_4090_ == 0)
{
lean_object* v___x_4091_; 
lean_dec_ref(v___x_4081_);
lean_dec(v_stx_4078_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v_b_4086_);
return v___x_4091_;
}
else
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v_a_4095_; lean_object* v___x_4096_; 
lean_dec_ref(v_b_4086_);
v___x_4092_ = lean_box(0);
v___x_4093_ = l_Lean_inheritedTraceOptions;
v___x_4094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4095_ = lean_array_uget_borrowed(v_as_4083_, v_i_4085_);
lean_inc(v_a_4095_);
lean_inc(v_stx_4078_);
v___x_4096_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4078_, v___x_4079_, v_a_4095_, v___x_4080_, v___y_4087_, v___y_4088_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v_scopes_4119_; lean_object* v___x_4120_; lean_object* v_opts_4121_; uint8_t v_hasTrace_4122_; 
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4096_, 1);
v___x_4116_ = lean_st_ref_get(v___x_4093_);
v___x_4117_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4118_ = lean_st_ref_get(v___y_4088_);
v_scopes_4119_ = lean_ctor_get(v___x_4118_, 2);
lean_inc(v_scopes_4119_);
lean_dec(v___x_4118_);
v___x_4120_ = l_List_head_x21___redArg(v___x_4117_, v_scopes_4119_);
lean_dec(v_scopes_4119_);
v_opts_4121_ = lean_ctor_get(v___x_4120_, 1);
lean_inc_ref(v_opts_4121_);
lean_dec(v___x_4120_);
v_hasTrace_4122_ = lean_ctor_get_uint8(v_opts_4121_, sizeof(void*)*1);
if (v_hasTrace_4122_ == 0)
{
lean_dec_ref(v_opts_4121_);
lean_dec(v___x_4116_);
v___y_4099_ = v___y_4087_;
v___y_4100_ = v___y_4088_;
goto v___jp_4098_;
}
else
{
lean_object* v___x_4123_; uint8_t v___x_4124_; 
v___x_4123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4124_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4116_, v_opts_4121_, v___x_4123_);
lean_dec_ref(v_opts_4121_);
lean_dec(v___x_4116_);
if (v___x_4124_ == 0)
{
v___y_4099_ = v___y_4087_;
v___y_4100_ = v___y_4088_;
goto v___jp_4098_;
}
else
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4125_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4126_ = lean_array_get_size(v_a_4097_);
v___x_4127_ = l_Nat_reprFast(v___x_4126_);
v___x_4128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
v___x_4129_ = l_Lean_MessageData_ofFormat(v___x_4128_);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4125_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4094_, v___x_4130_, v___y_4087_, v___y_4088_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_dec_ref_known(v___x_4131_, 1);
v___y_4099_ = v___y_4087_;
v___y_4100_ = v___y_4088_;
goto v___jp_4098_;
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec(v_a_4097_);
lean_dec_ref(v___x_4081_);
lean_dec(v_stx_4078_);
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4131_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4131_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
}
v___jp_4098_:
{
size_t v_sz_4101_; size_t v___x_4102_; lean_object* v___x_4103_; 
v_sz_4101_ = lean_array_size(v_a_4097_);
v___x_4102_ = ((size_t)0ULL);
lean_inc_ref(v___x_4081_);
lean_inc(v_a_4095_);
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4095_, v___x_4081_, v___x_4082_, v_a_4097_, v_sz_4101_, v___x_4102_, v___x_4092_, v___y_4099_, v___y_4100_);
lean_dec(v_a_4097_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v___x_4104_; size_t v___x_4105_; size_t v___x_4106_; lean_object* v___x_4107_; 
lean_dec_ref_known(v___x_4103_, 1);
v___x_4104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4105_ = ((size_t)1ULL);
v___x_4106_ = lean_usize_add(v_i_4085_, v___x_4105_);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4078_, v___x_4079_, v___x_4080_, v___x_4081_, v___x_4082_, v_as_4083_, v_sz_4084_, v___x_4106_, v___x_4104_, v___y_4087_, v___y_4088_);
return v___x_4107_;
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec_ref(v___x_4081_);
lean_dec(v_stx_4078_);
v_a_4108_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4103_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4103_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v___x_4081_);
lean_dec(v_stx_4078_);
v_a_4140_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4096_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4096_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4148_, lean_object* v___x_4149_, lean_object* v___x_4150_, lean_object* v___x_4151_, lean_object* v___x_4152_, lean_object* v_as_4153_, lean_object* v_sz_4154_, lean_object* v_i_4155_, lean_object* v_b_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
size_t v_sz_boxed_4160_; size_t v_i_boxed_4161_; lean_object* v_res_4162_; 
v_sz_boxed_4160_ = lean_unbox_usize(v_sz_4154_);
lean_dec(v_sz_4154_);
v_i_boxed_4161_ = lean_unbox_usize(v_i_4155_);
lean_dec(v_i_4155_);
v_res_4162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4148_, v___x_4149_, v___x_4150_, v___x_4151_, v___x_4152_, v_as_4153_, v_sz_boxed_4160_, v_i_boxed_4161_, v_b_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec_ref(v_as_4153_);
lean_dec(v___x_4152_);
lean_dec_ref(v___x_4150_);
lean_dec_ref(v___x_4149_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4163_, lean_object* v_stx_4164_, lean_object* v___x_4165_, lean_object* v___x_4166_, lean_object* v___x_4167_, lean_object* v___x_4168_, lean_object* v_n_4169_, lean_object* v_b_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
if (lean_obj_tag(v_n_4169_) == 0)
{
lean_object* v_cs_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; size_t v_sz_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v_cs_4174_ = lean_ctor_get(v_n_4169_, 0);
v___x_4175_ = lean_box(0);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
lean_ctor_set(v___x_4176_, 1, v_b_4170_);
v_sz_4177_ = lean_array_size(v_cs_4174_);
v___x_4178_ = ((size_t)0ULL);
v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4163_, v_stx_4164_, v___x_4165_, v___x_4166_, v___x_4167_, v___x_4168_, v_cs_4174_, v_sz_4177_, v___x_4178_, v___x_4176_, v___y_4171_, v___y_4172_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4194_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4194_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4194_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v_fst_4184_; 
v_fst_4184_ = lean_ctor_get(v_a_4180_, 0);
if (lean_obj_tag(v_fst_4184_) == 0)
{
lean_object* v_snd_4185_; lean_object* v___x_4186_; lean_object* v___x_4188_; 
v_snd_4185_ = lean_ctor_get(v_a_4180_, 1);
lean_inc(v_snd_4185_);
lean_dec(v_a_4180_);
v___x_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4186_, 0, v_snd_4185_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v___x_4186_);
v___x_4188_ = v___x_4182_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4186_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
else
{
lean_object* v_val_4190_; lean_object* v___x_4192_; 
lean_inc_ref(v_fst_4184_);
lean_dec(v_a_4180_);
v_val_4190_ = lean_ctor_get(v_fst_4184_, 0);
lean_inc(v_val_4190_);
lean_dec_ref_known(v_fst_4184_, 1);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v_val_4190_);
v___x_4192_ = v___x_4182_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_val_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
v_a_4195_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4179_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4179_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v_vs_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; size_t v_sz_4206_; size_t v___x_4207_; lean_object* v___x_4208_; 
v_vs_4203_ = lean_ctor_get(v_n_4169_, 0);
v___x_4204_ = lean_box(0);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
lean_ctor_set(v___x_4205_, 1, v_b_4170_);
v_sz_4206_ = lean_array_size(v_vs_4203_);
v___x_4207_ = ((size_t)0ULL);
v___x_4208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4164_, v___x_4165_, v___x_4166_, v___x_4167_, v___x_4168_, v_vs_4203_, v_sz_4206_, v___x_4207_, v___x_4205_, v___y_4171_, v___y_4172_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4223_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4211_ = v___x_4208_;
v_isShared_4212_ = v_isSharedCheck_4223_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4223_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v_fst_4213_; 
v_fst_4213_ = lean_ctor_get(v_a_4209_, 0);
if (lean_obj_tag(v_fst_4213_) == 0)
{
lean_object* v_snd_4214_; lean_object* v___x_4215_; lean_object* v___x_4217_; 
v_snd_4214_ = lean_ctor_get(v_a_4209_, 1);
lean_inc(v_snd_4214_);
lean_dec(v_a_4209_);
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_snd_4214_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___x_4215_);
v___x_4217_ = v___x_4211_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
else
{
lean_object* v_val_4219_; lean_object* v___x_4221_; 
lean_inc_ref(v_fst_4213_);
lean_dec(v_a_4209_);
v_val_4219_ = lean_ctor_get(v_fst_4213_, 0);
lean_inc(v_val_4219_);
lean_dec_ref_known(v_fst_4213_, 1);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v_val_4219_);
v___x_4221_ = v___x_4211_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_val_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4208_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4208_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4232_, lean_object* v_stx_4233_, lean_object* v___x_4234_, lean_object* v___x_4235_, lean_object* v___x_4236_, lean_object* v___x_4237_, lean_object* v_as_4238_, size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_b_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_usize_dec_lt(v_i_4240_, v_sz_4239_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
lean_dec_ref(v___x_4236_);
lean_dec(v_stx_4233_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v_b_4241_);
return v___x_4246_;
}
else
{
lean_object* v_snd_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4281_; 
v_snd_4247_ = lean_ctor_get(v_b_4241_, 1);
v_isSharedCheck_4281_ = !lean_is_exclusive(v_b_4241_);
if (v_isSharedCheck_4281_ == 0)
{
lean_object* v_unused_4282_; 
v_unused_4282_ = lean_ctor_get(v_b_4241_, 0);
lean_dec(v_unused_4282_);
v___x_4249_ = v_b_4241_;
v_isShared_4250_ = v_isSharedCheck_4281_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_snd_4247_);
lean_dec(v_b_4241_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4281_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4251_; lean_object* v_a_4252_; lean_object* v___x_4253_; 
v___x_4251_ = lean_box(0);
v_a_4252_ = lean_array_uget_borrowed(v_as_4238_, v_i_4240_);
lean_inc(v_snd_4247_);
lean_inc_ref(v___x_4236_);
lean_inc(v_stx_4233_);
v___x_4253_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4232_, v_stx_4233_, v___x_4234_, v___x_4235_, v___x_4236_, v___x_4237_, v_a_4252_, v_snd_4247_, v___y_4242_, v___y_4243_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4272_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4256_ = v___x_4253_;
v_isShared_4257_ = v_isSharedCheck_4272_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4253_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4272_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
if (lean_obj_tag(v_a_4254_) == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4260_; 
lean_dec_ref(v___x_4236_);
lean_dec(v_stx_4233_);
v___x_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4258_, 0, v_a_4254_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 0, v___x_4258_);
v___x_4260_ = v___x_4249_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4258_);
lean_ctor_set(v_reuseFailAlloc_4264_, 1, v_snd_4247_);
v___x_4260_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
lean_object* v___x_4262_; 
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v___x_4260_);
v___x_4262_ = v___x_4256_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; 
lean_del_object(v___x_4256_);
lean_dec(v_snd_4247_);
v_a_4265_ = lean_ctor_get(v_a_4254_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v_a_4254_, 1);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 1, v_a_4265_);
lean_ctor_set(v___x_4249_, 0, v___x_4251_);
v___x_4267_ = v___x_4249_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4251_);
lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_a_4265_);
v___x_4267_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
size_t v___x_4268_; size_t v___x_4269_; 
v___x_4268_ = ((size_t)1ULL);
v___x_4269_ = lean_usize_add(v_i_4240_, v___x_4268_);
v_i_4240_ = v___x_4269_;
v_b_4241_ = v___x_4267_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_del_object(v___x_4249_);
lean_dec(v_snd_4247_);
lean_dec_ref(v___x_4236_);
lean_dec(v_stx_4233_);
v_a_4273_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4253_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4253_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4283_, lean_object* v_stx_4284_, lean_object* v___x_4285_, lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v___x_4288_, lean_object* v_as_4289_, lean_object* v_sz_4290_, lean_object* v_i_4291_, lean_object* v_b_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
size_t v_sz_boxed_4296_; size_t v_i_boxed_4297_; lean_object* v_res_4298_; 
v_sz_boxed_4296_ = lean_unbox_usize(v_sz_4290_);
lean_dec(v_sz_4290_);
v_i_boxed_4297_ = lean_unbox_usize(v_i_4291_);
lean_dec(v_i_4291_);
v_res_4298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4283_, v_stx_4284_, v___x_4285_, v___x_4286_, v___x_4287_, v___x_4288_, v_as_4289_, v_sz_boxed_4296_, v_i_boxed_4297_, v_b_4292_, v___y_4293_, v___y_4294_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v_as_4289_);
lean_dec(v___x_4288_);
lean_dec_ref(v___x_4286_);
lean_dec_ref(v___x_4285_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4299_, lean_object* v_stx_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v___x_4303_, lean_object* v___x_4304_, lean_object* v_n_4305_, lean_object* v_b_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4299_, v_stx_4300_, v___x_4301_, v___x_4302_, v___x_4303_, v___x_4304_, v_n_4305_, v_b_4306_, v___y_4307_, v___y_4308_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec_ref(v_n_4305_);
lean_dec(v___x_4304_);
lean_dec_ref(v___x_4302_);
lean_dec_ref(v___x_4301_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4311_, lean_object* v___x_4312_, lean_object* v_stx_4313_, lean_object* v___x_4314_, lean_object* v___x_4315_, lean_object* v_t_4316_, lean_object* v_init_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_root_4321_; lean_object* v_tail_4322_; lean_object* v___x_4323_; 
v_root_4321_ = lean_ctor_get(v_t_4316_, 0);
v_tail_4322_ = lean_ctor_get(v_t_4316_, 1);
lean_inc_ref(v___x_4311_);
lean_inc(v_stx_4313_);
v___x_4323_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4317_, v_stx_4313_, v___x_4314_, v___x_4315_, v___x_4311_, v___x_4312_, v_root_4321_, v_init_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4360_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4360_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4360_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
if (lean_obj_tag(v_a_4324_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4330_; 
lean_dec(v_stx_4313_);
lean_dec_ref(v___x_4311_);
v_a_4328_ = lean_ctor_get(v_a_4324_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v_a_4324_, 1);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v_a_4328_);
v___x_4330_ = v___x_4326_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; size_t v_sz_4335_; size_t v___x_4336_; lean_object* v___x_4337_; 
lean_del_object(v___x_4326_);
v_a_4332_ = lean_ctor_get(v_a_4324_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v_a_4324_, 1);
v___x_4333_ = lean_box(0);
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v_a_4332_);
v_sz_4335_ = lean_array_size(v_tail_4322_);
v___x_4336_ = ((size_t)0ULL);
v___x_4337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4313_, v___x_4314_, v___x_4315_, v___x_4311_, v___x_4312_, v_tail_4322_, v_sz_4335_, v___x_4336_, v___x_4334_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4351_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4340_ = v___x_4337_;
v_isShared_4341_ = v_isSharedCheck_4351_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4337_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4351_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v_fst_4342_; 
v_fst_4342_ = lean_ctor_get(v_a_4338_, 0);
if (lean_obj_tag(v_fst_4342_) == 0)
{
lean_object* v_snd_4343_; lean_object* v___x_4345_; 
v_snd_4343_ = lean_ctor_get(v_a_4338_, 1);
lean_inc(v_snd_4343_);
lean_dec(v_a_4338_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v_snd_4343_);
v___x_4345_ = v___x_4340_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_snd_4343_);
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
lean_object* v_val_4347_; lean_object* v___x_4349_; 
lean_inc_ref(v_fst_4342_);
lean_dec(v_a_4338_);
v_val_4347_ = lean_ctor_get(v_fst_4342_, 0);
lean_inc(v_val_4347_);
lean_dec_ref_known(v_fst_4342_, 1);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v_val_4347_);
v___x_4349_ = v___x_4340_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_val_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
v_a_4352_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4337_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4337_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
lean_dec(v_stx_4313_);
lean_dec_ref(v___x_4311_);
v_a_4361_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4323_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4323_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4369_, lean_object* v___x_4370_, lean_object* v_stx_4371_, lean_object* v___x_4372_, lean_object* v___x_4373_, lean_object* v_t_4374_, lean_object* v_init_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4369_, v___x_4370_, v_stx_4371_, v___x_4372_, v___x_4373_, v_t_4374_, v_init_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec_ref(v_t_4374_);
lean_dec_ref(v___x_4373_);
lean_dec_ref(v___x_4372_);
lean_dec(v___x_4370_);
return v_res_4379_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4382_ = l_Lean_stringToMessageData(v___x_4381_);
return v___x_4382_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4387_ = l_Lean_stringToMessageData(v___x_4386_);
return v___x_4387_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4390_ = l_Lean_stringToMessageData(v___x_4389_);
return v___x_4390_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4393_ = l_Lean_stringToMessageData(v___x_4392_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v_scopes_4403_; lean_object* v___x_4404_; lean_object* v_opts_4405_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; uint8_t v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4437_; lean_object* v___y_4438_; uint8_t v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4446_; uint8_t v___y_4447_; lean_object* v___y_4448_; uint8_t v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4459_; uint8_t v___y_4460_; uint8_t v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4463_; lean_object* v___y_4464_; uint8_t v___y_4473_; uint8_t v___y_4474_; uint8_t v___y_4475_; uint8_t v___y_4509_; lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4401_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4402_ = lean_st_ref_get(v___y_4396_);
v_scopes_4403_ = lean_ctor_get(v___x_4402_, 2);
lean_inc(v_scopes_4403_);
lean_dec(v___x_4402_);
v___x_4404_ = l_List_head_x21___redArg(v___x_4401_, v_scopes_4403_);
lean_dec(v_scopes_4403_);
v_opts_4405_ = lean_ctor_get(v___x_4404_, 1);
lean_inc_ref(v_opts_4405_);
lean_dec(v___x_4404_);
v___x_4516_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4517_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4405_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4518_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4519_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4405_, v___x_4518_);
v___y_4509_ = v___x_4519_;
goto v___jp_4508_;
}
else
{
v___y_4509_ = v___x_4517_;
goto v___jp_4508_;
}
v___jp_4398_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = lean_box(0);
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
return v___x_4400_;
}
v___jp_4406_:
{
lean_object* v___x_4411_; lean_object* v_line_4412_; lean_object* v___x_4413_; lean_object* v_messages_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v_a_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
lean_inc_ref_n(v___y_4409_, 2);
v___x_4411_ = l_Lean_FileMap_toPosition(v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
v_line_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_line_4412_);
lean_dec_ref(v___x_4411_);
v___x_4413_ = lean_st_ref_get(v___y_4408_);
v_messages_4414_ = lean_ctor_get(v___x_4413_, 1);
lean_inc_ref(v_messages_4414_);
lean_dec(v___x_4413_);
v___x_4415_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4414_);
v___x_4416_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4408_);
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref(v___x_4416_);
v___x_4418_ = lean_box(0);
v___x_4419_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4409_, v_line_4412_, v_stx_4394_, v_opts_4405_, v___x_4415_, v_a_4417_, v___x_4418_, v___y_4407_, v___y_4408_);
lean_dec(v_a_4417_);
lean_dec_ref(v___x_4415_);
lean_dec_ref(v_opts_4405_);
lean_dec(v_line_4412_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; 
v_unused_4427_ = lean_ctor_get(v___x_4419_, 0);
lean_dec(v_unused_4427_);
v___x_4421_ = v___x_4419_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_dec(v___x_4419_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4418_);
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4418_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
else
{
return v___x_4419_;
}
}
v___jp_4428_:
{
lean_object* v_fileMap_4432_; lean_object* v___x_4433_; 
v_fileMap_4432_ = lean_ctor_get(v___y_4430_, 1);
v___x_4433_ = l_Lean_Syntax_getPos_x3f(v_stx_4394_, v___y_4429_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v___x_4434_; 
v___x_4434_ = lean_unsigned_to_nat(0u);
v___y_4407_ = v___y_4430_;
v___y_4408_ = v___y_4431_;
v___y_4409_ = v_fileMap_4432_;
v___y_4410_ = v___x_4434_;
goto v___jp_4406_;
}
else
{
lean_object* v_val_4435_; 
v_val_4435_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_val_4435_);
lean_dec_ref_known(v___x_4433_, 1);
v___y_4407_ = v___y_4430_;
v___y_4408_ = v___y_4431_;
v___y_4409_ = v_fileMap_4432_;
v___y_4410_ = v_val_4435_;
goto v___jp_4406_;
}
}
v___jp_4436_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
lean_inc_ref(v___y_4440_);
v___x_4441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___y_4440_);
v___x_4442_ = l_Lean_MessageData_ofFormat(v___x_4441_);
v___x_4443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___y_4437_);
lean_ctor_set(v___x_4443_, 1, v___x_4442_);
lean_inc(v___y_4438_);
v___x_4444_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___y_4438_, v___x_4443_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_dec_ref_known(v___x_4444_, 1);
v___y_4429_ = v___y_4439_;
v___y_4430_ = v___y_4395_;
v___y_4431_ = v___y_4396_;
goto v___jp_4428_;
}
else
{
lean_dec_ref(v_opts_4405_);
lean_dec(v_stx_4394_);
return v___x_4444_;
}
}
v___jp_4445_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_inc_ref(v___y_4450_);
v___x_4451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___y_4450_);
v___x_4452_ = l_Lean_MessageData_ofFormat(v___x_4451_);
v___x_4453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___y_4448_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
v___x_4454_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4453_);
lean_ctor_set(v___x_4455_, 1, v___x_4454_);
if (v___y_4447_ == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4437_ = v___x_4455_;
v___y_4438_ = v___y_4446_;
v___y_4439_ = v___y_4449_;
v___y_4440_ = v___x_4456_;
goto v___jp_4436_;
}
else
{
lean_object* v___x_4457_; 
v___x_4457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4437_ = v___x_4455_;
v___y_4438_ = v___y_4446_;
v___y_4439_ = v___y_4449_;
v___y_4440_ = v___x_4457_;
goto v___jp_4436_;
}
}
v___jp_4458_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_inc_ref(v___y_4464_);
v___x_4465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4465_, 0, v___y_4464_);
v___x_4466_ = l_Lean_MessageData_ofFormat(v___x_4465_);
lean_inc_ref(v___y_4462_);
v___x_4467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___y_4462_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
v___x_4468_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4467_);
lean_ctor_set(v___x_4469_, 1, v___x_4468_);
if (v___y_4460_ == 0)
{
lean_object* v___x_4470_; 
v___x_4470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4446_ = v___y_4459_;
v___y_4447_ = v___y_4461_;
v___y_4448_ = v___x_4469_;
v___y_4449_ = v___y_4463_;
v___y_4450_ = v___x_4470_;
goto v___jp_4445_;
}
else
{
lean_object* v___x_4471_; 
v___x_4471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4446_ = v___y_4459_;
v___y_4447_ = v___y_4461_;
v___y_4448_ = v___x_4469_;
v___y_4449_ = v___y_4463_;
v___y_4450_ = v___x_4471_;
goto v___jp_4445_;
}
}
v___jp_4472_:
{
lean_object* v___x_4476_; lean_object* v_a_4477_; uint8_t v___x_4478_; 
v___x_4476_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4394_, v___y_4395_, v___y_4396_);
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref(v___x_4476_);
v___x_4478_ = lean_unbox(v_a_4477_);
if (v___x_4478_ == 0)
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v_scopes_4483_; lean_object* v___x_4484_; lean_object* v_opts_4485_; uint8_t v_hasTrace_4486_; 
v___x_4479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4480_ = l_Lean_inheritedTraceOptions;
v___x_4481_ = lean_st_ref_get(v___x_4480_);
v___x_4482_ = lean_st_ref_get(v___y_4396_);
v_scopes_4483_ = lean_ctor_get(v___x_4482_, 2);
lean_inc(v_scopes_4483_);
lean_dec(v___x_4482_);
v___x_4484_ = l_List_head_x21___redArg(v___x_4401_, v_scopes_4483_);
lean_dec(v_scopes_4483_);
v_opts_4485_ = lean_ctor_get(v___x_4484_, 1);
lean_inc_ref(v_opts_4485_);
lean_dec(v___x_4484_);
v_hasTrace_4486_ = lean_ctor_get_uint8(v_opts_4485_, sizeof(void*)*1);
if (v_hasTrace_4486_ == 0)
{
uint8_t v___x_4487_; 
lean_dec_ref(v_opts_4485_);
lean_dec(v___x_4481_);
v___x_4487_ = lean_unbox(v_a_4477_);
lean_dec(v_a_4477_);
v___y_4429_ = v___x_4487_;
v___y_4430_ = v___y_4395_;
v___y_4431_ = v___y_4396_;
goto v___jp_4428_;
}
else
{
lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4488_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4481_, v_opts_4485_, v___x_4488_);
lean_dec_ref(v_opts_4485_);
lean_dec(v___x_4481_);
if (v___x_4489_ == 0)
{
uint8_t v___x_4490_; 
v___x_4490_ = lean_unbox(v_a_4477_);
lean_dec(v_a_4477_);
v___y_4429_ = v___x_4490_;
v___y_4430_ = v___y_4395_;
v___y_4431_ = v___y_4396_;
goto v___jp_4428_;
}
else
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4475_ == 0)
{
lean_object* v___x_4492_; uint8_t v___x_4493_; 
v___x_4492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4493_ = lean_unbox(v_a_4477_);
lean_dec(v_a_4477_);
v___y_4459_ = v___x_4479_;
v___y_4460_ = v___y_4474_;
v___y_4461_ = v___y_4473_;
v___y_4462_ = v___x_4491_;
v___y_4463_ = v___x_4493_;
v___y_4464_ = v___x_4492_;
goto v___jp_4458_;
}
else
{
lean_object* v___x_4494_; uint8_t v___x_4495_; 
v___x_4494_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4495_ = lean_unbox(v_a_4477_);
lean_dec(v_a_4477_);
v___y_4459_ = v___x_4479_;
v___y_4460_ = v___y_4474_;
v___y_4461_ = v___y_4473_;
v___y_4462_ = v___x_4491_;
v___y_4463_ = v___x_4495_;
v___y_4464_ = v___x_4494_;
goto v___jp_4458_;
}
}
}
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v_scopes_4500_; lean_object* v___x_4501_; lean_object* v_opts_4502_; uint8_t v_hasTrace_4503_; 
lean_dec(v_a_4477_);
lean_dec_ref(v_opts_4405_);
lean_dec(v_stx_4394_);
v___x_4496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4497_ = l_Lean_inheritedTraceOptions;
v___x_4498_ = lean_st_ref_get(v___x_4497_);
v___x_4499_ = lean_st_ref_get(v___y_4396_);
v_scopes_4500_ = lean_ctor_get(v___x_4499_, 2);
lean_inc(v_scopes_4500_);
lean_dec(v___x_4499_);
v___x_4501_ = l_List_head_x21___redArg(v___x_4401_, v_scopes_4500_);
lean_dec(v_scopes_4500_);
v_opts_4502_ = lean_ctor_get(v___x_4501_, 1);
lean_inc_ref(v_opts_4502_);
lean_dec(v___x_4501_);
v_hasTrace_4503_ = lean_ctor_get_uint8(v_opts_4502_, sizeof(void*)*1);
if (v_hasTrace_4503_ == 0)
{
lean_dec_ref(v_opts_4502_);
lean_dec(v___x_4498_);
goto v___jp_4398_;
}
else
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4505_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4498_, v_opts_4502_, v___x_4504_);
lean_dec_ref(v_opts_4502_);
lean_dec(v___x_4498_);
if (v___x_4505_ == 0)
{
goto v___jp_4398_;
}
else
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4507_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4496_, v___x_4506_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_dec_ref_known(v___x_4507_, 1);
goto v___jp_4398_;
}
else
{
return v___x_4507_;
}
}
}
}
}
v___jp_4508_:
{
lean_object* v___x_4510_; uint8_t v___x_4511_; lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4510_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4511_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4405_, v___x_4510_);
v___x_4512_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4513_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4405_, v___x_4512_);
if (v___y_4509_ == 0)
{
if (v___x_4511_ == 0)
{
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
lean_dec_ref(v_opts_4405_);
lean_dec(v_stx_4394_);
v___x_4514_ = lean_box(0);
v___x_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
return v___x_4515_;
}
else
{
v___y_4473_ = v___x_4513_;
v___y_4474_ = v___x_4511_;
v___y_4475_ = v___y_4509_;
goto v___jp_4472_;
}
}
else
{
v___y_4473_ = v___x_4513_;
v___y_4474_ = v___x_4511_;
v___y_4475_ = v___y_4509_;
goto v___jp_4472_;
}
}
else
{
v___y_4473_ = v___x_4513_;
v___y_4474_ = v___x_4511_;
v___y_4475_ = v___y_4509_;
goto v___jp_4472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4538_ = l_Lean_Elab_Command_addLinter(v___x_4537_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4540_;
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
