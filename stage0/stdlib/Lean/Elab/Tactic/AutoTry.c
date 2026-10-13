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
uint8_t v___x_748_; 
v___x_748_ = lean_nat_dec_le(v___x_746_, v___x_746_);
if (v___x_748_ == 0)
{
if (v___x_747_ == 0)
{
lean_dec(v_nc_x3f_719_);
lean_dec(v_mc_x3f_718_);
return v___x_744_;
}
else
{
size_t v___x_749_; size_t v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((size_t)0ULL);
v___x_750_ = lean_usize_of_nat(v___x_746_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_718_, v_nc_x3f_719_, v_children_743_, v___x_749_, v___x_750_, v___x_744_);
return v___x_751_;
}
}
else
{
size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_746_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_718_, v_nc_x3f_719_, v_children_743_, v___x_752_, v___x_753_, v___x_744_);
return v___x_754_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_718_) == 1)
{
if (lean_obj_tag(v_nc_x3f_719_) == 1)
{
lean_object* v_a_755_; lean_object* v_val_756_; lean_object* v_val_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_a_755_ = lean_ctor_get(v_msg_720_, 0);
v_val_756_ = lean_ctor_get(v_mc_x3f_718_, 0);
lean_inc(v_val_756_);
lean_dec_ref_known(v_mc_x3f_718_, 1);
v_val_757_ = lean_ctor_get(v_nc_x3f_719_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v_nc_x3f_719_, 1);
lean_inc(v_a_755_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_val_757_);
lean_ctor_set(v___x_758_, 1, v_a_755_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_val_756_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_array_push(v_acc_721_, v___x_759_);
return v___x_760_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_761_, lean_object* v_nc_x3f_762_, lean_object* v_as_763_, size_t v_i_764_, size_t v_stop_765_, lean_object* v_b_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = lean_usize_dec_eq(v_i_764_, v_stop_765_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; size_t v___x_770_; size_t v___x_771_; 
v___x_768_ = lean_array_uget_borrowed(v_as_763_, v_i_764_);
lean_inc(v_nc_x3f_762_);
lean_inc(v_mc_x3f_761_);
v___x_769_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_761_, v_nc_x3f_762_, v___x_768_, v_b_766_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_add(v_i_764_, v___x_770_);
v_i_764_ = v___x_771_;
v_b_766_ = v___x_769_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_762_);
lean_dec(v_mc_x3f_761_);
return v_b_766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_773_, lean_object* v_nc_x3f_774_, lean_object* v_as_775_, lean_object* v_i_776_, lean_object* v_stop_777_, lean_object* v_b_778_){
_start:
{
size_t v_i_boxed_779_; size_t v_stop_boxed_780_; lean_object* v_res_781_; 
v_i_boxed_779_ = lean_unbox_usize(v_i_776_);
lean_dec(v_i_776_);
v_stop_boxed_780_ = lean_unbox_usize(v_stop_777_);
lean_dec(v_stop_777_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_773_, v_nc_x3f_774_, v_as_775_, v_i_boxed_779_, v_stop_boxed_780_, v_b_778_);
lean_dec_ref(v_as_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_782_, lean_object* v_nc_x3f_783_, lean_object* v_msg_784_, lean_object* v_acc_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_782_, v_nc_x3f_783_, v_msg_784_, v_acc_785_);
lean_dec_ref(v_msg_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_box(0);
v___x_791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_792_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_790_, v___x_790_, v_msg_789_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_793_);
lean_dec_ref(v_msg_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_797_, lean_object* v_stx_798_){
_start:
{
lean_object* v___x_799_; 
lean_inc(v_stx_798_);
v___x_799_ = l_Lean_Syntax_getKind(v_stx_798_);
if (lean_obj_tag(v___x_799_) == 1)
{
lean_object* v_pre_800_; 
v_pre_800_ = lean_ctor_get(v___x_799_, 0);
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
lean_inc(v_pre_802_);
if (lean_obj_tag(v_pre_802_) == 1)
{
lean_object* v_pre_803_; 
v_pre_803_ = lean_ctor_get(v_pre_802_, 0);
if (lean_obj_tag(v_pre_803_) == 0)
{
lean_object* v_str_804_; lean_object* v_str_805_; lean_object* v_str_806_; lean_object* v_str_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_str_804_ = lean_ctor_get(v___x_799_, 1);
lean_inc_ref(v_str_804_);
lean_dec_ref_known(v___x_799_, 2);
v_str_805_ = lean_ctor_get(v_pre_800_, 1);
lean_inc_ref(v_str_805_);
lean_dec_ref_known(v_pre_800_, 2);
v_str_806_ = lean_ctor_get(v_pre_801_, 1);
lean_inc_ref(v_str_806_);
lean_dec_ref_known(v_pre_801_, 2);
v_str_807_ = lean_ctor_get(v_pre_802_, 1);
lean_inc_ref(v_str_807_);
lean_dec_ref_known(v_pre_802_, 2);
v___x_808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_809_ = lean_string_dec_eq(v_str_807_, v___x_808_);
lean_dec_ref(v_str_807_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec_ref(v_str_806_);
lean_dec_ref(v_str_805_);
lean_dec_ref(v_str_804_);
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_810_ = lean_box(0);
return v___x_810_;
}
else
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_812_ = lean_string_dec_eq(v_str_806_, v___x_811_);
lean_dec_ref(v_str_806_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec_ref(v_str_805_);
lean_dec_ref(v_str_804_);
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_813_ = lean_box(0);
return v___x_813_;
}
else
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_815_ = lean_string_dec_eq(v_str_805_, v___x_814_);
lean_dec_ref(v_str_805_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v_str_804_);
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_816_ = lean_box(0);
return v___x_816_;
}
else
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_818_ = lean_string_dec_eq(v_str_804_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_820_ = lean_string_dec_eq(v_str_804_, v___x_819_);
lean_dec_ref(v_str_804_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_821_ = lean_box(0);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v_body_823_; lean_object* v___y_825_; lean_object* v___x_828_; 
v___x_822_ = lean_unsigned_to_nat(1u);
v_body_823_ = l_Lean_Syntax_getArg(v_stx_798_, v___x_822_);
v___x_828_ = l_Lean_Syntax_getTailPos_x3f(v_body_823_, v___x_818_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_unsigned_to_nat(2u);
v___x_830_ = l_Lean_Syntax_getArg(v_stx_798_, v___x_829_);
lean_dec(v_stx_798_);
v___x_831_ = l_Lean_Syntax_getPos_x3f(v___x_830_, v___x_818_);
lean_dec(v___x_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_stop_832_; 
v_stop_832_ = lean_ctor_get(v_range_797_, 1);
lean_inc(v_stop_832_);
lean_dec_ref(v_range_797_);
v___y_825_ = v_stop_832_;
goto v___jp_824_;
}
else
{
lean_object* v_val_833_; 
lean_dec_ref(v_range_797_);
v_val_833_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v___x_831_, 1);
v___y_825_ = v_val_833_;
goto v___jp_824_;
}
}
else
{
lean_object* v_val_834_; 
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v_val_834_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v___x_828_, 1);
v___y_825_ = v_val_834_;
goto v___jp_824_;
}
v___jp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_body_823_);
lean_ctor_set(v___x_826_, 1, v___y_825_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
else
{
lean_object* v___x_835_; lean_object* v_body_836_; lean_object* v___y_838_; uint8_t v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v_str_804_);
v___x_835_ = lean_unsigned_to_nat(0u);
v_body_836_ = l_Lean_Syntax_getArg(v_stx_798_, v___x_835_);
lean_dec(v_stx_798_);
v___x_841_ = 0;
v___x_842_ = l_Lean_Syntax_getTailPos_x3f(v_body_836_, v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_stop_843_; 
v_stop_843_ = lean_ctor_get(v_range_797_, 1);
lean_inc(v_stop_843_);
lean_dec_ref(v_range_797_);
v___y_838_ = v_stop_843_;
goto v___jp_837_;
}
else
{
lean_object* v_val_844_; 
lean_dec_ref(v_range_797_);
v_val_844_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v___x_842_, 1);
v___y_838_ = v_val_844_;
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
}
}
}
else
{
lean_object* v___x_845_; 
lean_dec_ref_known(v_pre_802_, 2);
lean_dec_ref_known(v_pre_801_, 2);
lean_dec_ref_known(v_pre_800_, 2);
lean_dec_ref_known(v___x_799_, 2);
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_845_ = lean_box(0);
return v___x_845_;
}
}
else
{
lean_object* v___x_846_; 
lean_dec_ref_known(v_pre_801_, 2);
lean_dec(v_pre_802_);
lean_dec_ref_known(v_pre_800_, 2);
lean_dec_ref_known(v___x_799_, 2);
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_846_ = lean_box(0);
return v___x_846_;
}
}
else
{
lean_object* v___x_847_; 
lean_dec_ref_known(v_pre_800_, 2);
lean_dec(v_pre_801_);
lean_dec_ref_known(v___x_799_, 2);
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_847_ = lean_box(0);
return v___x_847_;
}
}
else
{
lean_object* v___x_848_; 
lean_dec(v_pre_800_);
lean_dec_ref_known(v___x_799_, 2);
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_848_ = lean_box(0);
return v___x_848_;
}
}
else
{
lean_object* v___x_849_; 
lean_dec(v___x_799_);
lean_dec(v_stx_798_);
lean_dec_ref(v_range_797_);
v___x_849_ = lean_box(0);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_853_, lean_object* v_stx_854_){
_start:
{
lean_object* v___x_855_; 
lean_inc(v_stx_854_);
lean_inc_ref(v_range_853_);
v___x_855_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_853_, v_stx_854_);
if (lean_obj_tag(v___x_855_) == 1)
{
lean_dec(v_stx_854_);
lean_dec_ref(v_range_853_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; size_t v_sz_859_; size_t v___x_860_; lean_object* v___x_861_; lean_object* v_fst_862_; 
lean_dec(v___x_855_);
v___x_856_ = l_Lean_Syntax_getArgs(v_stx_854_);
lean_dec(v_stx_854_);
v___x_857_ = lean_box(0);
v___x_858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_859_ = lean_array_size(v___x_856_);
v___x_860_ = ((size_t)0ULL);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_853_, v___x_856_, v_sz_859_, v___x_860_, v___x_858_);
lean_dec_ref(v___x_856_);
v_fst_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_fst_862_);
lean_dec_ref(v___x_861_);
if (lean_obj_tag(v_fst_862_) == 0)
{
return v___x_857_;
}
else
{
lean_object* v_val_863_; 
v_val_863_ = lean_ctor_get(v_fst_862_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v_fst_862_, 1);
return v_val_863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_864_, lean_object* v_as_865_, size_t v_sz_866_, size_t v_i_867_, lean_object* v_b_868_){
_start:
{
uint8_t v___x_869_; 
v___x_869_ = lean_usize_dec_lt(v_i_867_, v_sz_866_);
if (v___x_869_ == 0)
{
lean_dec_ref(v_range_864_);
lean_inc_ref(v_b_868_);
return v_b_868_;
}
else
{
lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_872_; 
v___x_870_ = lean_box(0);
v_a_871_ = lean_array_uget_borrowed(v_as_865_, v_i_867_);
lean_inc(v_a_871_);
lean_inc_ref(v_range_864_);
v___x_872_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_864_, v_a_871_);
if (lean_obj_tag(v___x_872_) == 1)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref(v_range_864_);
v___x_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_870_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; size_t v___x_876_; size_t v___x_877_; 
lean_dec(v___x_872_);
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_867_, v___x_876_);
v_i_867_ = v___x_877_;
v_b_868_ = v___x_875_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_879_, lean_object* v_as_880_, lean_object* v_sz_881_, lean_object* v_i_882_, lean_object* v_b_883_){
_start:
{
size_t v_sz_boxed_884_; size_t v_i_boxed_885_; lean_object* v_res_886_; 
v_sz_boxed_884_ = lean_unbox_usize(v_sz_881_);
lean_dec(v_sz_881_);
v_i_boxed_885_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_879_, v_as_880_, v_sz_boxed_884_, v_i_boxed_885_, v_b_883_);
lean_dec_ref(v_b_883_);
lean_dec_ref(v_as_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_887_, lean_object* v_stx_888_){
_start:
{
uint8_t v___x_889_; lean_object* v___x_890_; 
v___x_889_ = 0;
v___x_890_ = l_Lean_Syntax_getRange_x3f(v_stx_888_, v___x_889_);
if (lean_obj_tag(v___x_890_) == 1)
{
lean_object* v_val_891_; uint8_t v___x_892_; 
v_val_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = l_Lean_Syntax_Range_includes(v_val_891_, v_range_887_, v___x_889_, v___x_889_);
lean_dec(v_val_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
lean_dec(v_stx_888_);
lean_dec_ref(v_range_887_);
v___x_893_ = lean_box(0);
return v___x_893_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; size_t v_sz_896_; size_t v___x_897_; lean_object* v___x_898_; lean_object* v_fst_899_; 
v___x_894_ = l_Lean_Syntax_getArgs(v_stx_888_);
v___x_895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_896_ = lean_array_size(v___x_894_);
v___x_897_ = ((size_t)0ULL);
lean_inc_ref(v_range_887_);
v___x_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_887_, v___x_894_, v_sz_896_, v___x_897_, v___x_895_);
lean_dec_ref(v___x_894_);
v_fst_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_fst_899_);
lean_dec_ref(v___x_898_);
if (lean_obj_tag(v_fst_899_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_887_, v_stx_888_);
return v___x_900_;
}
else
{
lean_object* v_val_901_; 
lean_dec(v_stx_888_);
lean_dec_ref(v_range_887_);
v_val_901_ = lean_ctor_get(v_fst_899_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v_fst_899_, 1);
return v_val_901_;
}
}
}
else
{
lean_object* v___x_902_; 
lean_dec(v___x_890_);
lean_dec(v_stx_888_);
lean_dec_ref(v_range_887_);
v___x_902_ = lean_box(0);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_903_, lean_object* v_as_904_, size_t v_sz_905_, size_t v_i_906_, lean_object* v_b_907_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = lean_usize_dec_lt(v_i_906_, v_sz_905_);
if (v___x_908_ == 0)
{
lean_dec_ref(v_range_903_);
lean_inc_ref(v_b_907_);
return v_b_907_;
}
else
{
lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(0);
v_a_910_ = lean_array_uget_borrowed(v_as_904_, v_i_906_);
lean_inc(v_a_910_);
lean_inc_ref(v_range_903_);
v___x_911_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_903_, v_a_910_);
if (lean_obj_tag(v___x_911_) == 1)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref(v_range_903_);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_909_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; size_t v___x_915_; size_t v___x_916_; 
lean_dec(v___x_911_);
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_906_, v___x_915_);
v_i_906_ = v___x_916_;
v_b_907_ = v___x_914_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_918_, lean_object* v_as_919_, lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_b_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_918_, v_as_919_, v_sz_boxed_923_, v_i_boxed_924_, v_b_922_);
lean_dec_ref(v_b_922_);
lean_dec_ref(v_as_919_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_926_, lean_object* v_range_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_927_, v_cmd_926_);
return v___x_928_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_opts_929_, lean_object* v_opt_930_){
_start:
{
lean_object* v_name_931_; lean_object* v_defValue_932_; lean_object* v_map_933_; lean_object* v___x_934_; 
v_name_931_ = lean_ctor_get(v_opt_930_, 0);
v_defValue_932_ = lean_ctor_get(v_opt_930_, 1);
v_map_933_ = lean_ctor_get(v_opts_929_, 0);
v___x_934_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_933_, v_name_931_);
if (lean_obj_tag(v___x_934_) == 0)
{
uint8_t v___x_935_; 
v___x_935_ = lean_unbox(v_defValue_932_);
return v___x_935_;
}
else
{
lean_object* v_val_936_; 
v_val_936_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_934_, 1);
if (lean_obj_tag(v_val_936_) == 1)
{
uint8_t v_v_937_; 
v_v_937_ = lean_ctor_get_uint8(v_val_936_, 0);
lean_dec_ref_known(v_val_936_, 0);
return v_v_937_;
}
else
{
uint8_t v___x_938_; 
lean_dec(v_val_936_);
v___x_938_ = lean_unbox(v_defValue_932_);
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_opts_939_, lean_object* v_opt_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_939_, v_opt_940_);
lean_dec_ref(v_opt_940_);
lean_dec_ref(v_opts_939_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_943_, lean_object* v_info_944_, lean_object* v_acc_945_){
_start:
{
if (lean_obj_tag(v_info_944_) == 0)
{
lean_object* v_i_946_; lean_object* v_toElabInfo_947_; lean_object* v_mctxBefore_948_; lean_object* v_goalsBefore_949_; lean_object* v_stx_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_968_; 
v_i_946_ = lean_ctor_get(v_info_944_, 0);
lean_inc_ref(v_i_946_);
lean_dec_ref_known(v_info_944_, 1);
v_toElabInfo_947_ = lean_ctor_get(v_i_946_, 0);
lean_inc_ref(v_toElabInfo_947_);
v_mctxBefore_948_ = lean_ctor_get(v_i_946_, 1);
lean_inc_ref(v_mctxBefore_948_);
v_goalsBefore_949_ = lean_ctor_get(v_i_946_, 2);
lean_inc(v_goalsBefore_949_);
lean_dec_ref(v_i_946_);
v_stx_950_ = lean_ctor_get(v_toElabInfo_947_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_toElabInfo_947_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_toElabInfo_947_, 0);
lean_dec(v_unused_969_);
v___x_952_ = v_toElabInfo_947_;
v_isShared_953_ = v_isSharedCheck_968_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_stx_950_);
lean_dec(v_toElabInfo_947_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_968_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
uint8_t v___x_954_; 
lean_inc(v_stx_950_);
v___x_954_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_950_);
if (v___x_954_ == 0)
{
lean_del_object(v___x_952_);
lean_dec(v_stx_950_);
lean_dec(v_goalsBefore_949_);
lean_dec_ref(v_mctxBefore_948_);
return v_acc_945_;
}
else
{
lean_object* v___x_955_; 
v___x_955_ = l_List_head_x3f___redArg(v_goalsBefore_949_);
lean_dec(v_goalsBefore_949_);
if (lean_obj_tag(v___x_955_) == 1)
{
lean_object* v_toCommandContextInfo_956_; lean_object* v_val_957_; lean_object* v_env_958_; lean_object* v_options_959_; lean_object* v_currNamespace_960_; lean_object* v_openDecls_961_; lean_object* v_namingCtx_963_; 
v_toCommandContextInfo_956_ = lean_ctor_get(v_ctx_943_, 0);
v_val_957_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v___x_955_, 1);
v_env_958_ = lean_ctor_get(v_toCommandContextInfo_956_, 0);
v_options_959_ = lean_ctor_get(v_toCommandContextInfo_956_, 4);
v_currNamespace_960_ = lean_ctor_get(v_toCommandContextInfo_956_, 5);
v_openDecls_961_ = lean_ctor_get(v_toCommandContextInfo_956_, 6);
lean_inc(v_openDecls_961_);
lean_inc(v_currNamespace_960_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_openDecls_961_);
lean_ctor_set(v___x_952_, 0, v_currNamespace_960_);
v_namingCtx_963_ = v___x_952_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_currNamespace_960_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_openDecls_961_);
v_namingCtx_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_box(1);
lean_inc_ref(v_options_959_);
lean_inc_ref(v_env_958_);
v___x_965_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v_stx_950_);
lean_ctor_set(v___x_965_, 2, v_env_958_);
lean_ctor_set(v___x_965_, 3, v_mctxBefore_948_);
lean_ctor_set(v___x_965_, 4, v_options_959_);
lean_ctor_set(v___x_965_, 5, v_namingCtx_963_);
lean_ctor_set(v___x_965_, 6, v_val_957_);
v___x_966_ = lean_array_push(v_acc_945_, v___x_965_);
return v___x_966_;
}
}
else
{
lean_dec(v___x_955_);
lean_del_object(v___x_952_);
lean_dec(v_stx_950_);
lean_dec_ref(v_mctxBefore_948_);
return v_acc_945_;
}
}
}
}
else
{
lean_dec_ref(v_info_944_);
return v_acc_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_970_, lean_object* v_info_971_, lean_object* v_acc_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_970_, v_info_971_, v_acc_972_);
lean_dec_ref(v_ctx_970_);
return v_res_973_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(lean_object* v_x_978_){
_start:
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1));
v___x_980_ = lean_name_eq(v_x_978_, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___boxed(lean_object* v_x_981_){
_start:
{
uint8_t v_res_982_; lean_object* v_r_983_; 
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(v_x_981_);
lean_dec(v_x_981_);
v_r_983_ = lean_box(v_res_982_);
return v_r_983_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(lean_object* v_a_984_, lean_object* v_x_985_){
_start:
{
if (lean_obj_tag(v_x_985_) == 0)
{
uint8_t v___x_986_; 
v___x_986_ = 0;
return v___x_986_;
}
else
{
lean_object* v_key_987_; lean_object* v_tail_988_; uint8_t v___y_990_; lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; uint8_t v___x_996_; 
v_key_987_ = lean_ctor_get(v_x_985_, 0);
v_tail_988_ = lean_ctor_get(v_x_985_, 2);
v_fst_992_ = lean_ctor_get(v_key_987_, 0);
v_snd_993_ = lean_ctor_get(v_key_987_, 1);
v_fst_994_ = lean_ctor_get(v_a_984_, 0);
v_snd_995_ = lean_ctor_get(v_a_984_, 1);
v___x_996_ = l_Lean_Syntax_instBEqRange_beq(v_fst_992_, v_fst_994_);
if (v___x_996_ == 0)
{
v___y_990_ = v___x_996_;
goto v___jp_989_;
}
else
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_instBEqMVarId_beq(v_snd_993_, v_snd_995_);
v___y_990_ = v___x_997_;
goto v___jp_989_;
}
v___jp_989_:
{
if (v___y_990_ == 0)
{
v_x_985_ = v_tail_988_;
goto _start;
}
else
{
return v___y_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg___boxed(lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_res_1000_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec_ref(v_a_998_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
return v_x_1002_;
}
else
{
lean_object* v_key_1004_; lean_object* v_value_1005_; lean_object* v_tail_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1033_; 
v_key_1004_ = lean_ctor_get(v_x_1003_, 0);
v_value_1005_ = lean_ctor_get(v_x_1003_, 1);
v_tail_1006_ = lean_ctor_get(v_x_1003_, 2);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_x_1003_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1008_ = v_x_1003_;
v_isShared_1009_ = v_isSharedCheck_1033_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_tail_1006_);
lean_inc(v_value_1005_);
lean_inc(v_key_1004_);
lean_dec(v_x_1003_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1033_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_fst_1010_; lean_object* v_snd_1011_; lean_object* v___x_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; uint64_t v_fold_1018_; uint64_t v___x_1019_; uint64_t v___x_1020_; uint64_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v_fst_1010_ = lean_ctor_get(v_key_1004_, 0);
v_snd_1011_ = lean_ctor_get(v_key_1004_, 1);
v___x_1012_ = lean_array_get_size(v_x_1002_);
v___x_1013_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1010_);
v___x_1014_ = l_Lean_instHashableMVarId_hash(v_snd_1011_);
v___x_1015_ = lean_uint64_mix_hash(v___x_1013_, v___x_1014_);
v___x_1016_ = 32ULL;
v___x_1017_ = lean_uint64_shift_right(v___x_1015_, v___x_1016_);
v_fold_1018_ = lean_uint64_xor(v___x_1015_, v___x_1017_);
v___x_1019_ = 16ULL;
v___x_1020_ = lean_uint64_shift_right(v_fold_1018_, v___x_1019_);
v___x_1021_ = lean_uint64_xor(v_fold_1018_, v___x_1020_);
v___x_1022_ = lean_uint64_to_usize(v___x_1021_);
v___x_1023_ = lean_usize_of_nat(v___x_1012_);
v___x_1024_ = ((size_t)1ULL);
v___x_1025_ = lean_usize_sub(v___x_1023_, v___x_1024_);
v___x_1026_ = lean_usize_land(v___x_1022_, v___x_1025_);
v___x_1027_ = lean_array_uget_borrowed(v_x_1002_, v___x_1026_);
lean_inc(v___x_1027_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 2, v___x_1027_);
v___x_1029_ = v___x_1008_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_key_1004_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_value_1005_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_array_uset(v_x_1002_, v___x_1026_, v___x_1029_);
v_x_1002_ = v___x_1030_;
v_x_1003_ = v_tail_1006_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1034_, lean_object* v_source_1035_, lean_object* v_target_1036_){
_start:
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = lean_array_get_size(v_source_1035_);
v___x_1038_ = lean_nat_dec_lt(v_i_1034_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec_ref(v_source_1035_);
lean_dec(v_i_1034_);
return v_target_1036_;
}
else
{
lean_object* v_es_1039_; lean_object* v___x_1040_; lean_object* v_source_1041_; lean_object* v_target_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v_es_1039_ = lean_array_fget(v_source_1035_, v_i_1034_);
v___x_1040_ = lean_box(0);
v_source_1041_ = lean_array_fset(v_source_1035_, v_i_1034_, v___x_1040_);
v_target_1042_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1036_, v_es_1039_);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_nat_add(v_i_1034_, v___x_1043_);
lean_dec(v_i_1034_);
v_i_1034_ = v___x_1044_;
v_source_1035_ = v_source_1041_;
v_target_1036_ = v_target_1042_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(lean_object* v_data_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v_nbuckets_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1047_ = lean_array_get_size(v_data_1046_);
v___x_1048_ = lean_unsigned_to_nat(2u);
v_nbuckets_1049_ = lean_nat_mul(v___x_1047_, v___x_1048_);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_mk_array(v_nbuckets_1049_, v___x_1051_);
v___x_1053_ = lean_array_propagate_mark(v_data_1046_, v___x_1052_);
v___x_1054_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v___x_1050_, v_data_1046_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v_m_1055_, lean_object* v_a_1056_, lean_object* v_b_1057_){
_start:
{
lean_object* v_size_1058_; lean_object* v_buckets_1059_; lean_object* v_fst_1060_; lean_object* v_snd_1061_; lean_object* v___x_1062_; uint64_t v___x_1063_; uint64_t v___x_1064_; uint64_t v___x_1065_; uint64_t v___x_1066_; uint64_t v___x_1067_; uint64_t v_fold_1068_; uint64_t v___x_1069_; uint64_t v___x_1070_; uint64_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; size_t v___x_1076_; lean_object* v_bkt_1077_; uint8_t v___x_1078_; 
v_size_1058_ = lean_ctor_get(v_m_1055_, 0);
v_buckets_1059_ = lean_ctor_get(v_m_1055_, 1);
v_fst_1060_ = lean_ctor_get(v_a_1056_, 0);
v_snd_1061_ = lean_ctor_get(v_a_1056_, 1);
v___x_1062_ = lean_array_get_size(v_buckets_1059_);
v___x_1063_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1060_);
v___x_1064_ = l_Lean_instHashableMVarId_hash(v_snd_1061_);
v___x_1065_ = lean_uint64_mix_hash(v___x_1063_, v___x_1064_);
v___x_1066_ = 32ULL;
v___x_1067_ = lean_uint64_shift_right(v___x_1065_, v___x_1066_);
v_fold_1068_ = lean_uint64_xor(v___x_1065_, v___x_1067_);
v___x_1069_ = 16ULL;
v___x_1070_ = lean_uint64_shift_right(v_fold_1068_, v___x_1069_);
v___x_1071_ = lean_uint64_xor(v_fold_1068_, v___x_1070_);
v___x_1072_ = lean_uint64_to_usize(v___x_1071_);
v___x_1073_ = lean_usize_of_nat(v___x_1062_);
v___x_1074_ = ((size_t)1ULL);
v___x_1075_ = lean_usize_sub(v___x_1073_, v___x_1074_);
v___x_1076_ = lean_usize_land(v___x_1072_, v___x_1075_);
v_bkt_1077_ = lean_array_uget_borrowed(v_buckets_1059_, v___x_1076_);
v___x_1078_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1056_, v_bkt_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1099_; 
lean_inc_ref(v_buckets_1059_);
lean_inc(v_size_1058_);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_m_1055_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1100_ = lean_ctor_get(v_m_1055_, 1);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_m_1055_, 0);
lean_dec(v_unused_1101_);
v___x_1080_ = v_m_1055_;
v_isShared_1081_ = v_isSharedCheck_1099_;
goto v_resetjp_1079_;
}
else
{
lean_dec(v_m_1055_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1099_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v_size_x27_1083_; lean_object* v___x_1084_; lean_object* v_buckets_x27_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1082_ = lean_unsigned_to_nat(1u);
v_size_x27_1083_ = lean_nat_add(v_size_1058_, v___x_1082_);
lean_dec(v_size_1058_);
lean_inc(v_bkt_1077_);
v___x_1084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1084_, 0, v_a_1056_);
lean_ctor_set(v___x_1084_, 1, v_b_1057_);
lean_ctor_set(v___x_1084_, 2, v_bkt_1077_);
v_buckets_x27_1085_ = lean_array_uset(v_buckets_1059_, v___x_1076_, v___x_1084_);
v___x_1086_ = lean_unsigned_to_nat(4u);
v___x_1087_ = lean_nat_mul(v_size_x27_1083_, v___x_1086_);
v___x_1088_ = lean_unsigned_to_nat(3u);
v___x_1089_ = lean_nat_div(v___x_1087_, v___x_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_array_get_size(v_buckets_x27_1085_);
v___x_1091_ = lean_nat_dec_le(v___x_1089_, v___x_1090_);
lean_dec(v___x_1089_);
if (v___x_1091_ == 0)
{
lean_object* v_val_1092_; lean_object* v___x_1094_; 
v_val_1092_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_buckets_x27_1085_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v_val_1092_);
lean_ctor_set(v___x_1080_, 0, v_size_x27_1083_);
v___x_1094_ = v___x_1080_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_size_x27_1083_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_val_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
else
{
lean_object* v___x_1097_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v_buckets_x27_1085_);
lean_ctor_set(v___x_1080_, 0, v_size_x27_1083_);
v___x_1097_ = v___x_1080_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_size_x27_1083_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_buckets_x27_1085_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_dec(v_b_1057_);
lean_dec_ref(v_a_1056_);
return v_m_1055_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_buckets_1104_; lean_object* v_fst_1105_; lean_object* v_snd_1106_; lean_object* v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; uint64_t v_fold_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; uint64_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_buckets_1104_ = lean_ctor_get(v_m_1102_, 1);
v_fst_1105_ = lean_ctor_get(v_a_1103_, 0);
v_snd_1106_ = lean_ctor_get(v_a_1103_, 1);
v___x_1107_ = lean_array_get_size(v_buckets_1104_);
v___x_1108_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1105_);
v___x_1109_ = l_Lean_instHashableMVarId_hash(v_snd_1106_);
v___x_1110_ = lean_uint64_mix_hash(v___x_1108_, v___x_1109_);
v___x_1111_ = 32ULL;
v___x_1112_ = lean_uint64_shift_right(v___x_1110_, v___x_1111_);
v_fold_1113_ = lean_uint64_xor(v___x_1110_, v___x_1112_);
v___x_1114_ = 16ULL;
v___x_1115_ = lean_uint64_shift_right(v_fold_1113_, v___x_1114_);
v___x_1116_ = lean_uint64_xor(v_fold_1113_, v___x_1115_);
v___x_1117_ = lean_uint64_to_usize(v___x_1116_);
v___x_1118_ = lean_usize_of_nat(v___x_1107_);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_sub(v___x_1118_, v___x_1119_);
v___x_1121_ = lean_usize_land(v___x_1117_, v___x_1120_);
v___x_1122_ = lean_array_uget_borrowed(v_buckets_1104_, v___x_1121_);
v___x_1123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1103_, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object* v_m_1124_, lean_object* v_a_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1124_, v_a_1125_);
lean_dec_ref(v_a_1125_);
lean_dec_ref(v_m_1124_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object* v___x_1128_, lean_object* v_fst_1129_, lean_object* v_snd_1130_, lean_object* v___x_1131_, lean_object* v_as_1132_, size_t v_sz_1133_, size_t v_i_1134_, lean_object* v_b_1135_){
_start:
{
lean_object* v_a_1138_; uint8_t v___x_1142_; 
v___x_1142_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec(v___x_1131_);
lean_dec(v_snd_1130_);
lean_dec(v_fst_1129_);
lean_dec_ref(v___x_1128_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_b_1135_);
return v___x_1143_;
}
else
{
lean_object* v_a_1144_; lean_object* v_snd_1145_; lean_object* v_fst_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1182_; 
v_a_1144_ = lean_array_uget(v_as_1132_, v_i_1134_);
v_snd_1145_ = lean_ctor_get(v_a_1144_, 1);
v_fst_1146_ = lean_ctor_get(v_a_1144_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_a_1144_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1148_ = v_a_1144_;
v_isShared_1149_ = v_isSharedCheck_1182_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_snd_1145_);
lean_inc(v_fst_1146_);
lean_dec(v_a_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1182_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1181_; 
v_fst_1150_ = lean_ctor_get(v_snd_1145_, 0);
v_snd_1151_ = lean_ctor_get(v_snd_1145_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_snd_1145_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1153_ = v_snd_1145_;
v_isShared_1154_ = v_isSharedCheck_1181_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snd_1151_);
lean_inc(v_fst_1150_);
lean_dec(v_snd_1145_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1181_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_fst_1155_; lean_object* v_snd_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1180_; 
v_fst_1155_ = lean_ctor_get(v_b_1135_, 0);
v_snd_1156_ = lean_ctor_get(v_b_1135_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_b_1135_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1158_ = v_b_1135_;
v_isShared_1159_ = v_isSharedCheck_1180_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snd_1156_);
lean_inc(v_fst_1155_);
lean_dec(v_b_1135_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1180_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
lean_inc(v_snd_1151_);
lean_inc_ref(v___x_1128_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v_snd_1151_);
lean_ctor_set(v___x_1158_, 0, v___x_1128_);
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_snd_1151_);
v___x_1161_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
uint8_t v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1156_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v_env_1163_; lean_object* v_mctx_1164_; lean_object* v_opts_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v_env_1163_ = lean_ctor_get(v_fst_1146_, 0);
lean_inc_ref(v_env_1163_);
v_mctx_1164_ = lean_ctor_get(v_fst_1146_, 1);
lean_inc_ref(v_mctx_1164_);
v_opts_1165_ = lean_ctor_get(v_fst_1146_, 3);
lean_inc_ref(v_opts_1165_);
lean_dec(v_fst_1146_);
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1156_, v___x_1161_, v___x_1166_);
lean_inc(v_snd_1130_);
lean_inc(v_fst_1129_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_snd_1130_);
lean_ctor_set(v___x_1148_, 0, v_fst_1129_);
v___x_1169_ = v___x_1148_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_fst_1129_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_snd_1130_);
v___x_1169_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_inc(v___x_1131_);
v___x_1170_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1131_);
lean_ctor_set(v___x_1170_, 2, v_env_1163_);
lean_ctor_set(v___x_1170_, 3, v_mctx_1164_);
lean_ctor_set(v___x_1170_, 4, v_opts_1165_);
lean_ctor_set(v___x_1170_, 5, v_fst_1150_);
lean_ctor_set(v___x_1170_, 6, v_snd_1151_);
v___x_1171_ = lean_array_push(v_fst_1155_, v___x_1170_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v___x_1167_);
lean_ctor_set(v___x_1153_, 0, v___x_1171_);
v___x_1173_ = v___x_1153_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1167_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
v_a_1138_ = v___x_1173_;
goto v___jp_1137_;
}
}
}
else
{
lean_object* v___x_1177_; 
lean_dec_ref(v___x_1161_);
lean_dec(v_snd_1151_);
lean_dec(v_fst_1150_);
lean_del_object(v___x_1148_);
lean_dec(v_fst_1146_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_snd_1156_);
lean_ctor_set(v___x_1153_, 0, v_fst_1155_);
v___x_1177_ = v___x_1153_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_fst_1155_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_snd_1156_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
v_a_1138_ = v___x_1177_;
goto v___jp_1137_;
}
}
}
}
}
}
}
v___jp_1137_:
{
size_t v___x_1139_; size_t v___x_1140_; 
v___x_1139_ = ((size_t)1ULL);
v___x_1140_ = lean_usize_add(v_i_1134_, v___x_1139_);
v_i_1134_ = v___x_1140_;
v_b_1135_ = v_a_1138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object* v___x_1183_, lean_object* v_fst_1184_, lean_object* v_snd_1185_, lean_object* v___x_1186_, lean_object* v_as_1187_, lean_object* v_sz_1188_, lean_object* v_i_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_){
_start:
{
size_t v_sz_boxed_1192_; size_t v_i_boxed_1193_; lean_object* v_res_1194_; 
v_sz_boxed_1192_ = lean_unbox_usize(v_sz_1188_);
lean_dec(v_sz_1188_);
v_i_boxed_1193_ = lean_unbox_usize(v_i_1189_);
lean_dec(v_i_1189_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1183_, v_fst_1184_, v_snd_1185_, v___x_1186_, v_as_1187_, v_sz_boxed_1192_, v_i_boxed_1193_, v_b_1190_);
lean_dec_ref(v_as_1187_);
return v_res_1194_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1198_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
lean_ctor_set(v___x_1200_, 2, v___x_1199_);
lean_ctor_set(v___x_1200_, 3, v___x_1199_);
lean_ctor_set(v___x_1200_, 4, v___x_1198_);
lean_ctor_set(v___x_1200_, 5, v___x_1198_);
lean_ctor_set(v___x_1200_, 6, v___x_1198_);
lean_ctor_set(v___x_1200_, 7, v___x_1198_);
lean_ctor_set(v___x_1200_, 8, v___x_1198_);
lean_ctor_set(v___x_1200_, 9, v___x_1198_);
lean_ctor_set(v___x_1200_, 10, v___x_1198_);
lean_ctor_set(v___x_1200_, 11, v___x_1197_);
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_unsigned_to_nat(32u);
v___x_1202_ = lean_mk_empty_array_with_capacity(v___x_1201_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1204_ = ((size_t)5ULL);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_unsigned_to_nat(32u);
v___x_1207_ = lean_mk_empty_array_with_capacity(v___x_1206_);
v___x_1208_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2);
v___x_1209_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
lean_ctor_set(v___x_1209_, 2, v___x_1205_);
lean_ctor_set(v___x_1209_, 3, v___x_1205_);
lean_ctor_set_usize(v___x_1209_, 4, v___x_1204_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1210_ = lean_box(1);
v___x_1211_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3);
v___x_1212_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1211_);
lean_ctor_set(v___x_1213_, 2, v___x_1210_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(lean_object* v_msgData_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v_env_1218_; uint8_t v___x_1219_; lean_object* v_env_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_scopes_1223_; lean_object* v___x_1224_; lean_object* v_opts_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1217_ = lean_st_ref_get(v___y_1215_);
v_env_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_env_1218_);
lean_dec(v___x_1217_);
v___x_1219_ = 0;
v_env_1220_ = l_Lean_Environment_setRecordingDeps(v_env_1218_, v___x_1219_);
v___x_1221_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1222_ = lean_st_ref_get(v___y_1215_);
v_scopes_1223_ = lean_ctor_get(v___x_1222_, 2);
lean_inc(v_scopes_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = l_List_head_x21___redArg(v___x_1221_, v_scopes_1223_);
lean_dec(v_scopes_1223_);
v_opts_1225_ = lean_ctor_get(v___x_1224_, 1);
lean_inc_ref(v_opts_1225_);
lean_dec(v___x_1224_);
v___x_1226_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1);
v___x_1227_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4);
v___x_1228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1228_, 0, v_env_1220_);
lean_ctor_set(v___x_1228_, 1, v___x_1226_);
lean_ctor_set(v___x_1228_, 2, v___x_1227_);
lean_ctor_set(v___x_1228_, 3, v_opts_1225_);
v___x_1229_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v_msgData_1214_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_1231_, v___y_1232_);
lean_dec(v___y_1232_);
return v_res_1234_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1235_; double v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_float_of_nat(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v_cls_1239_, lean_object* v_msg_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Elab_Command_getRef___redArg(v___y_1241_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1295_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msg_1240_, v___y_1242_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1295_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1295_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v_traceState_1252_; lean_object* v_env_1253_; lean_object* v_messages_1254_; lean_object* v_scopes_1255_; lean_object* v_usedQuotCtxts_1256_; lean_object* v_nextMacroScope_1257_; lean_object* v_maxRecDepth_1258_; lean_object* v_ngen_1259_; lean_object* v_auxDeclNGen_1260_; lean_object* v_infoState_1261_; lean_object* v_snapshotTasks_1262_; lean_object* v_prevLinterStates_1263_; lean_object* v_codeQualityEntryTasks_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1294_; 
v___x_1251_ = lean_st_ref_take(v___y_1242_);
v_traceState_1252_ = lean_ctor_get(v___x_1251_, 9);
v_env_1253_ = lean_ctor_get(v___x_1251_, 0);
v_messages_1254_ = lean_ctor_get(v___x_1251_, 1);
v_scopes_1255_ = lean_ctor_get(v___x_1251_, 2);
v_usedQuotCtxts_1256_ = lean_ctor_get(v___x_1251_, 3);
v_nextMacroScope_1257_ = lean_ctor_get(v___x_1251_, 4);
v_maxRecDepth_1258_ = lean_ctor_get(v___x_1251_, 5);
v_ngen_1259_ = lean_ctor_get(v___x_1251_, 6);
v_auxDeclNGen_1260_ = lean_ctor_get(v___x_1251_, 7);
v_infoState_1261_ = lean_ctor_get(v___x_1251_, 8);
v_snapshotTasks_1262_ = lean_ctor_get(v___x_1251_, 10);
v_prevLinterStates_1263_ = lean_ctor_get(v___x_1251_, 11);
v_codeQualityEntryTasks_1264_ = lean_ctor_get(v___x_1251_, 12);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1266_ = v___x_1251_;
v_isShared_1267_ = v_isSharedCheck_1294_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1264_);
lean_inc(v_prevLinterStates_1263_);
lean_inc(v_snapshotTasks_1262_);
lean_inc(v_traceState_1252_);
lean_inc(v_infoState_1261_);
lean_inc(v_auxDeclNGen_1260_);
lean_inc(v_ngen_1259_);
lean_inc(v_maxRecDepth_1258_);
lean_inc(v_nextMacroScope_1257_);
lean_inc(v_usedQuotCtxts_1256_);
lean_inc(v_scopes_1255_);
lean_inc(v_messages_1254_);
lean_inc(v_env_1253_);
lean_dec(v___x_1251_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1294_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
uint64_t v_tid_1268_; lean_object* v_traces_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1293_; 
v_tid_1268_ = lean_ctor_get_uint64(v_traceState_1252_, sizeof(void*)*1);
v_traces_1269_ = lean_ctor_get(v_traceState_1252_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_traceState_1252_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1271_ = v_traceState_1252_;
v_isShared_1272_ = v_isSharedCheck_1293_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_traces_1269_);
lean_dec(v_traceState_1252_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1293_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; double v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_box(0);
v___x_1275_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_1276_ = 0;
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1278_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1278_, 0, v_cls_1239_);
lean_ctor_set(v___x_1278_, 1, v___x_1274_);
lean_ctor_set(v___x_1278_, 2, v___x_1277_);
lean_ctor_set_float(v___x_1278_, sizeof(void*)*3, v___x_1275_);
lean_ctor_set_float(v___x_1278_, sizeof(void*)*3 + 8, v___x_1275_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*3 + 16, v___x_1276_);
v___x_1279_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_1280_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v_a_1247_);
lean_ctor_set(v___x_1280_, 2, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v_a_1245_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_PersistentArray_push___redArg(v_traces_1269_, v___x_1281_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1282_);
v___x_1284_ = v___x_1271_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1282_);
lean_ctor_set_uint64(v_reuseFailAlloc_1292_, sizeof(void*)*1, v_tid_1268_);
v___x_1284_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 9, v___x_1284_);
v___x_1286_ = v___x_1266_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_env_1253_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_messages_1254_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_scopes_1255_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_usedQuotCtxts_1256_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_nextMacroScope_1257_);
lean_ctor_set(v_reuseFailAlloc_1291_, 5, v_maxRecDepth_1258_);
lean_ctor_set(v_reuseFailAlloc_1291_, 6, v_ngen_1259_);
lean_ctor_set(v_reuseFailAlloc_1291_, 7, v_auxDeclNGen_1260_);
lean_ctor_set(v_reuseFailAlloc_1291_, 8, v_infoState_1261_);
lean_ctor_set(v_reuseFailAlloc_1291_, 9, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1291_, 10, v_snapshotTasks_1262_);
lean_ctor_set(v_reuseFailAlloc_1291_, 11, v_prevLinterStates_1263_);
lean_ctor_set(v_reuseFailAlloc_1291_, 12, v_codeQualityEntryTasks_1264_);
v___x_1286_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_st_ref_put(v___y_1242_, v___x_1286_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1273_);
v___x_1289_ = v___x_1249_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1273_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_msg_1240_);
lean_dec(v_cls_1239_);
v_a_1296_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1244_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1244_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v_cls_1304_, lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_cls_1304_, v_msg_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1309_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2));
v___x_1316_ = l_Lean_Name_append(v___x_1315_, v___x_1314_);
return v___x_1316_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8));
v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(lean_object* v___x_1329_, lean_object* v_val_1330_, lean_object* v_cmd_1331_, uint8_t v_onUnsolved_1332_, uint8_t v___y_1333_, lean_object* v_as_1334_, size_t v_sz_1335_, size_t v_i_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1336_, v_sz_1335_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
lean_dec(v_cmd_1331_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_b_1337_);
return v___x_1342_;
}
else
{
lean_object* v_snd_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1491_; 
v_snd_1343_ = lean_ctor_get(v_b_1337_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_b_1337_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_b_1337_, 0);
lean_dec(v_unused_1492_);
v___x_1345_ = v_b_1337_;
v_isShared_1346_ = v_isSharedCheck_1491_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snd_1343_);
lean_dec(v_b_1337_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1491_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1490_; 
v_fst_1347_ = lean_ctor_get(v_snd_1343_, 0);
v_snd_1348_ = lean_ctor_get(v_snd_1343_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_snd_1343_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1350_ = v_snd_1343_;
v_isShared_1351_ = v_isSharedCheck_1490_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_snd_1348_);
lean_inc(v_fst_1347_);
lean_dec(v_snd_1343_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1490_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_a_1352_; lean_object* v_pos_1353_; lean_object* v_endPos_1354_; uint8_t v_severity_1355_; lean_object* v_data_1356_; lean_object* v___x_1357_; lean_object* v_a_1359_; 
v_a_1352_ = lean_array_uget_borrowed(v_as_1334_, v_i_1336_);
v_pos_1353_ = lean_ctor_get(v_a_1352_, 1);
v_endPos_1354_ = lean_ctor_get(v_a_1352_, 2);
lean_inc(v_endPos_1354_);
v_severity_1355_ = lean_ctor_get_uint8(v_a_1352_, sizeof(void*)*5 + 1);
v_data_1356_ = lean_ctor_get(v_a_1352_, 4);
v___x_1357_ = lean_box(0);
if (v_severity_1355_ == 2)
{
lean_object* v___f_1372_; uint8_t v___x_1373_; 
v___f_1372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1356_);
v___x_1373_ = l_Lean_MessageData_hasTag(v___f_1372_, v_data_1356_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec(v_endPos_1354_);
lean_del_object(v___x_1345_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_fst_1347_);
lean_ctor_set(v___x_1374_, 1, v_snd_1348_);
v_a_1359_ = v___x_1374_;
goto v___jp_1358_;
}
else
{
if (lean_obj_tag(v_endPos_1354_) == 1)
{
lean_object* v_val_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1487_; 
v_val_1375_ = lean_ctor_get(v_endPos_1354_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_endPos_1354_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1377_ = v_endPos_1354_;
v_isShared_1378_ = v_isSharedCheck_1487_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_val_1375_);
lean_dec(v_endPos_1354_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1487_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; uint8_t v___x_1383_; 
lean_inc_ref(v_pos_1353_);
v___x_1379_ = l_Lean_FileMap_ofPosition(v___x_1329_, v_pos_1353_);
v___x_1380_ = l_Lean_FileMap_ofPosition(v___x_1329_, v_val_1375_);
lean_inc(v___x_1380_);
lean_inc(v___x_1379_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = 0;
v___x_1383_ = l_Lean_Syntax_Range_includes(v_val_1330_, v___x_1381_, v___x_1382_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
lean_dec_ref_known(v___x_1381_, 2);
lean_dec(v___x_1380_);
lean_dec(v___x_1379_);
lean_del_object(v___x_1377_);
lean_del_object(v___x_1345_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_fst_1347_);
lean_ctor_set(v___x_1384_, 1, v_snd_1348_);
v_a_1359_ = v___x_1384_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1385_; 
lean_inc(v_cmd_1331_);
lean_inc_ref(v___x_1381_);
v___x_1385_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1381_, v_cmd_1331_);
if (lean_obj_tag(v___x_1385_) == 1)
{
lean_object* v_val_1386_; lean_object* v_fst_1387_; lean_object* v_snd_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v___x_1380_);
lean_dec(v___x_1379_);
lean_del_object(v___x_1377_);
v_val_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_val_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v_fst_1387_ = lean_ctor_get(v_val_1386_, 0);
v_snd_1388_ = lean_ctor_get(v_val_1386_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_val_1386_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1390_ = v_val_1386_;
v_isShared_1391_ = v_isSharedCheck_1451_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_snd_1388_);
lean_inc(v_fst_1387_);
lean_dec(v_val_1386_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1451_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1449_; lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_Syntax_getPos_x3f(v_fst_1387_, v___x_1382_);
if (lean_obj_tag(v___x_1450_) == 0)
{
v___y_1449_ = v___x_1383_;
goto v___jp_1448_;
}
else
{
lean_dec_ref_known(v___x_1450_, 1);
v___y_1449_ = v___x_1382_;
goto v___jp_1448_;
}
v___jp_1392_:
{
lean_object* v___x_1398_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v_snd_1348_);
lean_ctor_set(v___x_1390_, 0, v_fst_1347_);
v___x_1398_ = v___x_1390_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_fst_1347_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_snd_1348_);
v___x_1398_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
size_t v_sz_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v_sz_1399_ = lean_array_size(v___y_1393_);
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1381_, v_fst_1387_, v_snd_1388_, v___y_1394_, v___y_1393_, v_sz_1399_, v___x_1400_, v___x_1398_);
lean_dec_ref(v___y_1393_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v_fst_1403_ = lean_ctor_get(v_a_1402_, 0);
v_snd_1404_ = lean_ctor_get(v_a_1402_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_a_1402_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v_a_1402_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v_a_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_fst_1403_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_snd_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
v_a_1359_ = v___x_1409_;
goto v___jp_1358_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_del_object(v___x_1350_);
lean_dec(v_cmd_1331_);
v_a_1412_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1401_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1401_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
v___jp_1421_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
lean_inc_ref(v___x_1381_);
v___x_1422_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1381_);
v___x_1423_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1356_);
v___x_1424_ = lean_array_get_size(v___x_1423_);
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_nat_dec_eq(v___x_1424_, v___x_1425_);
if (v___x_1426_ == 0)
{
v___y_1393_ = v___x_1423_;
v___y_1394_ = v___x_1422_;
v___y_1395_ = v___y_1338_;
v___y_1396_ = v___y_1339_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_scopes_1432_; lean_object* v___x_1433_; lean_object* v_opts_1434_; uint8_t v_hasTrace_1435_; 
v___x_1427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1428_ = l_Lean_inheritedTraceOptions;
v___x_1429_ = lean_st_ref_get(v___x_1428_);
v___x_1430_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1431_ = lean_st_ref_get(v___y_1339_);
v_scopes_1432_ = lean_ctor_get(v___x_1431_, 2);
lean_inc(v_scopes_1432_);
lean_dec(v___x_1431_);
v___x_1433_ = l_List_head_x21___redArg(v___x_1430_, v_scopes_1432_);
lean_dec(v_scopes_1432_);
v_opts_1434_ = lean_ctor_get(v___x_1433_, 1);
lean_inc_ref(v_opts_1434_);
lean_dec(v___x_1433_);
v_hasTrace_1435_ = lean_ctor_get_uint8(v_opts_1434_, sizeof(void*)*1);
if (v_hasTrace_1435_ == 0)
{
lean_dec_ref(v_opts_1434_);
lean_dec(v___x_1429_);
v___y_1393_ = v___x_1423_;
v___y_1394_ = v___x_1422_;
v___y_1395_ = v___y_1338_;
v___y_1396_ = v___y_1339_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1437_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1429_, v_opts_1434_, v___x_1436_);
lean_dec_ref(v_opts_1434_);
lean_dec(v___x_1429_);
if (v___x_1437_ == 0)
{
v___y_1393_ = v___x_1423_;
v___y_1394_ = v___x_1422_;
v___y_1395_ = v___y_1338_;
v___y_1396_ = v___y_1339_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1439_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1427_, v___x_1438_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref_known(v___x_1439_, 1);
v___y_1393_ = v___x_1423_;
v___y_1394_ = v___x_1422_;
v___y_1395_ = v___y_1338_;
v___y_1396_ = v___y_1339_;
goto v___jp_1392_;
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v___x_1423_);
lean_dec(v___x_1422_);
lean_del_object(v___x_1390_);
lean_dec(v_snd_1388_);
lean_dec(v_fst_1387_);
lean_dec_ref_known(v___x_1381_, 2);
lean_del_object(v___x_1350_);
lean_dec(v_snd_1348_);
lean_dec(v_fst_1347_);
lean_dec(v_cmd_1331_);
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
}
v___jp_1448_:
{
if (v_onUnsolved_1332_ == 0)
{
if (v___y_1333_ == 0)
{
lean_del_object(v___x_1390_);
lean_dec(v_snd_1388_);
lean_dec(v_fst_1387_);
lean_dec_ref_known(v___x_1381_, 2);
goto v___jp_1366_;
}
else
{
if (v___y_1449_ == 0)
{
lean_del_object(v___x_1390_);
lean_dec(v_snd_1388_);
lean_dec(v_fst_1387_);
lean_dec_ref_known(v___x_1381_, 2);
goto v___jp_1366_;
}
else
{
lean_del_object(v___x_1345_);
goto v___jp_1421_;
}
}
}
else
{
lean_del_object(v___x_1345_);
goto v___jp_1421_;
}
}
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_scopes_1457_; lean_object* v___x_1458_; lean_object* v_opts_1459_; uint8_t v_hasTrace_1460_; 
lean_dec(v___x_1385_);
lean_dec_ref_known(v___x_1381_, 2);
lean_del_object(v___x_1345_);
v___x_1452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1453_ = l_Lean_inheritedTraceOptions;
v___x_1454_ = lean_st_ref_get(v___x_1453_);
v___x_1455_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1456_ = lean_st_ref_get(v___y_1339_);
v_scopes_1457_ = lean_ctor_get(v___x_1456_, 2);
lean_inc(v_scopes_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = l_List_head_x21___redArg(v___x_1455_, v_scopes_1457_);
lean_dec(v_scopes_1457_);
v_opts_1459_ = lean_ctor_get(v___x_1458_, 1);
lean_inc_ref(v_opts_1459_);
lean_dec(v___x_1458_);
v_hasTrace_1460_ = lean_ctor_get_uint8(v_opts_1459_, sizeof(void*)*1);
if (v_hasTrace_1460_ == 0)
{
lean_dec_ref(v_opts_1459_);
lean_dec(v___x_1454_);
lean_dec(v___x_1380_);
lean_dec(v___x_1379_);
lean_del_object(v___x_1377_);
goto v___jp_1370_;
}
else
{
lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1462_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1454_, v_opts_1459_, v___x_1461_);
lean_dec_ref(v_opts_1459_);
lean_dec(v___x_1454_);
if (v___x_1462_ == 0)
{
lean_dec(v___x_1380_);
lean_dec(v___x_1379_);
lean_del_object(v___x_1377_);
goto v___jp_1370_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1463_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1464_ = l_Nat_reprFast(v___x_1379_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 3);
lean_ctor_set(v___x_1377_, 0, v___x_1464_);
v___x_1466_ = v___x_1377_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1467_ = l_Lean_MessageData_ofFormat(v___x_1466_);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1463_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = l_Nat_reprFast(v___x_1380_);
v___x_1472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
v___x_1473_ = l_Lean_MessageData_ofFormat(v___x_1472_);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1470_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1452_, v___x_1476_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_dec_ref_known(v___x_1477_, 1);
goto v___jp_1370_;
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_del_object(v___x_1350_);
lean_dec(v_snd_1348_);
lean_dec(v_fst_1347_);
lean_dec(v_cmd_1331_);
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
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
lean_object* v___x_1488_; 
lean_dec(v_endPos_1354_);
lean_del_object(v___x_1345_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_fst_1347_);
lean_ctor_set(v___x_1488_, 1, v_snd_1348_);
v_a_1359_ = v___x_1488_;
goto v___jp_1358_;
}
}
}
else
{
lean_object* v___x_1489_; 
lean_dec(v_endPos_1354_);
lean_del_object(v___x_1345_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_fst_1347_);
lean_ctor_set(v___x_1489_, 1, v_snd_1348_);
v_a_1359_ = v___x_1489_;
goto v___jp_1358_;
}
v___jp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v_a_1359_);
lean_ctor_set(v___x_1350_, 0, v___x_1357_);
v___x_1361_ = v___x_1350_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_a_1359_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
size_t v___x_1362_; size_t v___x_1363_; 
v___x_1362_ = ((size_t)1ULL);
v___x_1363_ = lean_usize_add(v_i_1336_, v___x_1362_);
v_i_1336_ = v___x_1363_;
v_b_1337_ = v___x_1361_;
goto _start;
}
}
v___jp_1366_:
{
lean_object* v___x_1368_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v_snd_1348_);
lean_ctor_set(v___x_1345_, 0, v_fst_1347_);
v___x_1368_ = v___x_1345_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_fst_1347_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_snd_1348_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
v_a_1359_ = v___x_1368_;
goto v___jp_1358_;
}
}
v___jp_1370_:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_fst_1347_);
lean_ctor_set(v___x_1371_, 1, v_snd_1348_);
v_a_1359_ = v___x_1371_;
goto v___jp_1358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___boxed(lean_object* v___x_1493_, lean_object* v_val_1494_, lean_object* v_cmd_1495_, lean_object* v_onUnsolved_1496_, lean_object* v___y_1497_, lean_object* v_as_1498_, lean_object* v_sz_1499_, lean_object* v_i_1500_, lean_object* v_b_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v_onUnsolved_boxed_1505_; uint8_t v___y_12009__boxed_1506_; size_t v_sz_boxed_1507_; size_t v_i_boxed_1508_; lean_object* v_res_1509_; 
v_onUnsolved_boxed_1505_ = lean_unbox(v_onUnsolved_1496_);
v___y_12009__boxed_1506_ = lean_unbox(v___y_1497_);
v_sz_boxed_1507_ = lean_unbox_usize(v_sz_1499_);
lean_dec(v_sz_1499_);
v_i_boxed_1508_ = lean_unbox_usize(v_i_1500_);
lean_dec(v_i_1500_);
v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1493_, v_val_1494_, v_cmd_1495_, v_onUnsolved_boxed_1505_, v___y_12009__boxed_1506_, v_as_1498_, v_sz_boxed_1507_, v_i_boxed_1508_, v_b_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec_ref(v_as_1498_);
lean_dec_ref(v_val_1494_);
lean_dec_ref(v___x_1493_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object* v___x_1510_, lean_object* v_val_1511_, lean_object* v_cmd_1512_, uint8_t v_onUnsolved_1513_, uint8_t v___y_1514_, lean_object* v_as_1515_, size_t v_sz_1516_, size_t v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1517_, v_sz_1516_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
lean_dec(v_cmd_1512_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1518_);
return v___x_1523_;
}
else
{
lean_object* v_snd_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1672_; 
v_snd_1524_ = lean_ctor_get(v_b_1518_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_b_1518_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; 
v_unused_1673_ = lean_ctor_get(v_b_1518_, 0);
lean_dec(v_unused_1673_);
v___x_1526_ = v_b_1518_;
v_isShared_1527_ = v_isSharedCheck_1672_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snd_1524_);
lean_dec(v_b_1518_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1672_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_fst_1528_; lean_object* v_snd_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1671_; 
v_fst_1528_ = lean_ctor_get(v_snd_1524_, 0);
v_snd_1529_ = lean_ctor_get(v_snd_1524_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_snd_1524_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1531_ = v_snd_1524_;
v_isShared_1532_ = v_isSharedCheck_1671_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_snd_1529_);
lean_inc(v_fst_1528_);
lean_dec(v_snd_1524_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1671_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_a_1533_; lean_object* v_pos_1534_; lean_object* v_endPos_1535_; uint8_t v_severity_1536_; lean_object* v_data_1537_; lean_object* v___x_1538_; lean_object* v_a_1540_; 
v_a_1533_ = lean_array_uget_borrowed(v_as_1515_, v_i_1517_);
v_pos_1534_ = lean_ctor_get(v_a_1533_, 1);
v_endPos_1535_ = lean_ctor_get(v_a_1533_, 2);
lean_inc(v_endPos_1535_);
v_severity_1536_ = lean_ctor_get_uint8(v_a_1533_, sizeof(void*)*5 + 1);
v_data_1537_ = lean_ctor_get(v_a_1533_, 4);
v___x_1538_ = lean_box(0);
if (v_severity_1536_ == 2)
{
lean_object* v___f_1553_; uint8_t v___x_1554_; 
v___f_1553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1537_);
v___x_1554_ = l_Lean_MessageData_hasTag(v___f_1553_, v_data_1537_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_dec(v_endPos_1535_);
lean_del_object(v___x_1526_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_fst_1528_);
lean_ctor_set(v___x_1555_, 1, v_snd_1529_);
v_a_1540_ = v___x_1555_;
goto v___jp_1539_;
}
else
{
if (lean_obj_tag(v_endPos_1535_) == 1)
{
lean_object* v_val_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1668_; 
v_val_1556_ = lean_ctor_get(v_endPos_1535_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_endPos_1535_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1558_ = v_endPos_1535_;
v_isShared_1559_ = v_isSharedCheck_1668_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_val_1556_);
lean_dec(v_endPos_1535_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1668_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; uint8_t v___x_1564_; 
lean_inc_ref(v_pos_1534_);
v___x_1560_ = l_Lean_FileMap_ofPosition(v___x_1510_, v_pos_1534_);
v___x_1561_ = l_Lean_FileMap_ofPosition(v___x_1510_, v_val_1556_);
lean_inc(v___x_1561_);
lean_inc(v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = 0;
v___x_1564_ = l_Lean_Syntax_Range_includes(v_val_1511_, v___x_1562_, v___x_1563_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
lean_dec_ref_known(v___x_1562_, 2);
lean_dec(v___x_1561_);
lean_dec(v___x_1560_);
lean_del_object(v___x_1558_);
lean_del_object(v___x_1526_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_fst_1528_);
lean_ctor_set(v___x_1565_, 1, v_snd_1529_);
v_a_1540_ = v___x_1565_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1566_; 
lean_inc(v_cmd_1512_);
lean_inc_ref(v___x_1562_);
v___x_1566_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1562_, v_cmd_1512_);
if (lean_obj_tag(v___x_1566_) == 1)
{
lean_object* v_val_1567_; lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v___x_1561_);
lean_dec(v___x_1560_);
lean_del_object(v___x_1558_);
v_val_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v_fst_1568_ = lean_ctor_get(v_val_1567_, 0);
v_snd_1569_ = lean_ctor_get(v_val_1567_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_val_1567_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1571_ = v_val_1567_;
v_isShared_1572_ = v_isSharedCheck_1632_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_snd_1569_);
lean_inc(v_fst_1568_);
lean_dec(v_val_1567_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1632_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; uint8_t v___y_1630_; lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Syntax_getPos_x3f(v_fst_1568_, v___x_1563_);
if (lean_obj_tag(v___x_1631_) == 0)
{
v___y_1630_ = v___x_1564_;
goto v___jp_1629_;
}
else
{
lean_dec_ref_known(v___x_1631_, 1);
v___y_1630_ = v___x_1563_;
goto v___jp_1629_;
}
v___jp_1573_:
{
lean_object* v___x_1579_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v_snd_1529_);
lean_ctor_set(v___x_1571_, 0, v_fst_1528_);
v___x_1579_ = v___x_1571_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_fst_1528_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_snd_1529_);
v___x_1579_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
size_t v_sz_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v_sz_1580_ = lean_array_size(v___y_1575_);
v___x_1581_ = ((size_t)0ULL);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1562_, v_fst_1568_, v_snd_1569_, v___y_1574_, v___y_1575_, v_sz_1580_, v___x_1581_, v___x_1579_);
lean_dec_ref(v___y_1575_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v_fst_1584_ = lean_ctor_get(v_a_1583_, 0);
v_snd_1585_ = lean_ctor_get(v_a_1583_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_a_1583_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v_a_1583_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_snd_1585_);
lean_inc(v_fst_1584_);
lean_dec(v_a_1583_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_fst_1584_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_snd_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
v_a_1540_ = v___x_1590_;
goto v___jp_1539_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_del_object(v___x_1531_);
lean_dec(v_cmd_1512_);
v_a_1593_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1582_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1582_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
v___jp_1602_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
lean_inc_ref(v___x_1562_);
v___x_1603_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1562_);
v___x_1604_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1537_);
v___x_1605_ = lean_array_get_size(v___x_1604_);
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = lean_nat_dec_eq(v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
v___y_1574_ = v___x_1603_;
v___y_1575_ = v___x_1604_;
v___y_1576_ = v___y_1519_;
v___y_1577_ = v___y_1520_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_scopes_1613_; lean_object* v___x_1614_; lean_object* v_opts_1615_; uint8_t v_hasTrace_1616_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1609_ = l_Lean_inheritedTraceOptions;
v___x_1610_ = lean_st_ref_get(v___x_1609_);
v___x_1611_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1612_ = lean_st_ref_get(v___y_1520_);
v_scopes_1613_ = lean_ctor_get(v___x_1612_, 2);
lean_inc(v_scopes_1613_);
lean_dec(v___x_1612_);
v___x_1614_ = l_List_head_x21___redArg(v___x_1611_, v_scopes_1613_);
lean_dec(v_scopes_1613_);
v_opts_1615_ = lean_ctor_get(v___x_1614_, 1);
lean_inc_ref(v_opts_1615_);
lean_dec(v___x_1614_);
v_hasTrace_1616_ = lean_ctor_get_uint8(v_opts_1615_, sizeof(void*)*1);
if (v_hasTrace_1616_ == 0)
{
lean_dec_ref(v_opts_1615_);
lean_dec(v___x_1610_);
v___y_1574_ = v___x_1603_;
v___y_1575_ = v___x_1604_;
v___y_1576_ = v___y_1519_;
v___y_1577_ = v___y_1520_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1618_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1610_, v_opts_1615_, v___x_1617_);
lean_dec_ref(v_opts_1615_);
lean_dec(v___x_1610_);
if (v___x_1618_ == 0)
{
v___y_1574_ = v___x_1603_;
v___y_1575_ = v___x_1604_;
v___y_1576_ = v___y_1519_;
v___y_1577_ = v___y_1520_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1620_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1608_, v___x_1619_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
v___y_1574_ = v___x_1603_;
v___y_1575_ = v___x_1604_;
v___y_1576_ = v___y_1519_;
v___y_1577_ = v___y_1520_;
goto v___jp_1573_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v___x_1604_);
lean_dec(v___x_1603_);
lean_del_object(v___x_1571_);
lean_dec(v_snd_1569_);
lean_dec(v_fst_1568_);
lean_dec_ref_known(v___x_1562_, 2);
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_dec(v_cmd_1512_);
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
}
v___jp_1629_:
{
if (v_onUnsolved_1513_ == 0)
{
if (v___y_1514_ == 0)
{
lean_del_object(v___x_1571_);
lean_dec(v_snd_1569_);
lean_dec(v_fst_1568_);
lean_dec_ref_known(v___x_1562_, 2);
goto v___jp_1547_;
}
else
{
if (v___y_1630_ == 0)
{
lean_del_object(v___x_1571_);
lean_dec(v_snd_1569_);
lean_dec(v_fst_1568_);
lean_dec_ref_known(v___x_1562_, 2);
goto v___jp_1547_;
}
else
{
lean_del_object(v___x_1526_);
goto v___jp_1602_;
}
}
}
else
{
lean_del_object(v___x_1526_);
goto v___jp_1602_;
}
}
}
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_scopes_1638_; lean_object* v___x_1639_; lean_object* v_opts_1640_; uint8_t v_hasTrace_1641_; 
lean_dec(v___x_1566_);
lean_dec_ref_known(v___x_1562_, 2);
lean_del_object(v___x_1526_);
v___x_1633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1634_ = l_Lean_inheritedTraceOptions;
v___x_1635_ = lean_st_ref_get(v___x_1634_);
v___x_1636_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1637_ = lean_st_ref_get(v___y_1520_);
v_scopes_1638_ = lean_ctor_get(v___x_1637_, 2);
lean_inc(v_scopes_1638_);
lean_dec(v___x_1637_);
v___x_1639_ = l_List_head_x21___redArg(v___x_1636_, v_scopes_1638_);
lean_dec(v_scopes_1638_);
v_opts_1640_ = lean_ctor_get(v___x_1639_, 1);
lean_inc_ref(v_opts_1640_);
lean_dec(v___x_1639_);
v_hasTrace_1641_ = lean_ctor_get_uint8(v_opts_1640_, sizeof(void*)*1);
if (v_hasTrace_1641_ == 0)
{
lean_dec_ref(v_opts_1640_);
lean_dec(v___x_1635_);
lean_dec(v___x_1561_);
lean_dec(v___x_1560_);
lean_del_object(v___x_1558_);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1635_, v_opts_1640_, v___x_1642_);
lean_dec_ref(v_opts_1640_);
lean_dec(v___x_1635_);
if (v___x_1643_ == 0)
{
lean_dec(v___x_1561_);
lean_dec(v___x_1560_);
lean_del_object(v___x_1558_);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1645_ = l_Nat_reprFast(v___x_1560_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 3);
lean_ctor_set(v___x_1558_, 0, v___x_1645_);
v___x_1647_ = v___x_1558_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1648_ = l_Lean_MessageData_ofFormat(v___x_1647_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1644_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = l_Nat_reprFast(v___x_1561_);
v___x_1653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
v___x_1654_ = l_Lean_MessageData_ofFormat(v___x_1653_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1651_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1633_, v___x_1657_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_dec_ref_known(v___x_1658_, 1);
goto v___jp_1551_;
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_del_object(v___x_1531_);
lean_dec(v_snd_1529_);
lean_dec(v_fst_1528_);
lean_dec(v_cmd_1512_);
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
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
lean_object* v___x_1669_; 
lean_dec(v_endPos_1535_);
lean_del_object(v___x_1526_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v_fst_1528_);
lean_ctor_set(v___x_1669_, 1, v_snd_1529_);
v_a_1540_ = v___x_1669_;
goto v___jp_1539_;
}
}
}
else
{
lean_object* v___x_1670_; 
lean_dec(v_endPos_1535_);
lean_del_object(v___x_1526_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_fst_1528_);
lean_ctor_set(v___x_1670_, 1, v_snd_1529_);
v_a_1540_ = v___x_1670_;
goto v___jp_1539_;
}
v___jp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v_a_1540_);
lean_ctor_set(v___x_1531_, 0, v___x_1538_);
v___x_1542_ = v___x_1531_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_a_1540_);
v___x_1542_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
size_t v___x_1543_; size_t v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = ((size_t)1ULL);
v___x_1544_ = lean_usize_add(v_i_1517_, v___x_1543_);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1510_, v_val_1511_, v_cmd_1512_, v_onUnsolved_1513_, v___y_1514_, v_as_1515_, v_sz_1516_, v___x_1544_, v___x_1542_, v___y_1519_, v___y_1520_);
return v___x_1545_;
}
}
v___jp_1547_:
{
lean_object* v___x_1549_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v_snd_1529_);
lean_ctor_set(v___x_1526_, 0, v_fst_1528_);
v___x_1549_ = v___x_1526_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_fst_1528_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_snd_1529_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
v_a_1540_ = v___x_1549_;
goto v___jp_1539_;
}
}
v___jp_1551_:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_fst_1528_);
lean_ctor_set(v___x_1552_, 1, v_snd_1529_);
v_a_1540_ = v___x_1552_;
goto v___jp_1539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object* v___x_1674_, lean_object* v_val_1675_, lean_object* v_cmd_1676_, lean_object* v_onUnsolved_1677_, lean_object* v___y_1678_, lean_object* v_as_1679_, lean_object* v_sz_1680_, lean_object* v_i_1681_, lean_object* v_b_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v_onUnsolved_boxed_1686_; uint8_t v___y_12350__boxed_1687_; size_t v_sz_boxed_1688_; size_t v_i_boxed_1689_; lean_object* v_res_1690_; 
v_onUnsolved_boxed_1686_ = lean_unbox(v_onUnsolved_1677_);
v___y_12350__boxed_1687_ = lean_unbox(v___y_1678_);
v_sz_boxed_1688_ = lean_unbox_usize(v_sz_1680_);
lean_dec(v_sz_1680_);
v_i_boxed_1689_ = lean_unbox_usize(v_i_1681_);
lean_dec(v_i_1681_);
v_res_1690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_1674_, v_val_1675_, v_cmd_1676_, v_onUnsolved_boxed_1686_, v___y_12350__boxed_1687_, v_as_1679_, v_sz_boxed_1688_, v_i_boxed_1689_, v_b_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec_ref(v_as_1679_);
lean_dec_ref(v_val_1675_);
lean_dec_ref(v___x_1674_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(lean_object* v___x_1691_, lean_object* v_val_1692_, lean_object* v_cmd_1693_, uint8_t v_onUnsolved_1694_, uint8_t v___y_1695_, lean_object* v_as_1696_, size_t v_sz_1697_, size_t v_i_1698_, lean_object* v_b_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1698_, v_sz_1697_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_dec(v_cmd_1693_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_b_1699_);
return v___x_1704_;
}
else
{
lean_object* v_snd_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1853_; 
v_snd_1705_ = lean_ctor_get(v_b_1699_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_b_1699_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v_b_1699_, 0);
lean_dec(v_unused_1854_);
v___x_1707_ = v_b_1699_;
v_isShared_1708_ = v_isSharedCheck_1853_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snd_1705_);
lean_dec(v_b_1699_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1853_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_fst_1709_; lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1852_; 
v_fst_1709_ = lean_ctor_get(v_snd_1705_, 0);
v_snd_1710_ = lean_ctor_get(v_snd_1705_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_snd_1705_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1712_ = v_snd_1705_;
v_isShared_1713_ = v_isSharedCheck_1852_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_inc(v_fst_1709_);
lean_dec(v_snd_1705_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1852_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_a_1714_; lean_object* v_pos_1715_; lean_object* v_endPos_1716_; uint8_t v_severity_1717_; lean_object* v_data_1718_; lean_object* v___x_1719_; lean_object* v_a_1721_; 
v_a_1714_ = lean_array_uget_borrowed(v_as_1696_, v_i_1698_);
v_pos_1715_ = lean_ctor_get(v_a_1714_, 1);
v_endPos_1716_ = lean_ctor_get(v_a_1714_, 2);
lean_inc(v_endPos_1716_);
v_severity_1717_ = lean_ctor_get_uint8(v_a_1714_, sizeof(void*)*5 + 1);
v_data_1718_ = lean_ctor_get(v_a_1714_, 4);
v___x_1719_ = lean_box(0);
if (v_severity_1717_ == 2)
{
lean_object* v___f_1734_; uint8_t v___x_1735_; 
v___f_1734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1718_);
v___x_1735_ = l_Lean_MessageData_hasTag(v___f_1734_, v_data_1718_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
lean_dec(v_endPos_1716_);
lean_del_object(v___x_1707_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v_fst_1709_);
lean_ctor_set(v___x_1736_, 1, v_snd_1710_);
v_a_1721_ = v___x_1736_;
goto v___jp_1720_;
}
else
{
if (lean_obj_tag(v_endPos_1716_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1849_; 
v_val_1737_ = lean_ctor_get(v_endPos_1716_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_endPos_1716_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1739_ = v_endPos_1716_;
v_isShared_1740_ = v_isSharedCheck_1849_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_val_1737_);
lean_dec(v_endPos_1716_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1849_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; 
lean_inc_ref(v_pos_1715_);
v___x_1741_ = l_Lean_FileMap_ofPosition(v___x_1691_, v_pos_1715_);
v___x_1742_ = l_Lean_FileMap_ofPosition(v___x_1691_, v_val_1737_);
lean_inc(v___x_1742_);
lean_inc(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = 0;
v___x_1745_ = l_Lean_Syntax_Range_includes(v_val_1692_, v___x_1743_, v___x_1744_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
lean_dec_ref_known(v___x_1743_, 2);
lean_dec(v___x_1742_);
lean_dec(v___x_1741_);
lean_del_object(v___x_1739_);
lean_del_object(v___x_1707_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_fst_1709_);
lean_ctor_set(v___x_1746_, 1, v_snd_1710_);
v_a_1721_ = v___x_1746_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1747_; 
lean_inc(v_cmd_1693_);
lean_inc_ref(v___x_1743_);
v___x_1747_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1743_, v_cmd_1693_);
if (lean_obj_tag(v___x_1747_) == 1)
{
lean_object* v_val_1748_; lean_object* v_fst_1749_; lean_object* v_snd_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v___x_1742_);
lean_dec(v___x_1741_);
lean_del_object(v___x_1739_);
v_val_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v_fst_1749_ = lean_ctor_get(v_val_1748_, 0);
v_snd_1750_ = lean_ctor_get(v_val_1748_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_val_1748_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1752_ = v_val_1748_;
v_isShared_1753_ = v_isSharedCheck_1813_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_snd_1750_);
lean_inc(v_fst_1749_);
lean_dec(v_val_1748_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1813_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; uint8_t v___y_1811_; lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_Syntax_getPos_x3f(v_fst_1749_, v___x_1744_);
if (lean_obj_tag(v___x_1812_) == 0)
{
v___y_1811_ = v___x_1745_;
goto v___jp_1810_;
}
else
{
lean_dec_ref_known(v___x_1812_, 1);
v___y_1811_ = v___x_1744_;
goto v___jp_1810_;
}
v___jp_1754_:
{
lean_object* v___x_1760_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 1, v_snd_1710_);
lean_ctor_set(v___x_1752_, 0, v_fst_1709_);
v___x_1760_ = v___x_1752_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_fst_1709_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_snd_1710_);
v___x_1760_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
size_t v_sz_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v_sz_1761_ = lean_array_size(v___y_1756_);
v___x_1762_ = ((size_t)0ULL);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1743_, v_fst_1749_, v_snd_1750_, v___y_1755_, v___y_1756_, v_sz_1761_, v___x_1762_, v___x_1760_);
lean_dec_ref(v___y_1756_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v_fst_1765_; lean_object* v_snd_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v_fst_1765_ = lean_ctor_get(v_a_1764_, 0);
v_snd_1766_ = lean_ctor_get(v_a_1764_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_a_1764_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v_a_1764_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_snd_1766_);
lean_inc(v_fst_1765_);
lean_dec(v_a_1764_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_fst_1765_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_snd_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
v_a_1721_ = v___x_1771_;
goto v___jp_1720_;
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_del_object(v___x_1712_);
lean_dec(v_cmd_1693_);
v_a_1774_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1763_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1763_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
v___jp_1783_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
lean_inc_ref(v___x_1743_);
v___x_1784_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1743_);
v___x_1785_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1718_);
v___x_1786_ = lean_array_get_size(v___x_1785_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_nat_dec_eq(v___x_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
v___y_1755_ = v___x_1784_;
v___y_1756_ = v___x_1785_;
v___y_1757_ = v___y_1700_;
v___y_1758_ = v___y_1701_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_scopes_1794_; lean_object* v___x_1795_; lean_object* v_opts_1796_; uint8_t v_hasTrace_1797_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1790_ = l_Lean_inheritedTraceOptions;
v___x_1791_ = lean_st_ref_get(v___x_1790_);
v___x_1792_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1793_ = lean_st_ref_get(v___y_1701_);
v_scopes_1794_ = lean_ctor_get(v___x_1793_, 2);
lean_inc(v_scopes_1794_);
lean_dec(v___x_1793_);
v___x_1795_ = l_List_head_x21___redArg(v___x_1792_, v_scopes_1794_);
lean_dec(v_scopes_1794_);
v_opts_1796_ = lean_ctor_get(v___x_1795_, 1);
lean_inc_ref(v_opts_1796_);
lean_dec(v___x_1795_);
v_hasTrace_1797_ = lean_ctor_get_uint8(v_opts_1796_, sizeof(void*)*1);
if (v_hasTrace_1797_ == 0)
{
lean_dec_ref(v_opts_1796_);
lean_dec(v___x_1791_);
v___y_1755_ = v___x_1784_;
v___y_1756_ = v___x_1785_;
v___y_1757_ = v___y_1700_;
v___y_1758_ = v___y_1701_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1791_, v_opts_1796_, v___x_1798_);
lean_dec_ref(v_opts_1796_);
lean_dec(v___x_1791_);
if (v___x_1799_ == 0)
{
v___y_1755_ = v___x_1784_;
v___y_1756_ = v___x_1785_;
v___y_1757_ = v___y_1700_;
v___y_1758_ = v___y_1701_;
goto v___jp_1754_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1801_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1789_, v___x_1800_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_dec_ref_known(v___x_1801_, 1);
v___y_1755_ = v___x_1784_;
v___y_1756_ = v___x_1785_;
v___y_1757_ = v___y_1700_;
v___y_1758_ = v___y_1701_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec_ref(v___x_1785_);
lean_dec(v___x_1784_);
lean_del_object(v___x_1752_);
lean_dec(v_snd_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref_known(v___x_1743_, 2);
lean_del_object(v___x_1712_);
lean_dec(v_snd_1710_);
lean_dec(v_fst_1709_);
lean_dec(v_cmd_1693_);
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
}
}
v___jp_1810_:
{
if (v_onUnsolved_1694_ == 0)
{
if (v___y_1695_ == 0)
{
lean_del_object(v___x_1752_);
lean_dec(v_snd_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref_known(v___x_1743_, 2);
goto v___jp_1728_;
}
else
{
if (v___y_1811_ == 0)
{
lean_del_object(v___x_1752_);
lean_dec(v_snd_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref_known(v___x_1743_, 2);
goto v___jp_1728_;
}
else
{
lean_del_object(v___x_1707_);
goto v___jp_1783_;
}
}
}
else
{
lean_del_object(v___x_1707_);
goto v___jp_1783_;
}
}
}
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v_scopes_1819_; lean_object* v___x_1820_; lean_object* v_opts_1821_; uint8_t v_hasTrace_1822_; 
lean_dec(v___x_1747_);
lean_dec_ref_known(v___x_1743_, 2);
lean_del_object(v___x_1707_);
v___x_1814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1815_ = l_Lean_inheritedTraceOptions;
v___x_1816_ = lean_st_ref_get(v___x_1815_);
v___x_1817_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1818_ = lean_st_ref_get(v___y_1701_);
v_scopes_1819_ = lean_ctor_get(v___x_1818_, 2);
lean_inc(v_scopes_1819_);
lean_dec(v___x_1818_);
v___x_1820_ = l_List_head_x21___redArg(v___x_1817_, v_scopes_1819_);
lean_dec(v_scopes_1819_);
v_opts_1821_ = lean_ctor_get(v___x_1820_, 1);
lean_inc_ref(v_opts_1821_);
lean_dec(v___x_1820_);
v_hasTrace_1822_ = lean_ctor_get_uint8(v_opts_1821_, sizeof(void*)*1);
if (v_hasTrace_1822_ == 0)
{
lean_dec_ref(v_opts_1821_);
lean_dec(v___x_1816_);
lean_dec(v___x_1742_);
lean_dec(v___x_1741_);
lean_del_object(v___x_1739_);
goto v___jp_1732_;
}
else
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1824_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1816_, v_opts_1821_, v___x_1823_);
lean_dec_ref(v_opts_1821_);
lean_dec(v___x_1816_);
if (v___x_1824_ == 0)
{
lean_dec(v___x_1742_);
lean_dec(v___x_1741_);
lean_del_object(v___x_1739_);
goto v___jp_1732_;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1825_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1826_ = l_Nat_reprFast(v___x_1741_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set_tag(v___x_1739_, 3);
lean_ctor_set(v___x_1739_, 0, v___x_1826_);
v___x_1828_ = v___x_1739_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1829_ = l_Lean_MessageData_ofFormat(v___x_1828_);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1825_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = l_Nat_reprFast(v___x_1742_);
v___x_1834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
v___x_1835_ = l_Lean_MessageData_ofFormat(v___x_1834_);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1832_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1814_, v___x_1838_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_dec_ref_known(v___x_1839_, 1);
goto v___jp_1732_;
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_del_object(v___x_1712_);
lean_dec(v_snd_1710_);
lean_dec(v_fst_1709_);
lean_dec(v_cmd_1693_);
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
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
lean_object* v___x_1850_; 
lean_dec(v_endPos_1716_);
lean_del_object(v___x_1707_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_fst_1709_);
lean_ctor_set(v___x_1850_, 1, v_snd_1710_);
v_a_1721_ = v___x_1850_;
goto v___jp_1720_;
}
}
}
else
{
lean_object* v___x_1851_; 
lean_dec(v_endPos_1716_);
lean_del_object(v___x_1707_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v_fst_1709_);
lean_ctor_set(v___x_1851_, 1, v_snd_1710_);
v_a_1721_ = v___x_1851_;
goto v___jp_1720_;
}
v___jp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v_a_1721_);
lean_ctor_set(v___x_1712_, 0, v___x_1719_);
v___x_1723_ = v___x_1712_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_a_1721_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
size_t v___x_1724_; size_t v___x_1725_; 
v___x_1724_ = ((size_t)1ULL);
v___x_1725_ = lean_usize_add(v_i_1698_, v___x_1724_);
v_i_1698_ = v___x_1725_;
v_b_1699_ = v___x_1723_;
goto _start;
}
}
v___jp_1728_:
{
lean_object* v___x_1730_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v_snd_1710_);
lean_ctor_set(v___x_1707_, 0, v_fst_1709_);
v___x_1730_ = v___x_1707_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_fst_1709_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_snd_1710_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
v_a_1721_ = v___x_1730_;
goto v___jp_1720_;
}
}
v___jp_1732_:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_fst_1709_);
lean_ctor_set(v___x_1733_, 1, v_snd_1710_);
v_a_1721_ = v___x_1733_;
goto v___jp_1720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v___x_1855_, lean_object* v_val_1856_, lean_object* v_cmd_1857_, lean_object* v_onUnsolved_1858_, lean_object* v___y_1859_, lean_object* v_as_1860_, lean_object* v_sz_1861_, lean_object* v_i_1862_, lean_object* v_b_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v_onUnsolved_boxed_1867_; uint8_t v___y_12682__boxed_1868_; size_t v_sz_boxed_1869_; size_t v_i_boxed_1870_; lean_object* v_res_1871_; 
v_onUnsolved_boxed_1867_ = lean_unbox(v_onUnsolved_1858_);
v___y_12682__boxed_1868_ = lean_unbox(v___y_1859_);
v_sz_boxed_1869_ = lean_unbox_usize(v_sz_1861_);
lean_dec(v_sz_1861_);
v_i_boxed_1870_ = lean_unbox_usize(v_i_1862_);
lean_dec(v_i_1862_);
v_res_1871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1855_, v_val_1856_, v_cmd_1857_, v_onUnsolved_boxed_1867_, v___y_12682__boxed_1868_, v_as_1860_, v_sz_boxed_1869_, v_i_boxed_1870_, v_b_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v_as_1860_);
lean_dec_ref(v_val_1856_);
lean_dec_ref(v___x_1855_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(lean_object* v___x_1872_, lean_object* v_val_1873_, lean_object* v_cmd_1874_, uint8_t v_onUnsolved_1875_, uint8_t v___y_1876_, lean_object* v_as_1877_, size_t v_sz_1878_, size_t v_i_1879_, lean_object* v_b_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v___x_1884_; 
v___x_1884_ = lean_usize_dec_lt(v_i_1879_, v_sz_1878_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; 
lean_dec(v_cmd_1874_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v_b_1880_);
return v___x_1885_;
}
else
{
lean_object* v_snd_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_2034_; 
v_snd_1886_ = lean_ctor_get(v_b_1880_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_b_1880_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_b_1880_, 0);
lean_dec(v_unused_2035_);
v___x_1888_ = v_b_1880_;
v_isShared_1889_ = v_isSharedCheck_2034_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snd_1886_);
lean_dec(v_b_1880_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_2034_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_fst_1890_; lean_object* v_snd_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_2033_; 
v_fst_1890_ = lean_ctor_get(v_snd_1886_, 0);
v_snd_1891_ = lean_ctor_get(v_snd_1886_, 1);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_snd_1886_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_1893_ = v_snd_1886_;
v_isShared_1894_ = v_isSharedCheck_2033_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_snd_1891_);
lean_inc(v_fst_1890_);
lean_dec(v_snd_1886_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_2033_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_a_1895_; lean_object* v_pos_1896_; lean_object* v_endPos_1897_; uint8_t v_severity_1898_; lean_object* v_data_1899_; lean_object* v___x_1900_; lean_object* v_a_1902_; 
v_a_1895_ = lean_array_uget_borrowed(v_as_1877_, v_i_1879_);
v_pos_1896_ = lean_ctor_get(v_a_1895_, 1);
v_endPos_1897_ = lean_ctor_get(v_a_1895_, 2);
lean_inc(v_endPos_1897_);
v_severity_1898_ = lean_ctor_get_uint8(v_a_1895_, sizeof(void*)*5 + 1);
v_data_1899_ = lean_ctor_get(v_a_1895_, 4);
v___x_1900_ = lean_box(0);
if (v_severity_1898_ == 2)
{
lean_object* v___f_1915_; uint8_t v___x_1916_; 
v___f_1915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1899_);
v___x_1916_ = l_Lean_MessageData_hasTag(v___f_1915_, v_data_1899_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
lean_dec(v_endPos_1897_);
lean_del_object(v___x_1888_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_fst_1890_);
lean_ctor_set(v___x_1917_, 1, v_snd_1891_);
v_a_1902_ = v___x_1917_;
goto v___jp_1901_;
}
else
{
if (lean_obj_tag(v_endPos_1897_) == 1)
{
lean_object* v_val_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_2030_; 
v_val_1918_ = lean_ctor_get(v_endPos_1897_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_endPos_1897_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_1920_ = v_endPos_1897_;
v_isShared_1921_ = v_isSharedCheck_2030_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_val_1918_);
lean_dec(v_endPos_1897_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_2030_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; uint8_t v___x_1926_; 
lean_inc_ref(v_pos_1896_);
v___x_1922_ = l_Lean_FileMap_ofPosition(v___x_1872_, v_pos_1896_);
v___x_1923_ = l_Lean_FileMap_ofPosition(v___x_1872_, v_val_1918_);
lean_inc(v___x_1923_);
lean_inc(v___x_1922_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = 0;
v___x_1926_ = l_Lean_Syntax_Range_includes(v_val_1873_, v___x_1924_, v___x_1925_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref_known(v___x_1924_, 2);
lean_dec(v___x_1923_);
lean_dec(v___x_1922_);
lean_del_object(v___x_1920_);
lean_del_object(v___x_1888_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_fst_1890_);
lean_ctor_set(v___x_1927_, 1, v_snd_1891_);
v_a_1902_ = v___x_1927_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1928_; 
lean_inc(v_cmd_1874_);
lean_inc_ref(v___x_1924_);
v___x_1928_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1924_, v_cmd_1874_);
if (lean_obj_tag(v___x_1928_) == 1)
{
lean_object* v_val_1929_; lean_object* v_fst_1930_; lean_object* v_snd_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v___x_1923_);
lean_dec(v___x_1922_);
lean_del_object(v___x_1920_);
v_val_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_val_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v_fst_1930_ = lean_ctor_get(v_val_1929_, 0);
v_snd_1931_ = lean_ctor_get(v_val_1929_, 1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_val_1929_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1933_ = v_val_1929_;
v_isShared_1934_ = v_isSharedCheck_1994_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_snd_1931_);
lean_inc(v_fst_1930_);
lean_dec(v_val_1929_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1994_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; uint8_t v___y_1992_; lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_Syntax_getPos_x3f(v_fst_1930_, v___x_1925_);
if (lean_obj_tag(v___x_1993_) == 0)
{
v___y_1992_ = v___x_1926_;
goto v___jp_1991_;
}
else
{
lean_dec_ref_known(v___x_1993_, 1);
v___y_1992_ = v___x_1925_;
goto v___jp_1991_;
}
v___jp_1935_:
{
lean_object* v___x_1941_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v_snd_1891_);
lean_ctor_set(v___x_1933_, 0, v_fst_1890_);
v___x_1941_ = v___x_1933_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_fst_1890_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_snd_1891_);
v___x_1941_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
size_t v_sz_1942_; size_t v___x_1943_; lean_object* v___x_1944_; 
v_sz_1942_ = lean_array_size(v___y_1937_);
v___x_1943_ = ((size_t)0ULL);
v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1924_, v_fst_1930_, v_snd_1931_, v___y_1936_, v___y_1937_, v_sz_1942_, v___x_1943_, v___x_1941_);
lean_dec_ref(v___y_1937_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v_fst_1946_ = lean_ctor_get(v_a_1945_, 0);
v_snd_1947_ = lean_ctor_get(v_a_1945_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_a_1945_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v_a_1945_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snd_1947_);
lean_inc(v_fst_1946_);
lean_dec(v_a_1945_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_fst_1946_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_snd_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
v_a_1902_ = v___x_1952_;
goto v___jp_1901_;
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_del_object(v___x_1893_);
lean_dec(v_cmd_1874_);
v_a_1955_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1944_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1944_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
v___jp_1964_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
lean_inc_ref(v___x_1924_);
v___x_1965_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1924_);
v___x_1966_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1899_);
v___x_1967_ = lean_array_get_size(v___x_1966_);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_nat_dec_eq(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
v___y_1936_ = v___x_1965_;
v___y_1937_ = v___x_1966_;
v___y_1938_ = v___y_1881_;
v___y_1939_ = v___y_1882_;
goto v___jp_1935_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_scopes_1975_; lean_object* v___x_1976_; lean_object* v_opts_1977_; uint8_t v_hasTrace_1978_; 
v___x_1970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1971_ = l_Lean_inheritedTraceOptions;
v___x_1972_ = lean_st_ref_get(v___x_1971_);
v___x_1973_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1974_ = lean_st_ref_get(v___y_1882_);
v_scopes_1975_ = lean_ctor_get(v___x_1974_, 2);
lean_inc(v_scopes_1975_);
lean_dec(v___x_1974_);
v___x_1976_ = l_List_head_x21___redArg(v___x_1973_, v_scopes_1975_);
lean_dec(v_scopes_1975_);
v_opts_1977_ = lean_ctor_get(v___x_1976_, 1);
lean_inc_ref(v_opts_1977_);
lean_dec(v___x_1976_);
v_hasTrace_1978_ = lean_ctor_get_uint8(v_opts_1977_, sizeof(void*)*1);
if (v_hasTrace_1978_ == 0)
{
lean_dec_ref(v_opts_1977_);
lean_dec(v___x_1972_);
v___y_1936_ = v___x_1965_;
v___y_1937_ = v___x_1966_;
v___y_1938_ = v___y_1881_;
v___y_1939_ = v___y_1882_;
goto v___jp_1935_;
}
else
{
lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1980_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1972_, v_opts_1977_, v___x_1979_);
lean_dec_ref(v_opts_1977_);
lean_dec(v___x_1972_);
if (v___x_1980_ == 0)
{
v___y_1936_ = v___x_1965_;
v___y_1937_ = v___x_1966_;
v___y_1938_ = v___y_1881_;
v___y_1939_ = v___y_1882_;
goto v___jp_1935_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1982_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1970_, v___x_1981_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_dec_ref_known(v___x_1982_, 1);
v___y_1936_ = v___x_1965_;
v___y_1937_ = v___x_1966_;
v___y_1938_ = v___y_1881_;
v___y_1939_ = v___y_1882_;
goto v___jp_1935_;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref(v___x_1966_);
lean_dec(v___x_1965_);
lean_del_object(v___x_1933_);
lean_dec(v_snd_1931_);
lean_dec(v_fst_1930_);
lean_dec_ref_known(v___x_1924_, 2);
lean_del_object(v___x_1893_);
lean_dec(v_snd_1891_);
lean_dec(v_fst_1890_);
lean_dec(v_cmd_1874_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
}
v___jp_1991_:
{
if (v_onUnsolved_1875_ == 0)
{
if (v___y_1876_ == 0)
{
lean_del_object(v___x_1933_);
lean_dec(v_snd_1931_);
lean_dec(v_fst_1930_);
lean_dec_ref_known(v___x_1924_, 2);
goto v___jp_1909_;
}
else
{
if (v___y_1992_ == 0)
{
lean_del_object(v___x_1933_);
lean_dec(v_snd_1931_);
lean_dec(v_fst_1930_);
lean_dec_ref_known(v___x_1924_, 2);
goto v___jp_1909_;
}
else
{
lean_del_object(v___x_1888_);
goto v___jp_1964_;
}
}
}
else
{
lean_del_object(v___x_1888_);
goto v___jp_1964_;
}
}
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v_scopes_2000_; lean_object* v___x_2001_; lean_object* v_opts_2002_; uint8_t v_hasTrace_2003_; 
lean_dec(v___x_1928_);
lean_dec_ref_known(v___x_1924_, 2);
lean_del_object(v___x_1888_);
v___x_1995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1996_ = l_Lean_inheritedTraceOptions;
v___x_1997_ = lean_st_ref_get(v___x_1996_);
v___x_1998_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1999_ = lean_st_ref_get(v___y_1882_);
v_scopes_2000_ = lean_ctor_get(v___x_1999_, 2);
lean_inc(v_scopes_2000_);
lean_dec(v___x_1999_);
v___x_2001_ = l_List_head_x21___redArg(v___x_1998_, v_scopes_2000_);
lean_dec(v_scopes_2000_);
v_opts_2002_ = lean_ctor_get(v___x_2001_, 1);
lean_inc_ref(v_opts_2002_);
lean_dec(v___x_2001_);
v_hasTrace_2003_ = lean_ctor_get_uint8(v_opts_2002_, sizeof(void*)*1);
if (v_hasTrace_2003_ == 0)
{
lean_dec_ref(v_opts_2002_);
lean_dec(v___x_1997_);
lean_dec(v___x_1923_);
lean_dec(v___x_1922_);
lean_del_object(v___x_1920_);
goto v___jp_1913_;
}
else
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2005_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1997_, v_opts_2002_, v___x_2004_);
lean_dec_ref(v_opts_2002_);
lean_dec(v___x_1997_);
if (v___x_2005_ == 0)
{
lean_dec(v___x_1923_);
lean_dec(v___x_1922_);
lean_del_object(v___x_1920_);
goto v___jp_1913_;
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2006_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_2007_ = l_Nat_reprFast(v___x_1922_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 3);
lean_ctor_set(v___x_1920_, 0, v___x_2007_);
v___x_2009_ = v___x_1920_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2010_ = l_Lean_MessageData_ofFormat(v___x_2009_);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2006_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = l_Nat_reprFast(v___x_1923_);
v___x_2015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
v___x_2016_ = l_Lean_MessageData_ofFormat(v___x_2015_);
v___x_2017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2013_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1995_, v___x_2019_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_dec_ref_known(v___x_2020_, 1);
goto v___jp_1913_;
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_del_object(v___x_1893_);
lean_dec(v_snd_1891_);
lean_dec(v_fst_1890_);
lean_dec(v_cmd_1874_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
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
lean_object* v___x_2031_; 
lean_dec(v_endPos_1897_);
lean_del_object(v___x_1888_);
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_fst_1890_);
lean_ctor_set(v___x_2031_, 1, v_snd_1891_);
v_a_1902_ = v___x_2031_;
goto v___jp_1901_;
}
}
}
else
{
lean_object* v___x_2032_; 
lean_dec(v_endPos_1897_);
lean_del_object(v___x_1888_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_fst_1890_);
lean_ctor_set(v___x_2032_, 1, v_snd_1891_);
v_a_1902_ = v___x_2032_;
goto v___jp_1901_;
}
v___jp_1901_:
{
lean_object* v___x_1904_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v_a_1902_);
lean_ctor_set(v___x_1893_, 0, v___x_1900_);
v___x_1904_ = v___x_1893_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1902_);
v___x_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
size_t v___x_1905_; size_t v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_add(v_i_1879_, v___x_1905_);
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1872_, v_val_1873_, v_cmd_1874_, v_onUnsolved_1875_, v___y_1876_, v_as_1877_, v_sz_1878_, v___x_1906_, v___x_1904_, v___y_1881_, v___y_1882_);
return v___x_1907_;
}
}
v___jp_1909_:
{
lean_object* v___x_1911_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v_snd_1891_);
lean_ctor_set(v___x_1888_, 0, v_fst_1890_);
v___x_1911_ = v___x_1888_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_fst_1890_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_snd_1891_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
v_a_1902_ = v___x_1911_;
goto v___jp_1901_;
}
}
v___jp_1913_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_fst_1890_);
lean_ctor_set(v___x_1914_, 1, v_snd_1891_);
v_a_1902_ = v___x_1914_;
goto v___jp_1901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11___boxed(lean_object* v___x_2036_, lean_object* v_val_2037_, lean_object* v_cmd_2038_, lean_object* v_onUnsolved_2039_, lean_object* v___y_2040_, lean_object* v_as_2041_, lean_object* v_sz_2042_, lean_object* v_i_2043_, lean_object* v_b_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_onUnsolved_boxed_2048_; uint8_t v___y_13014__boxed_2049_; size_t v_sz_boxed_2050_; size_t v_i_boxed_2051_; lean_object* v_res_2052_; 
v_onUnsolved_boxed_2048_ = lean_unbox(v_onUnsolved_2039_);
v___y_13014__boxed_2049_ = lean_unbox(v___y_2040_);
v_sz_boxed_2050_ = lean_unbox_usize(v_sz_2042_);
lean_dec(v_sz_2042_);
v_i_boxed_2051_ = lean_unbox_usize(v_i_2043_);
lean_dec(v_i_2043_);
v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2036_, v_val_2037_, v_cmd_2038_, v_onUnsolved_boxed_2048_, v___y_13014__boxed_2049_, v_as_2041_, v_sz_boxed_2050_, v_i_boxed_2051_, v_b_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec_ref(v_as_2041_);
lean_dec_ref(v_val_2037_);
lean_dec_ref(v___x_2036_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(lean_object* v_init_2053_, lean_object* v___x_2054_, lean_object* v_val_2055_, lean_object* v_cmd_2056_, uint8_t v_onUnsolved_2057_, uint8_t v___y_2058_, lean_object* v_n_2059_, lean_object* v_b_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
if (lean_obj_tag(v_n_2059_) == 0)
{
lean_object* v_cs_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; size_t v_sz_2067_; size_t v___x_2068_; lean_object* v___x_2069_; 
v_cs_2064_ = lean_ctor_get(v_n_2059_, 0);
v___x_2065_ = lean_box(0);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v_b_2060_);
v_sz_2067_ = lean_array_size(v_cs_2064_);
v___x_2068_ = ((size_t)0ULL);
v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2053_, v___x_2054_, v_val_2055_, v_cmd_2056_, v_onUnsolved_2057_, v___y_2058_, v_cs_2064_, v_sz_2067_, v___x_2068_, v___x_2066_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2084_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2084_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2084_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v_fst_2074_; 
v_fst_2074_ = lean_ctor_get(v_a_2070_, 0);
if (lean_obj_tag(v_fst_2074_) == 0)
{
lean_object* v_snd_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v_snd_2075_ = lean_ctor_get(v_a_2070_, 1);
lean_inc(v_snd_2075_);
lean_dec(v_a_2070_);
v___x_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_snd_2075_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2076_);
v___x_2078_ = v___x_2072_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
else
{
lean_object* v_val_2080_; lean_object* v___x_2082_; 
lean_inc_ref(v_fst_2074_);
lean_dec(v_a_2070_);
v_val_2080_ = lean_ctor_get(v_fst_2074_, 0);
lean_inc(v_val_2080_);
lean_dec_ref_known(v_fst_2074_, 1);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v_val_2080_);
v___x_2082_ = v___x_2072_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_val_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2069_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2069_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
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
lean_object* v_vs_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; size_t v_sz_2096_; size_t v___x_2097_; lean_object* v___x_2098_; 
v_vs_2093_ = lean_ctor_get(v_n_2059_, 0);
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v_b_2060_);
v_sz_2096_ = lean_array_size(v_vs_2093_);
v___x_2097_ = ((size_t)0ULL);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2054_, v_val_2055_, v_cmd_2056_, v_onUnsolved_2057_, v___y_2058_, v_vs_2093_, v_sz_2096_, v___x_2097_, v___x_2095_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2113_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2113_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2113_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_fst_2103_; 
v_fst_2103_ = lean_ctor_get(v_a_2099_, 0);
if (lean_obj_tag(v_fst_2103_) == 0)
{
lean_object* v_snd_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v_snd_2104_ = lean_ctor_get(v_a_2099_, 1);
lean_inc(v_snd_2104_);
lean_dec(v_a_2099_);
v___x_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2105_, 0, v_snd_2104_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2105_);
v___x_2107_ = v___x_2101_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
else
{
lean_object* v_val_2109_; lean_object* v___x_2111_; 
lean_inc_ref(v_fst_2103_);
lean_dec(v_a_2099_);
v_val_2109_ = lean_ctor_get(v_fst_2103_, 0);
lean_inc(v_val_2109_);
lean_dec_ref_known(v_fst_2103_, 1);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v_val_2109_);
v___x_2111_ = v___x_2101_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_val_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2098_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2098_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(lean_object* v_init_2122_, lean_object* v___x_2123_, lean_object* v_val_2124_, lean_object* v_cmd_2125_, uint8_t v_onUnsolved_2126_, uint8_t v___y_2127_, lean_object* v_as_2128_, size_t v_sz_2129_, size_t v_i_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_usize_dec_lt(v_i_2130_, v_sz_2129_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec(v_cmd_2125_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_b_2131_);
return v___x_2136_;
}
else
{
lean_object* v_snd_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2171_; 
v_snd_2137_ = lean_ctor_get(v_b_2131_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_b_2131_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; 
v_unused_2172_ = lean_ctor_get(v_b_2131_, 0);
lean_dec(v_unused_2172_);
v___x_2139_ = v_b_2131_;
v_isShared_2140_ = v_isSharedCheck_2171_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_snd_2137_);
lean_dec(v_b_2131_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2171_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v_a_2142_; lean_object* v___x_2143_; 
v___x_2141_ = lean_box(0);
v_a_2142_ = lean_array_uget_borrowed(v_as_2128_, v_i_2130_);
lean_inc(v_snd_2137_);
lean_inc(v_cmd_2125_);
v___x_2143_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2122_, v___x_2123_, v_val_2124_, v_cmd_2125_, v_onUnsolved_2126_, v___y_2127_, v_a_2142_, v_snd_2137_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2162_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2162_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2162_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
if (lean_obj_tag(v_a_2144_) == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_cmd_2125_);
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_a_2144_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2148_);
v___x_2150_ = v___x_2139_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2137_);
v___x_2150_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2150_);
v___x_2152_ = v___x_2146_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; 
lean_del_object(v___x_2146_);
lean_dec(v_snd_2137_);
v_a_2155_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v_a_2144_, 1);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_a_2155_);
lean_ctor_set(v___x_2139_, 0, v___x_2141_);
v___x_2157_ = v___x_2139_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2155_);
v___x_2157_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
size_t v___x_2158_; size_t v___x_2159_; 
v___x_2158_ = ((size_t)1ULL);
v___x_2159_ = lean_usize_add(v_i_2130_, v___x_2158_);
v_i_2130_ = v___x_2159_;
v_b_2131_ = v___x_2157_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_del_object(v___x_2139_);
lean_dec(v_snd_2137_);
lean_dec(v_cmd_2125_);
v_a_2163_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2143_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2143_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10___boxed(lean_object* v_init_2173_, lean_object* v___x_2174_, lean_object* v_val_2175_, lean_object* v_cmd_2176_, lean_object* v_onUnsolved_2177_, lean_object* v___y_2178_, lean_object* v_as_2179_, lean_object* v_sz_2180_, lean_object* v_i_2181_, lean_object* v_b_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
uint8_t v_onUnsolved_boxed_2186_; uint8_t v___y_13315__boxed_2187_; size_t v_sz_boxed_2188_; size_t v_i_boxed_2189_; lean_object* v_res_2190_; 
v_onUnsolved_boxed_2186_ = lean_unbox(v_onUnsolved_2177_);
v___y_13315__boxed_2187_ = lean_unbox(v___y_2178_);
v_sz_boxed_2188_ = lean_unbox_usize(v_sz_2180_);
lean_dec(v_sz_2180_);
v_i_boxed_2189_ = lean_unbox_usize(v_i_2181_);
lean_dec(v_i_2181_);
v_res_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2173_, v___x_2174_, v_val_2175_, v_cmd_2176_, v_onUnsolved_boxed_2186_, v___y_13315__boxed_2187_, v_as_2179_, v_sz_boxed_2188_, v_i_boxed_2189_, v_b_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec_ref(v_as_2179_);
lean_dec_ref(v_val_2175_);
lean_dec_ref(v___x_2174_);
lean_dec_ref(v_init_2173_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8___boxed(lean_object* v_init_2191_, lean_object* v___x_2192_, lean_object* v_val_2193_, lean_object* v_cmd_2194_, lean_object* v_onUnsolved_2195_, lean_object* v___y_2196_, lean_object* v_n_2197_, lean_object* v_b_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
uint8_t v_onUnsolved_boxed_2202_; uint8_t v___y_13337__boxed_2203_; lean_object* v_res_2204_; 
v_onUnsolved_boxed_2202_ = lean_unbox(v_onUnsolved_2195_);
v___y_13337__boxed_2203_ = lean_unbox(v___y_2196_);
v_res_2204_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2191_, v___x_2192_, v_val_2193_, v_cmd_2194_, v_onUnsolved_boxed_2202_, v___y_13337__boxed_2203_, v_n_2197_, v_b_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec_ref(v_n_2197_);
lean_dec_ref(v_val_2193_);
lean_dec_ref(v___x_2192_);
lean_dec_ref(v_init_2191_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object* v___x_2205_, lean_object* v_val_2206_, lean_object* v_cmd_2207_, uint8_t v_onUnsolved_2208_, uint8_t v___y_2209_, lean_object* v_t_2210_, lean_object* v_init_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_root_2215_; lean_object* v_tail_2216_; lean_object* v___x_2217_; 
v_root_2215_ = lean_ctor_get(v_t_2210_, 0);
v_tail_2216_ = lean_ctor_get(v_t_2210_, 1);
lean_inc(v_cmd_2207_);
lean_inc_ref(v_init_2211_);
v___x_2217_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2211_, v___x_2205_, v_val_2206_, v_cmd_2207_, v_onUnsolved_2208_, v___y_2209_, v_root_2215_, v_init_2211_, v___y_2212_, v___y_2213_);
lean_dec_ref(v_init_2211_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2254_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2254_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2254_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
if (lean_obj_tag(v_a_2218_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; 
lean_dec(v_cmd_2207_);
v_a_2222_ = lean_ctor_get(v_a_2218_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v_a_2218_, 1);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v_a_2222_);
v___x_2224_ = v___x_2220_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; size_t v_sz_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
lean_del_object(v___x_2220_);
v_a_2226_ = lean_ctor_get(v_a_2218_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v_a_2218_, 1);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v_a_2226_);
v_sz_2229_ = lean_array_size(v_tail_2216_);
v___x_2230_ = ((size_t)0ULL);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_2205_, v_val_2206_, v_cmd_2207_, v_onUnsolved_2208_, v___y_2209_, v_tail_2216_, v_sz_2229_, v___x_2230_, v___x_2228_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2245_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2245_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2245_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v_fst_2236_; 
v_fst_2236_ = lean_ctor_get(v_a_2232_, 0);
if (lean_obj_tag(v_fst_2236_) == 0)
{
lean_object* v_snd_2237_; lean_object* v___x_2239_; 
v_snd_2237_ = lean_ctor_get(v_a_2232_, 1);
lean_inc(v_snd_2237_);
lean_dec(v_a_2232_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v_snd_2237_);
v___x_2239_ = v___x_2234_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_snd_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
else
{
lean_object* v_val_2241_; lean_object* v___x_2243_; 
lean_inc_ref(v_fst_2236_);
lean_dec(v_a_2232_);
v_val_2241_ = lean_ctor_get(v_fst_2236_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v_fst_2236_, 1);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v_val_2241_);
v___x_2243_ = v___x_2234_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_val_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
v_a_2246_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2231_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2231_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_cmd_2207_);
v_a_2255_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2217_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2217_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object* v___x_2263_, lean_object* v_val_2264_, lean_object* v_cmd_2265_, lean_object* v_onUnsolved_2266_, lean_object* v___y_2267_, lean_object* v_t_2268_, lean_object* v_init_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
uint8_t v_onUnsolved_boxed_2273_; uint8_t v___y_13528__boxed_2274_; lean_object* v_res_2275_; 
v_onUnsolved_boxed_2273_ = lean_unbox(v_onUnsolved_2266_);
v___y_13528__boxed_2274_ = lean_unbox(v___y_2267_);
v_res_2275_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2263_, v_val_2264_, v_cmd_2265_, v_onUnsolved_boxed_2273_, v___y_13528__boxed_2274_, v_t_2268_, v_init_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_t_2268_);
lean_dec_ref(v_val_2264_);
lean_dec_ref(v___x_2263_);
return v_res_2275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_unsigned_to_nat(16u);
v___x_2278_ = lean_mk_array(v___x_2277_, v___x_2276_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2280_ = lean_unsigned_to_nat(0u);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v___x_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2285_, lean_object* v_opts_2286_, lean_object* v_tree_2287_, lean_object* v_msgs_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
uint8_t v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; uint8_t v___y_2296_; lean_object* v___y_2297_; uint8_t v___y_2298_; uint8_t v___y_2324_; uint8_t v___y_2325_; lean_object* v_acc_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___f_2330_; uint8_t v___y_2332_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___f_2330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2339_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2340_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2286_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2341_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2342_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2286_, v___x_2341_);
v___y_2332_ = v___x_2342_;
goto v___jp_2331_;
}
else
{
v___y_2332_ = v___x_2340_;
goto v___jp_2331_;
}
v___jp_2292_:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Syntax_getRange_x3f(v_cmd_2285_, v___y_2298_);
if (lean_obj_tag(v___x_2299_) == 1)
{
lean_object* v_val_2300_; lean_object* v_fileMap_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_val_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v_fileMap_2301_ = lean_ctor_get(v___y_2297_, 1);
v___x_2302_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___y_2294_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v_fileMap_2301_, v_val_2300_, v_cmd_2285_, v___y_2293_, v___y_2296_, v_msgs_2288_, v___x_2303_, v___y_2297_, v___y_2295_);
lean_dec(v_val_2300_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2313_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2313_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2313_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_fst_2309_; lean_object* v___x_2311_; 
v_fst_2309_ = lean_ctor_get(v_a_2305_, 0);
lean_inc(v_fst_2309_);
lean_dec(v_a_2305_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v_fst_2309_);
v___x_2311_ = v___x_2307_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_fst_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2314_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2304_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2304_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v___x_2322_; 
lean_dec(v___x_2299_);
lean_dec(v_cmd_2285_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___y_2294_);
return v___x_2322_;
}
}
v___jp_2323_:
{
if (v___y_2324_ == 0)
{
if (v___y_2325_ == 0)
{
lean_object* v___x_2329_; 
lean_dec(v_cmd_2285_);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v_acc_2326_);
return v___x_2329_;
}
else
{
v___y_2293_ = v___y_2324_;
v___y_2294_ = v_acc_2326_;
v___y_2295_ = v___y_2328_;
v___y_2296_ = v___y_2325_;
v___y_2297_ = v___y_2327_;
v___y_2298_ = v___y_2325_;
goto v___jp_2292_;
}
}
else
{
v___y_2293_ = v___y_2324_;
v___y_2294_ = v_acc_2326_;
v___y_2295_ = v___y_2328_;
v___y_2296_ = v___y_2325_;
v___y_2297_ = v___y_2327_;
v___y_2298_ = v___y_2324_;
goto v___jp_2292_;
}
}
v___jp_2331_:
{
lean_object* v___x_2333_; uint8_t v_onUnsolved_2334_; lean_object* v___x_2335_; uint8_t v_onSorry_2336_; lean_object* v_acc_2337_; 
v___x_2333_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2334_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2286_, v___x_2333_);
v___x_2335_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2336_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2286_, v___x_2335_);
v_acc_2337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2336_ == 0)
{
lean_dec_ref(v_tree_2287_);
v___y_2324_ = v_onUnsolved_2334_;
v___y_2325_ = v___y_2332_;
v_acc_2326_ = v_acc_2337_;
v___y_2327_ = v_a_2289_;
v___y_2328_ = v_a_2290_;
goto v___jp_2323_;
}
else
{
lean_object* v_acc_2338_; 
v_acc_2338_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2330_, v_acc_2337_, v_tree_2287_);
v___y_2324_ = v_onUnsolved_2334_;
v___y_2325_ = v___y_2332_;
v_acc_2326_ = v_acc_2338_;
v___y_2327_ = v_a_2289_;
v___y_2328_ = v_a_2290_;
goto v___jp_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2343_, lean_object* v_opts_2344_, lean_object* v_tree_2345_, lean_object* v_msgs_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2343_, v_opts_2344_, v_tree_2345_, v_msgs_2346_, v_a_2347_, v_a_2348_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec_ref(v_msgs_2346_);
lean_dec_ref(v_opts_2344_);
return v_res_2350_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2351_, lean_object* v_m_2352_, lean_object* v_a_2353_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2352_, v_a_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object* v_00_u03b2_2355_, lean_object* v_m_2356_, lean_object* v_a_2357_){
_start:
{
uint8_t v_res_2358_; lean_object* v_r_2359_; 
v_res_2358_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(v_00_u03b2_2355_, v_m_2356_, v_a_2357_);
lean_dec_ref(v_a_2357_);
lean_dec_ref(v_m_2356_);
v_r_2359_ = lean_box(v_res_2358_);
return v_r_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v_00_u03b2_2360_, lean_object* v_m_2361_, lean_object* v_a_2362_, lean_object* v_b_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_2361_, v_a_2362_, v_b_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v___x_2365_, lean_object* v_fst_2366_, lean_object* v_snd_2367_, lean_object* v___x_2368_, lean_object* v_as_2369_, size_t v_sz_2370_, size_t v_i_2371_, lean_object* v_b_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_2365_, v_fst_2366_, v_snd_2367_, v___x_2368_, v_as_2369_, v_sz_2370_, v_i_2371_, v_b_2372_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v___x_2377_, lean_object* v_fst_2378_, lean_object* v_snd_2379_, lean_object* v___x_2380_, lean_object* v_as_2381_, lean_object* v_sz_2382_, lean_object* v_i_2383_, lean_object* v_b_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
size_t v_sz_boxed_2388_; size_t v_i_boxed_2389_; lean_object* v_res_2390_; 
v_sz_boxed_2388_ = lean_unbox_usize(v_sz_2382_);
lean_dec(v_sz_2382_);
v_i_boxed_2389_ = lean_unbox_usize(v_i_2383_);
lean_dec(v_i_2383_);
v_res_2390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2377_, v_fst_2378_, v_snd_2379_, v___x_2380_, v_as_2381_, v_sz_boxed_2388_, v_i_boxed_2389_, v_b_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec_ref(v_as_2381_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(lean_object* v_msgData_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_2391_, v___y_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___boxed(lean_object* v_msgData_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(v_msgData_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2400_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_object* v_00_u03b2_2401_, lean_object* v_a_2402_, lean_object* v_x_2403_){
_start:
{
uint8_t v___x_2404_; 
v___x_2404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_2402_, v_x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2405_, lean_object* v_a_2406_, lean_object* v_x_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(v_00_u03b2_2405_, v_a_2406_, v_x_2407_);
lean_dec(v_x_2407_);
lean_dec_ref(v_a_2406_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3(lean_object* v_00_u03b2_2410_, lean_object* v_data_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_data_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2413_, lean_object* v_i_2414_, lean_object* v_source_2415_, lean_object* v_target_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v_i_2414_, v_source_2415_, v_target_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2418_, lean_object* v_x_2419_, lean_object* v_x_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_x_2419_, v_x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; 
lean_inc(v___y_2424_);
lean_inc_ref(v___y_2423_);
v___x_2430_ = lean_apply_7(v_x_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, lean_box(0));
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2440_, lean_object* v_x_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___f_2449_; lean_object* v___x_2450_; 
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___f_2449_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2449_, 0, v_x_2441_);
lean_closure_set(v___f_2449_, 1, v___y_2442_);
lean_closure_set(v___f_2449_, 2, v___y_2443_);
v___x_2450_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2440_, v___f_2449_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2450_) == 0)
{
return v___x_2450_;
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2459_, lean_object* v_x_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2459_, v_x_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2469_, lean_object* v_mvarId_2470_, lean_object* v_x_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2470_, v_x_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2480_, lean_object* v_mvarId_2481_, lean_object* v_x_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2480_, v_mvarId_2481_, v_x_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2533_, lean_object* v_x_2534_){
_start:
{
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2535_, lean_object* v_x_2536_){
_start:
{
uint8_t v___x_11016__boxed_2537_; uint8_t v_res_2538_; lean_object* v_r_2539_; 
v___x_11016__boxed_2537_ = lean_unbox(v___x_2535_);
v_res_2538_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_11016__boxed_2537_, v_x_2536_);
lean_dec(v_x_2536_);
v_r_2539_ = lean_box(v_res_2538_);
return v_r_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v_env_2547_; uint8_t v___x_2548_; lean_object* v_env_2549_; lean_object* v___x_2550_; lean_object* v_toCold_2551_; lean_object* v_mctx_2552_; lean_object* v_lctx_2553_; lean_object* v_options_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2546_ = lean_st_ref_get(v___y_2544_);
v_env_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc_ref(v_env_2547_);
lean_dec(v___x_2546_);
v___x_2548_ = 0;
v_env_2549_ = l_Lean_Environment_setRecordingDeps(v_env_2547_, v___x_2548_);
v___x_2550_ = lean_st_ref_get(v___y_2542_);
v_toCold_2551_ = lean_ctor_get(v___y_2543_, 0);
v_mctx_2552_ = lean_ctor_get(v___x_2550_, 0);
lean_inc_ref(v_mctx_2552_);
lean_dec(v___x_2550_);
v_lctx_2553_ = lean_ctor_get(v___y_2541_, 2);
v_options_2554_ = lean_ctor_get(v_toCold_2551_, 2);
lean_inc_ref(v_options_2554_);
lean_inc_ref(v_lctx_2553_);
v___x_2555_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2555_, 0, v_env_2549_);
lean_ctor_set(v___x_2555_, 1, v_mctx_2552_);
lean_ctor_set(v___x_2555_, 2, v_lctx_2553_);
lean_ctor_set(v___x_2555_, 3, v_options_2554_);
v___x_2556_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v_msgData_2540_);
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2565_, lean_object* v_msg_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_ref_2572_; lean_object* v___x_2573_; lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2619_; 
v_ref_2572_ = lean_ctor_get(v___y_2569_, 2);
v___x_2573_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2619_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2619_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v_traceState_2579_; lean_object* v_env_2580_; lean_object* v_nextMacroScope_2581_; lean_object* v_ngen_2582_; lean_object* v_auxDeclNGen_2583_; lean_object* v_cache_2584_; lean_object* v_recordedDeps_2585_; lean_object* v_messages_2586_; lean_object* v_infoState_2587_; lean_object* v_snapshotTasks_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2618_; 
v___x_2578_ = lean_st_ref_take(v___y_2570_);
v_traceState_2579_ = lean_ctor_get(v___x_2578_, 4);
v_env_2580_ = lean_ctor_get(v___x_2578_, 0);
v_nextMacroScope_2581_ = lean_ctor_get(v___x_2578_, 1);
v_ngen_2582_ = lean_ctor_get(v___x_2578_, 2);
v_auxDeclNGen_2583_ = lean_ctor_get(v___x_2578_, 3);
v_cache_2584_ = lean_ctor_get(v___x_2578_, 5);
v_recordedDeps_2585_ = lean_ctor_get(v___x_2578_, 6);
v_messages_2586_ = lean_ctor_get(v___x_2578_, 7);
v_infoState_2587_ = lean_ctor_get(v___x_2578_, 8);
v_snapshotTasks_2588_ = lean_ctor_get(v___x_2578_, 9);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2590_ = v___x_2578_;
v_isShared_2591_ = v_isSharedCheck_2618_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_snapshotTasks_2588_);
lean_inc(v_infoState_2587_);
lean_inc(v_messages_2586_);
lean_inc(v_recordedDeps_2585_);
lean_inc(v_cache_2584_);
lean_inc(v_traceState_2579_);
lean_inc(v_auxDeclNGen_2583_);
lean_inc(v_ngen_2582_);
lean_inc(v_nextMacroScope_2581_);
lean_inc(v_env_2580_);
lean_dec(v___x_2578_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2618_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
uint64_t v_tid_2592_; lean_object* v_traces_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2617_; 
v_tid_2592_ = lean_ctor_get_uint64(v_traceState_2579_, sizeof(void*)*1);
v_traces_2593_ = lean_ctor_get(v_traceState_2579_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_traceState_2579_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2595_ = v_traceState_2579_;
v_isShared_2596_ = v_isSharedCheck_2617_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_traces_2593_);
lean_dec(v_traceState_2579_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2617_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; double v___x_2599_; uint8_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2600_ = 0;
v___x_2601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2602_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2602_, 0, v_cls_2565_);
lean_ctor_set(v___x_2602_, 1, v___x_2598_);
lean_ctor_set(v___x_2602_, 2, v___x_2601_);
lean_ctor_set_float(v___x_2602_, sizeof(void*)*3, v___x_2599_);
lean_ctor_set_float(v___x_2602_, sizeof(void*)*3 + 8, v___x_2599_);
lean_ctor_set_uint8(v___x_2602_, sizeof(void*)*3 + 16, v___x_2600_);
v___x_2603_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2604_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v_a_2574_);
lean_ctor_set(v___x_2604_, 2, v___x_2603_);
lean_inc(v_ref_2572_);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v_ref_2572_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = l_Lean_PersistentArray_push___redArg(v_traces_2593_, v___x_2605_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2606_);
v___x_2608_ = v___x_2595_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2606_);
lean_ctor_set_uint64(v_reuseFailAlloc_2616_, sizeof(void*)*1, v_tid_2592_);
v___x_2608_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2610_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 4, v___x_2608_);
v___x_2610_ = v___x_2590_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_env_2580_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_nextMacroScope_2581_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_ngen_2582_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_auxDeclNGen_2583_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2615_, 5, v_cache_2584_);
lean_ctor_set(v_reuseFailAlloc_2615_, 6, v_recordedDeps_2585_);
lean_ctor_set(v_reuseFailAlloc_2615_, 7, v_messages_2586_);
lean_ctor_set(v_reuseFailAlloc_2615_, 8, v_infoState_2587_);
lean_ctor_set(v_reuseFailAlloc_2615_, 9, v_snapshotTasks_2588_);
v___x_2610_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_st_ref_put(v___y_2570_, v___x_2610_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2597_);
v___x_2613_ = v___x_2576_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2597_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2620_, lean_object* v_msg_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2620_, v_msg_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2627_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2630_ = l_Lean_stringToMessageData(v___x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2631_, lean_object* v___f_2632_, lean_object* v___x_2633_, lean_object* v___x_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; lean_object* v_a_2644_; lean_object* v___y_2648_; lean_object* v___x_2662_; 
v___x_2642_ = lean_st_mk_ref(v___x_2631_);
v___x_2662_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2642_, v___y_2636_, v___y_2638_, v___y_2640_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2664_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2634_, v___x_2633_, v___x_2642_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; 
lean_dec(v_a_2663_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___f_2632_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v_a_2644_ = v_a_2665_;
goto v___jp_2643_;
}
else
{
lean_object* v_a_2666_; uint8_t v___y_2668_; uint8_t v___x_2712_; 
v_a_2666_ = lean_ctor_get(v___x_2664_, 0);
v___x_2712_ = l_Lean_Exception_isInterrupt(v_a_2666_);
if (v___x_2712_ == 0)
{
uint8_t v___x_2713_; 
lean_inc(v_a_2666_);
v___x_2713_ = l_Lean_Exception_isRuntime(v_a_2666_);
v___y_2668_ = v___x_2713_;
goto v___jp_2667_;
}
else
{
v___y_2668_ = v___x_2712_;
goto v___jp_2667_;
}
v___jp_2667_:
{
if (v___y_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2669_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2663_, v___y_2668_, v___x_2642_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2702_; 
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2669_, 0);
lean_dec(v_unused_2703_);
v___x_2671_ = v___x_2669_;
v_isShared_2672_ = v_isSharedCheck_2702_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v___x_2669_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2702_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
uint8_t v___x_2673_; 
v___x_2673_ = l_Lean_Exception_isInterrupt(v_a_2666_);
if (v___x_2673_ == 0)
{
uint8_t v___x_2674_; 
lean_inc(v_a_2666_);
v___x_2674_ = l_Lean_Exception_isMaxRecDepth(v_a_2666_);
if (v___x_2674_ == 0)
{
lean_object* v_toCold_2675_; lean_object* v_options_2676_; uint8_t v_hasTrace_2677_; 
lean_del_object(v___x_2671_);
v_toCold_2675_ = lean_ctor_get(v___y_2639_, 0);
v_options_2676_ = lean_ctor_get(v_toCold_2675_, 2);
v_hasTrace_2677_ = lean_ctor_get_uint8(v_options_2676_, sizeof(void*)*1);
if (v_hasTrace_2677_ == 0)
{
lean_dec(v_a_2666_);
goto v___jp_2659_;
}
else
{
lean_object* v_inheritedTraceOptions_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v_inheritedTraceOptions_2678_ = lean_ctor_get(v_toCold_2675_, 11);
v___x_2679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2678_, v_options_2676_, v___x_2680_);
if (v___x_2681_ == 0)
{
lean_dec(v_a_2666_);
goto v___jp_2659_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2682_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2683_ = l_Lean_Exception_toMessageData(v_a_2666_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2679_, v___x_2684_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
lean_inc(v___x_2642_);
v___x_2687_ = lean_apply_10(v___f_2632_, v_a_2686_, v___x_2633_, v___x_2642_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, lean_box(0));
v___y_2648_ = v___x_2687_;
goto v___jp_2647_;
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v___x_2642_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___f_2632_);
v_a_2688_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2685_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2685_);
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
}
}
}
else
{
lean_object* v___x_2697_; 
lean_dec(v___x_2642_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___f_2632_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 1);
lean_ctor_set(v___x_2671_, 0, v_a_2666_);
v___x_2697_ = v___x_2671_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2666_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
lean_object* v___x_2700_; 
lean_dec(v___x_2642_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___f_2632_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 1);
lean_ctor_set(v___x_2671_, 0, v_a_2666_);
v___x_2700_ = v___x_2671_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2666_);
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
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_a_2666_);
lean_dec(v___x_2642_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___f_2632_);
v_a_2704_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2669_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2669_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_dec(v_a_2663_);
lean_dec(v___x_2642_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___f_2632_);
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v___x_2642_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___x_2634_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___f_2632_);
v_a_2714_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2662_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2662_);
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
v___jp_2643_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = lean_st_ref_get(v___x_2642_);
lean_dec(v___x_2642_);
lean_dec(v___x_2645_);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_a_2644_);
return v___x_2646_;
}
v___jp_2647_:
{
if (lean_obj_tag(v___y_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v_a_2650_; 
v_a_2649_ = lean_ctor_get(v___y_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___y_2648_, 1);
v_a_2650_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_a_2650_);
lean_dec(v_a_2649_);
v_a_2644_ = v_a_2650_;
goto v___jp_2643_;
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v___x_2642_);
v_a_2651_ = lean_ctor_get(v___y_2648_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___y_2648_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___y_2648_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___y_2648_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
v___jp_2659_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_box(0);
lean_inc(v___x_2642_);
v___x_2661_ = lean_apply_10(v___f_2632_, v___x_2660_, v___x_2633_, v___x_2642_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, lean_box(0));
v___y_2648_ = v___x_2661_;
goto v___jp_2647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2722_, lean_object* v___f_2723_, lean_object* v___x_2724_, lean_object* v___x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2722_, v___f_2723_, v___x_2724_, v___x_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2734_, uint8_t v___x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2734_, v___x_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2744_, lean_object* v___x_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
uint8_t v___x_11347__boxed_2753_; lean_object* v_res_2754_; 
v___x_11347__boxed_2753_ = lean_unbox(v___x_2745_);
v_res_2754_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2744_, v___x_11347__boxed_2753_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2755_, lean_object* v_msg_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_ref_2762_; lean_object* v___x_2763_; lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2809_; 
v_ref_2762_ = lean_ctor_get(v___y_2759_, 2);
v___x_2763_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2809_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2809_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v_traceState_2769_; lean_object* v_env_2770_; lean_object* v_nextMacroScope_2771_; lean_object* v_ngen_2772_; lean_object* v_auxDeclNGen_2773_; lean_object* v_cache_2774_; lean_object* v_recordedDeps_2775_; lean_object* v_messages_2776_; lean_object* v_infoState_2777_; lean_object* v_snapshotTasks_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2808_; 
v___x_2768_ = lean_st_ref_take(v___y_2760_);
v_traceState_2769_ = lean_ctor_get(v___x_2768_, 4);
v_env_2770_ = lean_ctor_get(v___x_2768_, 0);
v_nextMacroScope_2771_ = lean_ctor_get(v___x_2768_, 1);
v_ngen_2772_ = lean_ctor_get(v___x_2768_, 2);
v_auxDeclNGen_2773_ = lean_ctor_get(v___x_2768_, 3);
v_cache_2774_ = lean_ctor_get(v___x_2768_, 5);
v_recordedDeps_2775_ = lean_ctor_get(v___x_2768_, 6);
v_messages_2776_ = lean_ctor_get(v___x_2768_, 7);
v_infoState_2777_ = lean_ctor_get(v___x_2768_, 8);
v_snapshotTasks_2778_ = lean_ctor_get(v___x_2768_, 9);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2780_ = v___x_2768_;
v_isShared_2781_ = v_isSharedCheck_2808_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_snapshotTasks_2778_);
lean_inc(v_infoState_2777_);
lean_inc(v_messages_2776_);
lean_inc(v_recordedDeps_2775_);
lean_inc(v_cache_2774_);
lean_inc(v_traceState_2769_);
lean_inc(v_auxDeclNGen_2773_);
lean_inc(v_ngen_2772_);
lean_inc(v_nextMacroScope_2771_);
lean_inc(v_env_2770_);
lean_dec(v___x_2768_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2808_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
uint64_t v_tid_2782_; lean_object* v_traces_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2807_; 
v_tid_2782_ = lean_ctor_get_uint64(v_traceState_2769_, sizeof(void*)*1);
v_traces_2783_ = lean_ctor_get(v_traceState_2769_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_traceState_2769_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2785_ = v_traceState_2769_;
v_isShared_2786_ = v_isSharedCheck_2807_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_traces_2783_);
lean_dec(v_traceState_2769_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2807_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; double v___x_2789_; uint8_t v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_box(0);
v___x_2789_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2790_ = 0;
v___x_2791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2792_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2792_, 0, v_cls_2755_);
lean_ctor_set(v___x_2792_, 1, v___x_2788_);
lean_ctor_set(v___x_2792_, 2, v___x_2791_);
lean_ctor_set_float(v___x_2792_, sizeof(void*)*3, v___x_2789_);
lean_ctor_set_float(v___x_2792_, sizeof(void*)*3 + 8, v___x_2789_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*3 + 16, v___x_2790_);
v___x_2793_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2794_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v_a_2764_);
lean_ctor_set(v___x_2794_, 2, v___x_2793_);
lean_inc(v_ref_2762_);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v_ref_2762_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_PersistentArray_push___redArg(v_traces_2783_, v___x_2795_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2796_);
v___x_2798_ = v___x_2785_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2796_);
lean_ctor_set_uint64(v_reuseFailAlloc_2806_, sizeof(void*)*1, v_tid_2782_);
v___x_2798_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2800_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 4, v___x_2798_);
v___x_2800_ = v___x_2780_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_env_2770_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_nextMacroScope_2771_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_ngen_2772_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_auxDeclNGen_2773_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2805_, 5, v_cache_2774_);
lean_ctor_set(v_reuseFailAlloc_2805_, 6, v_recordedDeps_2775_);
lean_ctor_set(v_reuseFailAlloc_2805_, 7, v_messages_2776_);
lean_ctor_set(v_reuseFailAlloc_2805_, 8, v_infoState_2777_);
lean_ctor_set(v_reuseFailAlloc_2805_, 9, v_snapshotTasks_2778_);
v___x_2800_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = lean_st_ref_put(v___y_2760_, v___x_2800_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2787_);
v___x_2803_ = v___x_2766_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2787_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2810_, lean_object* v_msg_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2810_, v_msg_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
return v_res_2817_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2820_ = l_Lean_stringToMessageData(v___x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v___f_2821_, lean_object* v_term_2822_, lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___y_2831_; lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2822_, v___x_2823_, v___x_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v___f_2821_);
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_fst_2857_; lean_object* v___x_2859_; 
v_fst_2857_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_fst_2857_);
lean_dec(v_a_2853_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_fst_2857_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_fst_2857_);
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
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2902_; 
v_a_2862_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2864_ = v___x_2852_;
v_isShared_2865_ = v_isSharedCheck_2902_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2852_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2902_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
uint8_t v___y_2867_; uint8_t v___x_2900_; 
v___x_2900_ = l_Lean_Exception_isInterrupt(v_a_2862_);
if (v___x_2900_ == 0)
{
uint8_t v___x_2901_; 
lean_inc(v_a_2862_);
v___x_2901_ = l_Lean_Exception_isRuntime(v_a_2862_);
v___y_2867_ = v___x_2901_;
goto v___jp_2866_;
}
else
{
v___y_2867_ = v___x_2900_;
goto v___jp_2866_;
}
v___jp_2866_:
{
if (v___y_2867_ == 0)
{
uint8_t v___x_2868_; 
v___x_2868_ = l_Lean_Exception_isInterrupt(v_a_2862_);
if (v___x_2868_ == 0)
{
uint8_t v___x_2869_; 
lean_inc(v_a_2862_);
v___x_2869_ = l_Lean_Exception_isMaxRecDepth(v_a_2862_);
if (v___x_2869_ == 0)
{
lean_object* v_toCold_2870_; lean_object* v_options_2871_; uint8_t v_hasTrace_2872_; 
lean_del_object(v___x_2864_);
v_toCold_2870_ = lean_ctor_get(v___y_2827_, 0);
v_options_2871_ = lean_ctor_get(v_toCold_2870_, 2);
v_hasTrace_2872_ = lean_ctor_get_uint8(v_options_2871_, sizeof(void*)*1);
if (v_hasTrace_2872_ == 0)
{
lean_dec(v_a_2862_);
goto v___jp_2849_;
}
else
{
lean_object* v_inheritedTraceOptions_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v_inheritedTraceOptions_2873_ = lean_ctor_get(v_toCold_2870_, 11);
v___x_2874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2876_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2873_, v_options_2871_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_dec(v_a_2862_);
goto v___jp_2849_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2877_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2878_ = l_Lean_Exception_toMessageData(v_a_2862_);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2874_, v___x_2879_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = lean_apply_6(v___f_2821_, v_a_2881_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, lean_box(0));
v___y_2831_ = v___x_2882_;
goto v___jp_2830_;
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v___f_2821_);
v_a_2883_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2880_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2880_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
}
else
{
lean_object* v___x_2892_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v___f_2821_);
if (v_isShared_2865_ == 0)
{
v___x_2892_ = v___x_2864_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2862_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
else
{
lean_object* v___x_2895_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v___f_2821_);
if (v_isShared_2865_ == 0)
{
v___x_2895_ = v___x_2864_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2862_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v___x_2898_; 
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v___f_2821_);
if (v_isShared_2865_ == 0)
{
v___x_2898_ = v___x_2864_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2862_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
v___jp_2830_:
{
if (lean_obj_tag(v___y_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2840_; 
v_a_2832_ = lean_ctor_get(v___y_2831_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___y_2831_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2834_ = v___y_2831_;
v_isShared_2835_ = v_isSharedCheck_2840_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___y_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2840_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_a_2836_; lean_object* v___x_2838_; 
v_a_2836_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_a_2836_);
lean_dec(v_a_2832_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_a_2836_);
v___x_2838_ = v___x_2834_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
v_a_2841_ = lean_ctor_get(v___y_2831_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___y_2831_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___y_2831_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___y_2831_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
v___jp_2849_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_box(0);
v___x_2851_ = lean_apply_6(v___f_2821_, v___x_2850_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, lean_box(0));
v___y_2831_ = v___x_2851_;
goto v___jp_2830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed(lean_object* v___f_2903_, lean_object* v_term_2904_, lean_object* v___x_2905_, lean_object* v___x_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(v___f_2903_, v_term_2904_, v___x_2905_, v___x_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2913_, lean_object* v_vals_2914_, lean_object* v_i_2915_, lean_object* v_k_2916_){
_start:
{
lean_object* v___x_2917_; uint8_t v___x_2918_; 
v___x_2917_ = lean_array_get_size(v_keys_2913_);
v___x_2918_ = lean_nat_dec_lt(v_i_2915_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
lean_dec(v_i_2915_);
v___x_2919_ = lean_box(0);
return v___x_2919_;
}
else
{
lean_object* v_k_x27_2920_; uint8_t v___x_2921_; 
v_k_x27_2920_ = lean_array_fget_borrowed(v_keys_2913_, v_i_2915_);
v___x_2921_ = l_Lean_instBEqMVarId_beq(v_k_2916_, v_k_x27_2920_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_nat_add(v_i_2915_, v___x_2922_);
lean_dec(v_i_2915_);
v_i_2915_ = v___x_2923_;
goto _start;
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_array_fget_borrowed(v_vals_2914_, v_i_2915_);
lean_dec(v_i_2915_);
lean_inc(v___x_2925_);
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2927_, lean_object* v_vals_2928_, lean_object* v_i_2929_, lean_object* v_k_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_2927_, v_vals_2928_, v_i_2929_, v_k_2930_);
lean_dec(v_k_2930_);
lean_dec_ref(v_vals_2928_);
lean_dec_ref(v_keys_2927_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(lean_object* v_x_2932_, size_t v_x_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2932_) == 0)
{
lean_object* v_es_2935_; lean_object* v___x_2936_; size_t v___x_2937_; size_t v___x_2938_; lean_object* v_j_2939_; lean_object* v___x_2940_; 
v_es_2935_ = lean_ctor_get(v_x_2932_, 0);
v___x_2936_ = lean_box(2);
v___x_2937_ = ((size_t)31ULL);
v___x_2938_ = lean_usize_land(v_x_2933_, v___x_2937_);
v_j_2939_ = lean_usize_to_nat(v___x_2938_);
v___x_2940_ = lean_array_get_borrowed(v___x_2936_, v_es_2935_, v_j_2939_);
lean_dec(v_j_2939_);
switch(lean_obj_tag(v___x_2940_))
{
case 0:
{
lean_object* v_key_2941_; lean_object* v_val_2942_; uint8_t v___x_2943_; 
v_key_2941_ = lean_ctor_get(v___x_2940_, 0);
v_val_2942_ = lean_ctor_get(v___x_2940_, 1);
v___x_2943_ = l_Lean_instBEqMVarId_beq(v_x_2934_, v_key_2941_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
v___x_2944_ = lean_box(0);
return v___x_2944_;
}
else
{
lean_object* v___x_2945_; 
lean_inc(v_val_2942_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v_val_2942_);
return v___x_2945_;
}
}
case 1:
{
lean_object* v_node_2946_; size_t v___x_2947_; size_t v___x_2948_; 
v_node_2946_ = lean_ctor_get(v___x_2940_, 0);
v___x_2947_ = ((size_t)5ULL);
v___x_2948_ = lean_usize_shift_right(v_x_2933_, v___x_2947_);
v_x_2932_ = v_node_2946_;
v_x_2933_ = v___x_2948_;
goto _start;
}
default: 
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_box(0);
return v___x_2950_;
}
}
}
else
{
lean_object* v_ks_2951_; lean_object* v_vs_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_ks_2951_ = lean_ctor_get(v_x_2932_, 0);
v_vs_2952_ = lean_ctor_get(v_x_2932_, 1);
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_ks_2951_, v_vs_2952_, v___x_2953_, v_x_2934_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg___boxed(lean_object* v_x_2955_, lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
size_t v_x_11666__boxed_2958_; lean_object* v_res_2959_; 
v_x_11666__boxed_2958_ = lean_unbox_usize(v_x_2956_);
lean_dec(v_x_2956_);
v_res_2959_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2955_, v_x_11666__boxed_2958_, v_x_2957_);
lean_dec(v_x_2957_);
lean_dec_ref(v_x_2955_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(lean_object* v_x_2960_, lean_object* v_x_2961_){
_start:
{
uint64_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = l_Lean_instHashableMVarId_hash(v_x_2961_);
v___x_2963_ = lean_uint64_to_usize(v___x_2962_);
v___x_2964_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2960_, v___x_2963_, v_x_2961_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg___boxed(lean_object* v_x_2965_, lean_object* v_x_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_2965_, v_x_2966_);
lean_dec(v_x_2966_);
lean_dec_ref(v_x_2965_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(lean_object* v_c_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_mctx_2997_; lean_object* v_env_2998_; lean_object* v_opts_2999_; lean_object* v_namingCtx_3000_; lean_object* v_goal_3001_; lean_object* v_decls_3002_; lean_object* v___x_3003_; 
v_mctx_2997_ = lean_ctor_get(v_c_2993_, 3);
lean_inc_ref(v_mctx_2997_);
v_env_2998_ = lean_ctor_get(v_c_2993_, 2);
lean_inc_ref(v_env_2998_);
v_opts_2999_ = lean_ctor_get(v_c_2993_, 4);
lean_inc_ref(v_opts_2999_);
v_namingCtx_3000_ = lean_ctor_get(v_c_2993_, 5);
lean_inc_ref(v_namingCtx_3000_);
v_goal_3001_ = lean_ctor_get(v_c_2993_, 6);
lean_inc(v_goal_3001_);
lean_dec_ref(v_c_2993_);
v_decls_3002_ = lean_ctor_get(v_mctx_2997_, 5);
v___x_3003_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3002_, v_goal_3001_);
if (lean_obj_tag(v___x_3003_) == 1)
{
lean_object* v_val_3004_; lean_object* v_lctx_3005_; lean_object* v___f_3006_; lean_object* v___f_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___f_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; lean_object* v_term_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; 
v_val_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v_lctx_3005_ = lean_ctor_get(v_val_3004_, 1);
lean_inc_ref(v_lctx_3005_);
lean_dec(v_val_3004_);
v___f_3006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__0));
v___f_3007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__1));
v___x_3008_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__3));
v___x_3009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__4));
v___x_3010_ = lean_box(0);
lean_inc(v_goal_3001_);
v___x_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3011_, 0, v_goal_3001_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___f_3012_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed), 11, 4);
lean_closure_set(v___f_3012_, 0, v___x_3011_);
lean_closure_set(v___f_3012_, 1, v___f_3006_);
lean_closure_set(v___f_3012_, 2, v___x_3009_);
lean_closure_set(v___f_3012_, 3, v___x_3008_);
v___x_3013_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed), 10, 3);
lean_closure_set(v___x_3013_, 0, lean_box(0));
lean_closure_set(v___x_3013_, 1, v_goal_3001_);
lean_closure_set(v___x_3013_, 2, v___f_3012_);
v___x_3014_ = 1;
v___x_3015_ = lean_box(v___x_3014_);
v_term_3016_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed), 9, 2);
lean_closure_set(v_term_3016_, 0, v___x_3013_);
lean_closure_set(v_term_3016_, 1, v___x_3015_);
v___x_3017_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__6));
v___x_3018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__7));
v___f_3019_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___boxed), 9, 4);
lean_closure_set(v___f_3019_, 0, v___f_3007_);
lean_closure_set(v___f_3019_, 1, v_term_3016_);
lean_closure_set(v___f_3019_, 2, v___x_3017_);
lean_closure_set(v___f_3019_, 3, v___x_3018_);
v___x_3020_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_2998_, v_mctx_2997_, v_lctx_3005_, v_opts_2999_, v_namingCtx_3000_, v___f_3019_, v_a_2994_, v_a_2995_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_dec(v___x_3003_);
lean_dec(v_goal_3001_);
lean_dec_ref(v_namingCtx_3000_);
lean_dec_ref(v_opts_2999_);
lean_dec_ref(v_env_2998_);
lean_dec_ref(v_mctx_2997_);
v___x_3021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__0));
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
return v___x_3022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___boxed(lean_object* v_c_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_c_3023_, v_a_3024_, v_a_3025_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(lean_object* v_00_u03b2_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_x_3029_, v_x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___boxed(lean_object* v_00_u03b2_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0(v_00_u03b2_3032_, v_x_3033_, v_x_3034_);
lean_dec(v_x_3034_);
lean_dec_ref(v_x_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(lean_object* v_cls_3036_, lean_object* v_msg_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_3036_, v_msg_3037_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___boxed(lean_object* v_cls_3048_, lean_object* v_msg_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1(v_cls_3048_, v_msg_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(lean_object* v_00_u03b2_3060_, lean_object* v_x_3061_, size_t v_x_3062_, lean_object* v_x_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_3061_, v_x_3062_, v_x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3065_, lean_object* v_x_3066_, lean_object* v_x_3067_, lean_object* v_x_3068_){
_start:
{
size_t v_x_11923__boxed_3069_; lean_object* v_res_3070_; 
v_x_11923__boxed_3069_ = lean_unbox_usize(v_x_3067_);
lean_dec(v_x_3067_);
v_res_3070_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3065_, v_x_3066_, v_x_11923__boxed_3069_, v_x_3068_);
lean_dec(v_x_3068_);
lean_dec_ref(v_x_3066_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3071_, lean_object* v_keys_3072_, lean_object* v_vals_3073_, lean_object* v_heq_3074_, lean_object* v_i_3075_, lean_object* v_k_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___redArg(v_keys_3072_, v_vals_3073_, v_i_3075_, v_k_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3078_, lean_object* v_keys_3079_, lean_object* v_vals_3080_, lean_object* v_heq_3081_, lean_object* v_i_3082_, lean_object* v_k_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0_spec__2(v_00_u03b2_3078_, v_keys_3079_, v_vals_3080_, v_heq_3081_, v_i_3082_, v_k_3083_);
lean_dec(v_k_3083_);
lean_dec_ref(v_vals_3080_);
lean_dec_ref(v_keys_3079_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(uint8_t v___x_3087_, lean_object* v___x_3088_, lean_object* v_ref_3089_, lean_object* v_a_3090_, lean_object* v___x_3091_, lean_object* v___x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
if (v___x_3087_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3088_);
v___x_3097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__0));
v___x_3098_ = lean_box(0);
v___x_3099_ = 4;
v___x_3100_ = l_Lean_MessageData_nil;
v___x_3101_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(v_ref_3089_, v_a_3090_, v___x_3096_, v___x_3097_, v___x_3098_, v___x_3099_, v___x_3100_, v___y_3093_, v___y_3094_);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3102_ = lean_array_get(v___x_3091_, v_a_3090_, v___x_3092_);
lean_dec_ref(v_a_3090_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3088_);
v___x_3104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___closed__1));
v___x_3105_ = lean_box(0);
v___x_3106_ = 4;
v___x_3107_ = l_Lean_MessageData_nil;
v___x_3108_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_ref_3089_, v___x_3102_, v___x_3103_, v___x_3104_, v___x_3105_, v___x_3106_, v___x_3107_, v___y_3093_, v___y_3094_);
return v___x_3108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed(lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v_ref_3111_, lean_object* v_a_3112_, lean_object* v___x_3113_, lean_object* v___x_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
uint8_t v___x_3494__boxed_3118_; lean_object* v_res_3119_; 
v___x_3494__boxed_3118_ = lean_unbox(v___x_3109_);
v_res_3119_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3494__boxed_3118_, v___x_3110_, v_ref_3111_, v_a_3112_, v___x_3113_, v___x_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___x_3114_);
lean_dec_ref(v___x_3113_);
return v_res_3119_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3120_, uint8_t v___y_3121_, lean_object* v_x_3122_){
_start:
{
if (lean_obj_tag(v_x_3122_) == 1)
{
lean_object* v_pre_3123_; 
v_pre_3123_ = lean_ctor_get(v_x_3122_, 0);
if (lean_obj_tag(v_pre_3123_) == 0)
{
lean_object* v_str_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v_str_3124_ = lean_ctor_get(v_x_3122_, 1);
v___x_3125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1));
v___x_3126_ = lean_string_dec_eq(v_str_3124_, v___x_3125_);
if (v___x_3126_ == 0)
{
return v___x_3126_;
}
else
{
return v_suppressElabErrors_3120_;
}
}
else
{
return v___y_3121_;
}
}
else
{
return v___y_3121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3127_, lean_object* v___y_3128_, lean_object* v_x_3129_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3130_; uint8_t v___y_3547__boxed_3131_; uint8_t v_res_3132_; lean_object* v_r_3133_; 
v_suppressElabErrors_boxed_3130_ = lean_unbox(v_suppressElabErrors_3127_);
v___y_3547__boxed_3131_ = lean_unbox(v___y_3128_);
v_res_3132_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3130_, v___y_3547__boxed_3131_, v_x_3129_);
lean_dec(v_x_3129_);
v_r_3133_ = lean_box(v_res_3132_);
return v_r_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3134_, lean_object* v_msgData_3135_, uint8_t v_severity_3136_, uint8_t v_isSilent_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___y_3142_; uint8_t v___y_3143_; lean_object* v___y_3144_; uint8_t v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; uint8_t v___y_3207_; lean_object* v___y_3208_; uint8_t v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3235_; uint8_t v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; uint8_t v___y_3243_; uint8_t v___y_3244_; uint8_t v___y_3245_; uint8_t v___x_3260_; uint8_t v___y_3262_; uint8_t v___y_3263_; uint8_t v___y_3264_; uint8_t v___y_3266_; uint8_t v___x_3278_; 
v___x_3260_ = 2;
v___x_3278_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3136_, v___x_3260_);
if (v___x_3278_ == 0)
{
v___y_3266_ = v___x_3278_;
goto v___jp_3265_;
}
else
{
uint8_t v___x_3279_; 
lean_inc_ref(v_msgData_3135_);
v___x_3279_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3135_);
v___y_3266_ = v___x_3279_;
goto v___jp_3265_;
}
v___jp_3141_:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_Elab_Command_getScope___redArg(v___y_3149_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v_currNamespace_3152_; lean_object* v___x_3153_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v_currNamespace_3152_ = lean_ctor_get(v_a_3151_, 2);
lean_inc(v_currNamespace_3152_);
lean_dec(v_a_3151_);
v___x_3153_ = l_Lean_Elab_Command_getScope___redArg(v___y_3149_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3189_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3189_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3189_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_openDecls_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_env_3163_; lean_object* v_messages_3164_; lean_object* v_scopes_3165_; lean_object* v_usedQuotCtxts_3166_; lean_object* v_nextMacroScope_3167_; lean_object* v_maxRecDepth_3168_; lean_object* v_ngen_3169_; lean_object* v_auxDeclNGen_3170_; lean_object* v_infoState_3171_; lean_object* v_traceState_3172_; lean_object* v_snapshotTasks_3173_; lean_object* v_prevLinterStates_3174_; lean_object* v_codeQualityEntryTasks_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3188_; 
v_openDecls_3158_ = lean_ctor_get(v_a_3154_, 3);
lean_inc(v_openDecls_3158_);
lean_dec(v_a_3154_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_currNamespace_3152_);
lean_ctor_set(v___x_3159_, 1, v_openDecls_3158_);
v___x_3160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v___y_3148_);
lean_inc_ref(v___y_3142_);
lean_inc_ref(v___y_3147_);
v___x_3161_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3161_, 0, v___y_3147_);
lean_ctor_set(v___x_3161_, 1, v___y_3144_);
lean_ctor_set(v___x_3161_, 2, v___y_3146_);
lean_ctor_set(v___x_3161_, 3, v___y_3142_);
lean_ctor_set(v___x_3161_, 4, v___x_3160_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*5, v___y_3143_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*5 + 1, v___y_3145_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*5 + 2, v_isSilent_3137_);
v___x_3162_ = lean_st_ref_take(v___y_3149_);
v_env_3163_ = lean_ctor_get(v___x_3162_, 0);
v_messages_3164_ = lean_ctor_get(v___x_3162_, 1);
v_scopes_3165_ = lean_ctor_get(v___x_3162_, 2);
v_usedQuotCtxts_3166_ = lean_ctor_get(v___x_3162_, 3);
v_nextMacroScope_3167_ = lean_ctor_get(v___x_3162_, 4);
v_maxRecDepth_3168_ = lean_ctor_get(v___x_3162_, 5);
v_ngen_3169_ = lean_ctor_get(v___x_3162_, 6);
v_auxDeclNGen_3170_ = lean_ctor_get(v___x_3162_, 7);
v_infoState_3171_ = lean_ctor_get(v___x_3162_, 8);
v_traceState_3172_ = lean_ctor_get(v___x_3162_, 9);
v_snapshotTasks_3173_ = lean_ctor_get(v___x_3162_, 10);
v_prevLinterStates_3174_ = lean_ctor_get(v___x_3162_, 11);
v_codeQualityEntryTasks_3175_ = lean_ctor_get(v___x_3162_, 12);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3177_ = v___x_3162_;
v_isShared_3178_ = v_isSharedCheck_3188_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3175_);
lean_inc(v_prevLinterStates_3174_);
lean_inc(v_snapshotTasks_3173_);
lean_inc(v_traceState_3172_);
lean_inc(v_infoState_3171_);
lean_inc(v_auxDeclNGen_3170_);
lean_inc(v_ngen_3169_);
lean_inc(v_maxRecDepth_3168_);
lean_inc(v_nextMacroScope_3167_);
lean_inc(v_usedQuotCtxts_3166_);
lean_inc(v_scopes_3165_);
lean_inc(v_messages_3164_);
lean_inc(v_env_3163_);
lean_dec(v___x_3162_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3188_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3179_ = lean_box(0);
v___x_3180_ = l_Lean_MessageLog_add(v___x_3161_, v_messages_3164_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 1, v___x_3180_);
v___x_3182_ = v___x_3177_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_env_3163_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_scopes_3165_);
lean_ctor_set(v_reuseFailAlloc_3187_, 3, v_usedQuotCtxts_3166_);
lean_ctor_set(v_reuseFailAlloc_3187_, 4, v_nextMacroScope_3167_);
lean_ctor_set(v_reuseFailAlloc_3187_, 5, v_maxRecDepth_3168_);
lean_ctor_set(v_reuseFailAlloc_3187_, 6, v_ngen_3169_);
lean_ctor_set(v_reuseFailAlloc_3187_, 7, v_auxDeclNGen_3170_);
lean_ctor_set(v_reuseFailAlloc_3187_, 8, v_infoState_3171_);
lean_ctor_set(v_reuseFailAlloc_3187_, 9, v_traceState_3172_);
lean_ctor_set(v_reuseFailAlloc_3187_, 10, v_snapshotTasks_3173_);
lean_ctor_set(v_reuseFailAlloc_3187_, 11, v_prevLinterStates_3174_);
lean_ctor_set(v_reuseFailAlloc_3187_, 12, v_codeQualityEntryTasks_3175_);
v___x_3182_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3183_ = lean_st_ref_put(v___y_3149_, v___x_3182_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v___x_3179_);
v___x_3185_ = v___x_3156_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3179_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_currNamespace_3152_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
v_a_3190_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3153_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3153_);
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
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3144_);
v_a_3198_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3150_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3150_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
v___jp_3206_:
{
lean_object* v_fileName_3212_; lean_object* v_fileMap_3213_; uint8_t v_suppressElabErrors_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3233_; 
v_fileName_3212_ = lean_ctor_get(v___y_3138_, 0);
v_fileMap_3213_ = lean_ctor_get(v___y_3138_, 1);
v_suppressElabErrors_3214_ = lean_ctor_get_uint8(v___y_3138_, sizeof(void*)*10);
v___x_3215_ = lean_box(v_suppressElabErrors_3214_);
v___x_3216_ = lean_box(v___y_3207_);
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3217_, 0, v___x_3215_);
lean_closure_set(v___f_3217_, 1, v___x_3216_);
v___x_3218_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3135_);
v___x_3219_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v___x_3218_, v___y_3139_);
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3233_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3233_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_inc_ref_n(v_fileMap_3213_, 2);
v___x_3224_ = l_Lean_FileMap_toPosition(v_fileMap_3213_, v___y_3208_);
lean_dec(v___y_3208_);
v___x_3225_ = l_Lean_FileMap_toPosition(v_fileMap_3213_, v___y_3211_);
lean_dec(v___y_3211_);
v___x_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
v___x_3227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3214_ == 0)
{
lean_del_object(v___x_3222_);
lean_dec_ref(v___f_3217_);
v___y_3142_ = v___x_3227_;
v___y_3143_ = v___y_3209_;
v___y_3144_ = v___x_3224_;
v___y_3145_ = v___y_3210_;
v___y_3146_ = v___x_3226_;
v___y_3147_ = v_fileName_3212_;
v___y_3148_ = v_a_3220_;
v___y_3149_ = v___y_3139_;
goto v___jp_3141_;
}
else
{
uint8_t v___x_3228_; 
lean_inc(v_a_3220_);
v___x_3228_ = l_Lean_MessageData_hasTag(v___f_3217_, v_a_3220_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
lean_dec_ref_known(v___x_3226_, 1);
lean_dec_ref(v___x_3224_);
lean_dec(v_a_3220_);
v___x_3229_ = lean_box(0);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3229_);
v___x_3231_ = v___x_3222_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
else
{
lean_del_object(v___x_3222_);
v___y_3142_ = v___x_3227_;
v___y_3143_ = v___y_3209_;
v___y_3144_ = v___x_3224_;
v___y_3145_ = v___y_3210_;
v___y_3146_ = v___x_3226_;
v___y_3147_ = v_fileName_3212_;
v___y_3148_ = v_a_3220_;
v___y_3149_ = v___y_3139_;
goto v___jp_3141_;
}
}
}
}
v___jp_3234_:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_Syntax_getTailPos_x3f(v___y_3238_, v___y_3236_);
lean_dec(v___y_3238_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_inc(v___y_3239_);
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3239_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3239_;
goto v___jp_3206_;
}
else
{
lean_object* v_val_3241_; 
v_val_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_val_3241_);
lean_dec_ref_known(v___x_3240_, 1);
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3239_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v_val_3241_;
goto v___jp_3206_;
}
}
v___jp_3242_:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Elab_Command_getRef___redArg(v___y_3138_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v_ref_3248_; lean_object* v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v_ref_3248_ = l_Lean_replaceRef(v_ref_3134_, v_a_3247_);
lean_dec(v_a_3247_);
v___x_3249_ = l_Lean_Syntax_getPos_x3f(v_ref_3248_, v___y_3244_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_unsigned_to_nat(0u);
v___y_3235_ = v___y_3243_;
v___y_3236_ = v___y_3244_;
v___y_3237_ = v___y_3245_;
v___y_3238_ = v_ref_3248_;
v___y_3239_ = v___x_3250_;
goto v___jp_3234_;
}
else
{
lean_object* v_val_3251_; 
v_val_3251_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_val_3251_);
lean_dec_ref_known(v___x_3249_, 1);
v___y_3235_ = v___y_3243_;
v___y_3236_ = v___y_3244_;
v___y_3237_ = v___y_3245_;
v___y_3238_ = v_ref_3248_;
v___y_3239_ = v_val_3251_;
goto v___jp_3234_;
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v_msgData_3135_);
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
if (v___y_3264_ == 0)
{
v___y_3243_ = v___y_3262_;
v___y_3244_ = v___y_3263_;
v___y_3245_ = v_severity_3136_;
goto v___jp_3242_;
}
else
{
v___y_3243_ = v___y_3262_;
v___y_3244_ = v___y_3263_;
v___y_3245_ = v___x_3260_;
goto v___jp_3242_;
}
}
v___jp_3265_:
{
if (v___y_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v_scopes_3269_; lean_object* v___x_3270_; lean_object* v_opts_3271_; uint8_t v___x_3272_; uint8_t v___x_3273_; 
v___x_3267_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3268_ = lean_st_ref_get(v___y_3139_);
v_scopes_3269_ = lean_ctor_get(v___x_3268_, 2);
lean_inc(v_scopes_3269_);
lean_dec(v___x_3268_);
v___x_3270_ = l_List_head_x21___redArg(v___x_3267_, v_scopes_3269_);
lean_dec(v_scopes_3269_);
v_opts_3271_ = lean_ctor_get(v___x_3270_, 1);
lean_inc_ref(v_opts_3271_);
lean_dec(v___x_3270_);
v___x_3272_ = 1;
v___x_3273_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3136_, v___x_3272_);
if (v___x_3273_ == 0)
{
lean_dec_ref(v_opts_3271_);
v___y_3262_ = v___y_3266_;
v___y_3263_ = v___y_3266_;
v___y_3264_ = v___x_3273_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = l_Lean_warningAsError;
v___x_3275_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3271_, v___x_3274_);
lean_dec_ref(v_opts_3271_);
v___y_3262_ = v___y_3266_;
v___y_3263_ = v___y_3266_;
v___y_3264_ = v___x_3275_;
goto v___jp_3261_;
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec_ref(v_msgData_3135_);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3280_, lean_object* v_msgData_3281_, lean_object* v_severity_3282_, lean_object* v_isSilent_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v_severity_boxed_3287_; uint8_t v_isSilent_boxed_3288_; lean_object* v_res_3289_; 
v_severity_boxed_3287_ = lean_unbox(v_severity_3282_);
v_isSilent_boxed_3288_ = lean_unbox(v_isSilent_3283_);
v_res_3289_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3280_, v_msgData_3281_, v_severity_boxed_3287_, v_isSilent_boxed_3288_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v_ref_3280_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3290_, lean_object* v_msgData_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
uint8_t v___x_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = 0;
v___x_3296_ = 0;
v___x_3297_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3290_, v_msgData_3291_, v___x_3295_, v___x_3296_, v___y_3292_, v___y_3293_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3298_, lean_object* v_msgData_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3298_, v_msgData_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v_ref_3298_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3308_ = lean_string_append(v___x_3307_, v___x_3305_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3309_, lean_object* v_x_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3309_, v_x_3310_);
lean_dec_ref(v_x_3310_);
lean_dec_ref(v___x_3309_);
return v_res_3311_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3314_ = l_Lean_stringToMessageData(v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3320_ = l_Lean_stringToMessageData(v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3321_, uint8_t v___x_3322_, lean_object* v___x_3323_, lean_object* v_insertPos_3324_, lean_object* v_cmdLine_3325_, lean_object* v_ref_3326_, size_t v_sz_3327_, size_t v_i_3328_, lean_object* v_bs_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
uint8_t v___x_3333_; 
v___x_3333_ = lean_usize_dec_lt(v_i_3328_, v_sz_3327_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
lean_dec_ref(v___x_3323_);
lean_dec_ref(v___x_3321_);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_bs_3329_);
return v___x_3334_;
}
else
{
lean_object* v_v_3335_; lean_object* v___x_3336_; lean_object* v_bs_x27_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_v_3335_ = lean_array_uget(v_bs_3329_, v_i_3328_);
v___x_3336_ = lean_unsigned_to_nat(0u);
v_bs_x27_3337_ = lean_array_uset(v_bs_3329_, v_i_3328_, v___x_3336_);
lean_inc(v_v_3335_);
v___x_3338_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3338_, 0, v_v_3335_);
v___x_3339_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3338_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___f_3343_; lean_object* v___x_3344_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = l_Std_Format_defWidth;
v___x_3342_ = l_Std_Format_pretty(v_a_3340_, v___x_3341_, v___x_3336_, v___x_3336_);
lean_inc_ref(v___x_3342_);
v___f_3343_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3343_, 0, v___x_3342_);
lean_inc_ref(v___x_3321_);
v___x_3344_ = lean_string_append(v___x_3321_, v___x_3342_);
lean_dec_ref(v___x_3342_);
if (v___x_3322_ == 0)
{
goto v___jp_3345_;
}
else
{
lean_object* v___x_3356_; lean_object* v_line_3357_; lean_object* v_column_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3393_; 
lean_inc_ref(v___x_3323_);
v___x_3356_ = l_Lean_FileMap_toPosition(v___x_3323_, v_insertPos_3324_);
v_line_3357_ = lean_ctor_get(v___x_3356_, 0);
v_column_3358_ = lean_ctor_get(v___x_3356_, 1);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3360_ = v___x_3356_;
v_isShared_3361_ = v_isSharedCheck_3393_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_column_3358_);
lean_inc(v_line_3357_);
lean_dec(v___x_3356_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3393_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3362_ = lean_nat_sub(v_line_3357_, v_cmdLine_3325_);
lean_dec(v_line_3357_);
v___x_3363_ = lean_unsigned_to_nat(1u);
v___x_3364_ = lean_nat_add(v___x_3362_, v___x_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3344_);
v___x_3366_ = l_String_quote(v___x_3344_);
v___x_3367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
v___x_3368_ = l_Lean_MessageData_ofFormat(v___x_3367_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 7);
lean_ctor_set(v___x_3360_, 1, v___x_3368_);
lean_ctor_set(v___x_3360_, 0, v___x_3365_);
v___x_3370_ = v___x_3360_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3365_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3371_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3370_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = l_Nat_reprFast(v___x_3364_);
v___x_3374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
v___x_3375_ = l_Lean_MessageData_ofFormat(v___x_3374_);
v___x_3376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3372_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = l_Nat_reprFast(v_column_3358_);
v___x_3380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
v___x_3381_ = l_Lean_MessageData_ofFormat(v___x_3380_);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3378_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3326_, v___x_3382_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_dec_ref_known(v___x_3383_, 1);
goto v___jp_3345_;
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v___x_3344_);
lean_dec_ref(v___f_3343_);
lean_dec_ref(v_bs_x27_3337_);
lean_dec(v_v_3335_);
lean_dec_ref(v___x_3323_);
lean_dec_ref(v___x_3321_);
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
}
v___jp_3345_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; size_t v___x_3352_; size_t v___x_3353_; lean_object* v___x_3354_; 
v___x_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3344_);
v___x_3347_ = lean_box(0);
v___x_3348_ = l_Lean_MessageData_ofSyntax(v_v_3335_);
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
v___x_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___f_3343_);
v___x_3351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3346_);
lean_ctor_set(v___x_3351_, 1, v___x_3347_);
lean_ctor_set(v___x_3351_, 2, v___x_3347_);
lean_ctor_set(v___x_3351_, 3, v___x_3347_);
lean_ctor_set(v___x_3351_, 4, v___x_3349_);
lean_ctor_set(v___x_3351_, 5, v___x_3350_);
v___x_3352_ = ((size_t)1ULL);
v___x_3353_ = lean_usize_add(v_i_3328_, v___x_3352_);
v___x_3354_ = lean_array_uset(v_bs_x27_3337_, v_i_3328_, v___x_3351_);
v_i_3328_ = v___x_3353_;
v_bs_3329_ = v___x_3354_;
goto _start;
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v_bs_x27_3337_);
lean_dec(v_v_3335_);
lean_dec_ref(v___x_3323_);
lean_dec_ref(v___x_3321_);
v_a_3394_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3339_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3339_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3402_, lean_object* v___x_3403_, lean_object* v___x_3404_, lean_object* v_insertPos_3405_, lean_object* v_cmdLine_3406_, lean_object* v_ref_3407_, lean_object* v_sz_3408_, lean_object* v_i_3409_, lean_object* v_bs_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v___x_3859__boxed_3414_; size_t v_sz_boxed_3415_; size_t v_i_boxed_3416_; lean_object* v_res_3417_; 
v___x_3859__boxed_3414_ = lean_unbox(v___x_3403_);
v_sz_boxed_3415_ = lean_unbox_usize(v_sz_3408_);
lean_dec(v_sz_3408_);
v_i_boxed_3416_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_res_3417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3402_, v___x_3859__boxed_3414_, v___x_3404_, v_insertPos_3405_, v_cmdLine_3406_, v_ref_3407_, v_sz_boxed_3415_, v_i_boxed_3416_, v_bs_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v_ref_3407_);
lean_dec(v_cmdLine_3406_);
lean_dec(v_insertPos_3405_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3418_, lean_object* v_ref_3419_, lean_object* v_insertPos_3420_, lean_object* v_suggs_3421_, lean_object* v_cmdLine_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3426_ = lean_array_get_size(v_suggs_3421_);
v___x_3427_ = lean_unsigned_to_nat(0u);
v___x_3428_ = lean_nat_dec_eq(v___x_3426_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_object* v_fileMap_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v_scopes_3435_; lean_object* v___x_3436_; lean_object* v_opts_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; size_t v_sz_3440_; size_t v___x_3441_; lean_object* v___x_3442_; 
v_fileMap_3429_ = lean_ctor_get(v_a_3423_, 1);
v___x_3430_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_inc_ref_n(v_fileMap_3429_, 2);
v___x_3431_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3418_, v_fileMap_3429_);
lean_inc(v_insertPos_3420_);
v___x_3432_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3420_);
v___x_3433_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3434_ = lean_st_ref_get(v_a_3424_);
v_scopes_3435_ = lean_ctor_get(v___x_3434_, 2);
lean_inc(v_scopes_3435_);
lean_dec(v___x_3434_);
v___x_3436_ = l_List_head_x21___redArg(v___x_3433_, v_scopes_3435_);
lean_dec(v_scopes_3435_);
v_opts_3437_ = lean_ctor_get(v___x_3436_, 1);
lean_inc_ref(v_opts_3437_);
lean_dec(v___x_3436_);
v___x_3438_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3439_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3437_, v___x_3438_);
lean_dec_ref(v_opts_3437_);
v_sz_3440_ = lean_array_size(v_suggs_3421_);
v___x_3441_ = ((size_t)0ULL);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3431_, v___x_3439_, v_fileMap_3429_, v_insertPos_3420_, v_cmdLine_3422_, v_ref_3419_, v_sz_3440_, v___x_3441_, v_suggs_3421_, v_a_3423_, v_a_3424_);
lean_dec(v_insertPos_3420_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___y_3448_; lean_object* v___x_3449_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3442_, 1);
v___x_3444_ = lean_array_get_size(v_a_3443_);
v___x_3445_ = lean_unsigned_to_nat(1u);
v___x_3446_ = lean_nat_dec_eq(v___x_3444_, v___x_3445_);
v___x_3447_ = lean_box(v___x_3446_);
v___y_3448_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3448_, 0, v___x_3447_);
lean_closure_set(v___y_3448_, 1, v___x_3432_);
lean_closure_set(v___y_3448_, 2, v_ref_3419_);
lean_closure_set(v___y_3448_, 3, v_a_3443_);
lean_closure_set(v___y_3448_, 4, v___x_3430_);
lean_closure_set(v___y_3448_, 5, v___x_3427_);
v___x_3449_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3448_, v_a_3423_, v_a_3424_);
return v___x_3449_;
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v___x_3432_);
lean_dec(v_ref_3419_);
v_a_3450_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3442_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3442_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec_ref(v_suggs_3421_);
lean_dec(v_insertPos_3420_);
lean_dec(v_ref_3419_);
v___x_3458_ = lean_box(0);
v___x_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
return v___x_3459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3460_, lean_object* v_ref_3461_, lean_object* v_insertPos_3462_, lean_object* v_suggs_3463_, lean_object* v_cmdLine_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3460_, v_ref_3461_, v_insertPos_3462_, v_suggs_3463_, v_cmdLine_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_cmdLine_3464_);
lean_dec(v_tacticSeq_3460_);
return v_res_3468_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3469_){
_start:
{
uint8_t v___x_3470_; 
v___x_3470_ = 0;
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3471_){
_start:
{
uint8_t v_res_3472_; lean_object* v_r_3473_; 
v_res_3472_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3471_);
lean_dec(v_x_3471_);
v_r_3473_ = lean_box(v_res_3472_);
return v_r_3473_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Array_mkArray0___redArg();
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3494_, lean_object* v_ref_3495_, lean_object* v_goal_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_toCold_3505_; lean_object* v_currRecDepth_3506_; lean_object* v_ref_3507_; uint16_t v_optionFlags_3508_; uint8_t v_suppressElabErrors_3509_; uint8_t v_isRecordingDeps_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_ref_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v_toCold_3505_ = lean_ctor_get(v___y_3499_, 0);
v_currRecDepth_3506_ = lean_ctor_get(v___y_3499_, 1);
v_ref_3507_ = lean_ctor_get(v___y_3499_, 2);
v_optionFlags_3508_ = lean_ctor_get_uint16(v___y_3499_, sizeof(void*)*3);
v_suppressElabErrors_3509_ = lean_ctor_get_uint8(v___y_3499_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3510_ = lean_ctor_get_uint8(v___y_3499_, sizeof(void*)*3 + 3);
v___x_3511_ = 0;
v___x_3512_ = l_Lean_SourceInfo_fromRef(v_ref_3507_, v___x_3511_);
v___x_3513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__0));
lean_inc_n(v___x_3512_, 3);
v___x_3514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3512_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
v___x_3516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__5);
v___x_3518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3512_);
lean_ctor_set(v___x_3518_, 1, v___x_3516_);
lean_ctor_set(v___x_3518_, 2, v___x_3517_);
v___x_3519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7));
v___x_3520_ = l_Lean_Syntax_node1(v___x_3512_, v___x_3519_, v___x_3518_);
v___x_3521_ = l_Lean_Syntax_node2(v___x_3512_, v___x_3515_, v___x_3514_, v___x_3520_);
v___x_3522_ = lean_box(0);
v___x_3523_ = lean_box(0);
v___x_3524_ = 1;
v___x_3525_ = lean_box(1);
v___x_3526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3527_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3527_, 0, v___x_3522_);
lean_ctor_set(v___x_3527_, 1, v___x_3523_);
lean_ctor_set(v___x_3527_, 2, v___x_3522_);
lean_ctor_set(v___x_3527_, 3, v___f_3494_);
lean_ctor_set(v___x_3527_, 4, v___x_3525_);
lean_ctor_set(v___x_3527_, 5, v___x_3525_);
lean_ctor_set(v___x_3527_, 6, v___x_3522_);
lean_ctor_set(v___x_3527_, 7, v___x_3526_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8, v___x_3524_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 1, v___x_3524_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 2, v___x_3524_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 3, v___x_3524_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 4, v___x_3511_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 5, v___x_3511_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 6, v___x_3511_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 7, v___x_3511_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 8, v___x_3524_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 9, v___x_3511_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*8 + 10, v___x_3524_);
v___x_3528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v___x_3529_ = lean_box(0);
v_ref_3530_ = l_Lean_replaceRef(v_ref_3495_, v_ref_3507_);
lean_inc(v_currRecDepth_3506_);
lean_inc_ref(v_toCold_3505_);
v___x_3531_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3531_, 0, v_toCold_3505_);
lean_ctor_set(v___x_3531_, 1, v_currRecDepth_3506_);
lean_ctor_set(v___x_3531_, 2, v_ref_3530_);
lean_ctor_set_uint16(v___x_3531_, sizeof(void*)*3, v_optionFlags_3508_);
lean_ctor_set_uint8(v___x_3531_, sizeof(void*)*3 + 2, v_suppressElabErrors_3509_);
lean_ctor_set_uint8(v___x_3531_, sizeof(void*)*3 + 3, v_isRecordingDeps_3510_);
v___x_3532_ = l_Lean_Elab_runTactic(v_goal_3496_, v___x_3521_, v___x_3527_, v___x_3528_, v___y_3497_, v___y_3498_, v___x_3531_, v___y_3500_);
lean_dec_ref_known(v___x_3531_, 3);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v___x_3532_, 0);
lean_dec(v_unused_3540_);
v___x_3534_ = v___x_3532_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_dec(v___x_3532_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3529_);
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3529_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3566_; 
v_a_3541_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3543_ = v___x_3532_;
v_isShared_3544_ = v_isSharedCheck_3566_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3532_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3566_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
lean_inc(v_a_3541_);
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
uint8_t v___y_3548_; uint8_t v___y_3560_; uint8_t v___x_3563_; 
v___x_3563_ = l_Lean_Exception_isInterrupt(v_a_3541_);
if (v___x_3563_ == 0)
{
uint8_t v___x_3564_; 
lean_inc(v_a_3541_);
v___x_3564_ = l_Lean_Exception_isRuntime(v_a_3541_);
v___y_3560_ = v___x_3564_;
goto v___jp_3559_;
}
else
{
v___y_3560_ = v___x_3563_;
goto v___jp_3559_;
}
v___jp_3547_:
{
if (v___y_3548_ == 0)
{
lean_object* v_options_3549_; uint8_t v_hasTrace_3550_; 
lean_dec_ref(v___x_3546_);
v_options_3549_ = lean_ctor_get(v_toCold_3505_, 2);
v_hasTrace_3550_ = lean_ctor_get_uint8(v_options_3549_, sizeof(void*)*1);
if (v_hasTrace_3550_ == 0)
{
lean_dec(v_a_3541_);
goto v___jp_3502_;
}
else
{
lean_object* v_inheritedTraceOptions_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_inheritedTraceOptions_3551_ = lean_ctor_get(v_toCold_3505_, 11);
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3553_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3554_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3551_, v_options_3549_, v___x_3553_);
if (v___x_3554_ == 0)
{
lean_dec(v_a_3541_);
goto v___jp_3502_;
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3555_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3556_ = l_Lean_Exception_toMessageData(v_a_3541_);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3552_, v___x_3557_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
return v___x_3558_;
}
}
}
else
{
lean_dec(v_a_3541_);
return v___x_3546_;
}
}
v___jp_3559_:
{
if (v___y_3560_ == 0)
{
uint8_t v___x_3561_; 
v___x_3561_ = l_Lean_Exception_isInterrupt(v_a_3541_);
if (v___x_3561_ == 0)
{
uint8_t v___x_3562_; 
lean_inc(v_a_3541_);
v___x_3562_ = l_Lean_Exception_isMaxRecDepth(v_a_3541_);
v___y_3548_ = v___x_3562_;
goto v___jp_3547_;
}
else
{
v___y_3548_ = v___x_3561_;
goto v___jp_3547_;
}
}
else
{
lean_dec(v_a_3541_);
return v___x_3546_;
}
}
}
}
}
v___jp_3502_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = lean_box(0);
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3567_, lean_object* v_ref_3568_, lean_object* v_goal_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3567_, v_ref_3568_, v_goal_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v_ref_3568_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v_mctx_3581_; lean_object* v_ref_3582_; lean_object* v_env_3583_; lean_object* v_opts_3584_; lean_object* v_namingCtx_3585_; lean_object* v_goal_3586_; lean_object* v_decls_3587_; lean_object* v___x_3588_; 
v_mctx_3581_ = lean_ctor_get(v_c_3577_, 3);
lean_inc_ref(v_mctx_3581_);
v_ref_3582_ = lean_ctor_get(v_c_3577_, 1);
lean_inc(v_ref_3582_);
v_env_3583_ = lean_ctor_get(v_c_3577_, 2);
lean_inc_ref(v_env_3583_);
v_opts_3584_ = lean_ctor_get(v_c_3577_, 4);
lean_inc_ref(v_opts_3584_);
v_namingCtx_3585_ = lean_ctor_get(v_c_3577_, 5);
lean_inc_ref(v_namingCtx_3585_);
v_goal_3586_ = lean_ctor_get(v_c_3577_, 6);
lean_inc(v_goal_3586_);
lean_dec_ref(v_c_3577_);
v_decls_3587_ = lean_ctor_get(v_mctx_3581_, 5);
v___x_3588_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3587_, v_goal_3586_);
if (lean_obj_tag(v___x_3588_) == 1)
{
lean_object* v_val_3589_; lean_object* v_lctx_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___x_3593_; 
v_val_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_val_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v_lctx_3590_ = lean_ctor_get(v_val_3589_, 1);
lean_inc_ref(v_lctx_3590_);
lean_dec(v_val_3589_);
v___f_3591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3592_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3592_, 0, v___f_3591_);
lean_closure_set(v___f_3592_, 1, v_ref_3582_);
lean_closure_set(v___f_3592_, 2, v_goal_3586_);
v___x_3593_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3583_, v_mctx_3581_, v_lctx_3590_, v_opts_3584_, v_namingCtx_3585_, v___f_3592_, v_a_3578_, v_a_3579_);
return v___x_3593_;
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
lean_dec(v___x_3588_);
lean_dec(v_goal_3586_);
lean_dec_ref(v_namingCtx_3585_);
lean_dec_ref(v_opts_3584_);
lean_dec_ref(v_env_3583_);
lean_dec(v_ref_3582_);
lean_dec_ref(v_mctx_3581_);
v___x_3594_ = lean_box(0);
v___x_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
return v___x_3595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3596_, v_a_3597_, v_a_3598_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
return v_res_3600_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3601_, lean_object* v_val_3602_, lean_object* v_as_3603_, size_t v_i_3604_, size_t v_stop_3605_){
_start:
{
uint8_t v___x_3610_; 
v___x_3610_ = lean_usize_dec_eq(v_i_3604_, v_stop_3605_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; lean_object* v_pos_3612_; uint8_t v_severity_3613_; lean_object* v_data_3614_; lean_object* v___f_3615_; uint8_t v___x_3616_; uint8_t v___y_3618_; uint8_t v___y_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; uint8_t v___y_3623_; 
v___x_3611_ = lean_array_uget_borrowed(v_as_3603_, v_i_3604_);
v_pos_3612_ = lean_ctor_get(v___x_3611_, 1);
v_severity_3613_ = lean_ctor_get_uint8(v___x_3611_, sizeof(void*)*5 + 1);
v_data_3614_ = lean_ctor_get(v___x_3611_, 4);
v___f_3615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
v___x_3616_ = 1;
lean_inc_ref(v_pos_3612_);
v___x_3620_ = l_Lean_FileMap_ofPosition(v___x_3601_, v_pos_3612_);
v___x_3621_ = l_Lean_Syntax_Range_contains(v_val_3602_, v___x_3620_, v___x_3616_);
lean_dec(v___x_3620_);
if (v_severity_3613_ == 2)
{
v___y_3623_ = v___x_3616_;
goto v___jp_3622_;
}
else
{
v___y_3623_ = v___x_3610_;
goto v___jp_3622_;
}
v___jp_3617_:
{
if (v___y_3619_ == 0)
{
goto v___jp_3606_;
}
else
{
if (v___y_3618_ == 0)
{
return v___x_3616_;
}
else
{
goto v___jp_3606_;
}
}
}
v___jp_3622_:
{
uint8_t v___x_3624_; 
lean_inc(v_data_3614_);
v___x_3624_ = l_Lean_MessageData_hasTag(v___f_3615_, v_data_3614_);
if (v___x_3621_ == 0)
{
v___y_3618_ = v___x_3624_;
v___y_3619_ = v___x_3621_;
goto v___jp_3617_;
}
else
{
v___y_3618_ = v___x_3624_;
v___y_3619_ = v___y_3623_;
goto v___jp_3617_;
}
}
}
else
{
uint8_t v___x_3625_; 
v___x_3625_ = 0;
return v___x_3625_;
}
v___jp_3606_:
{
size_t v___x_3607_; size_t v___x_3608_; 
v___x_3607_ = ((size_t)1ULL);
v___x_3608_ = lean_usize_add(v_i_3604_, v___x_3607_);
v_i_3604_ = v___x_3608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3626_, lean_object* v_val_3627_, lean_object* v_as_3628_, lean_object* v_i_3629_, lean_object* v_stop_3630_){
_start:
{
size_t v_i_boxed_3631_; size_t v_stop_boxed_3632_; uint8_t v_res_3633_; lean_object* v_r_3634_; 
v_i_boxed_3631_ = lean_unbox_usize(v_i_3629_);
lean_dec(v_i_3629_);
v_stop_boxed_3632_ = lean_unbox_usize(v_stop_3630_);
lean_dec(v_stop_3630_);
v_res_3633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3626_, v_val_3627_, v_as_3628_, v_i_boxed_3631_, v_stop_boxed_3632_);
lean_dec_ref(v_as_3628_);
lean_dec_ref(v_val_3627_);
lean_dec_ref(v___x_3626_);
v_r_3634_ = lean_box(v_res_3633_);
return v_r_3634_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3635_, lean_object* v_val_3636_, lean_object* v_x_3637_){
_start:
{
if (lean_obj_tag(v_x_3637_) == 0)
{
lean_object* v_cs_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v_cs_3638_ = lean_ctor_get(v_x_3637_, 0);
v___x_3639_ = lean_unsigned_to_nat(0u);
v___x_3640_ = lean_array_get_size(v_cs_3638_);
v___x_3641_ = lean_nat_dec_lt(v___x_3639_, v___x_3640_);
if (v___x_3641_ == 0)
{
return v___x_3641_;
}
else
{
if (v___x_3641_ == 0)
{
return v___x_3641_;
}
else
{
size_t v___x_3642_; size_t v___x_3643_; uint8_t v___x_3644_; 
v___x_3642_ = ((size_t)0ULL);
v___x_3643_ = lean_usize_of_nat(v___x_3640_);
v___x_3644_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3635_, v_val_3636_, v_cs_3638_, v___x_3642_, v___x_3643_);
return v___x_3644_;
}
}
}
else
{
lean_object* v_vs_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v_vs_3645_ = lean_ctor_get(v_x_3637_, 0);
v___x_3646_ = lean_unsigned_to_nat(0u);
v___x_3647_ = lean_array_get_size(v_vs_3645_);
v___x_3648_ = lean_nat_dec_lt(v___x_3646_, v___x_3647_);
if (v___x_3648_ == 0)
{
return v___x_3648_;
}
else
{
if (v___x_3648_ == 0)
{
return v___x_3648_;
}
else
{
size_t v___x_3649_; size_t v___x_3650_; uint8_t v___x_3651_; 
v___x_3649_ = ((size_t)0ULL);
v___x_3650_ = lean_usize_of_nat(v___x_3647_);
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3635_, v_val_3636_, v_vs_3645_, v___x_3649_, v___x_3650_);
return v___x_3651_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3652_, lean_object* v_val_3653_, lean_object* v_as_3654_, size_t v_i_3655_, size_t v_stop_3656_){
_start:
{
uint8_t v___x_3657_; 
v___x_3657_ = lean_usize_dec_eq(v_i_3655_, v_stop_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; uint8_t v___x_3659_; 
v___x_3658_ = lean_array_uget_borrowed(v_as_3654_, v_i_3655_);
v___x_3659_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3652_, v_val_3653_, v___x_3658_);
if (v___x_3659_ == 0)
{
size_t v___x_3660_; size_t v___x_3661_; 
v___x_3660_ = ((size_t)1ULL);
v___x_3661_ = lean_usize_add(v_i_3655_, v___x_3660_);
v_i_3655_ = v___x_3661_;
goto _start;
}
else
{
return v___x_3659_;
}
}
else
{
uint8_t v___x_3663_; 
v___x_3663_ = 0;
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3664_, lean_object* v_val_3665_, lean_object* v_as_3666_, lean_object* v_i_3667_, lean_object* v_stop_3668_){
_start:
{
size_t v_i_boxed_3669_; size_t v_stop_boxed_3670_; uint8_t v_res_3671_; lean_object* v_r_3672_; 
v_i_boxed_3669_ = lean_unbox_usize(v_i_3667_);
lean_dec(v_i_3667_);
v_stop_boxed_3670_ = lean_unbox_usize(v_stop_3668_);
lean_dec(v_stop_3668_);
v_res_3671_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3664_, v_val_3665_, v_as_3666_, v_i_boxed_3669_, v_stop_boxed_3670_);
lean_dec_ref(v_as_3666_);
lean_dec_ref(v_val_3665_);
lean_dec_ref(v___x_3664_);
v_r_3672_ = lean_box(v_res_3671_);
return v_r_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3673_, lean_object* v_val_3674_, lean_object* v_x_3675_){
_start:
{
uint8_t v_res_3676_; lean_object* v_r_3677_; 
v_res_3676_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3673_, v_val_3674_, v_x_3675_);
lean_dec_ref(v_x_3675_);
lean_dec_ref(v_val_3674_);
lean_dec_ref(v___x_3673_);
v_r_3677_ = lean_box(v_res_3676_);
return v_r_3677_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3678_, lean_object* v_val_3679_, lean_object* v_t_3680_){
_start:
{
lean_object* v_root_3681_; lean_object* v_tail_3682_; uint8_t v___x_3683_; 
v_root_3681_ = lean_ctor_get(v_t_3680_, 0);
v_tail_3682_ = lean_ctor_get(v_t_3680_, 1);
v___x_3683_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3678_, v_val_3679_, v_root_3681_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3684_ = lean_unsigned_to_nat(0u);
v___x_3685_ = lean_array_get_size(v_tail_3682_);
v___x_3686_ = lean_nat_dec_lt(v___x_3684_, v___x_3685_);
if (v___x_3686_ == 0)
{
return v___x_3686_;
}
else
{
if (v___x_3686_ == 0)
{
return v___x_3686_;
}
else
{
size_t v___x_3687_; size_t v___x_3688_; uint8_t v___x_3689_; 
v___x_3687_ = ((size_t)0ULL);
v___x_3688_ = lean_usize_of_nat(v___x_3685_);
v___x_3689_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3678_, v_val_3679_, v_tail_3682_, v___x_3687_, v___x_3688_);
return v___x_3689_;
}
}
}
else
{
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3690_, lean_object* v_val_3691_, lean_object* v_t_3692_){
_start:
{
uint8_t v_res_3693_; lean_object* v_r_3694_; 
v_res_3693_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3690_, v_val_3691_, v_t_3692_);
lean_dec_ref(v_t_3692_);
lean_dec_ref(v_val_3691_);
lean_dec_ref(v___x_3690_);
v_r_3694_ = lean_box(v_res_3693_);
return v_r_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
uint8_t v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = 0;
v___x_3700_ = l_Lean_Syntax_getRange_x3f(v_stx_3695_, v___x_3699_);
if (lean_obj_tag(v___x_3700_) == 1)
{
lean_object* v_val_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3714_; 
v_val_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3714_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_val_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3714_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v_fileMap_3705_; lean_object* v___x_3706_; lean_object* v_messages_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
v_fileMap_3705_ = lean_ctor_get(v_a_3696_, 1);
v___x_3706_ = lean_st_ref_get(v_a_3697_);
v_messages_3707_ = lean_ctor_get(v___x_3706_, 1);
lean_inc_ref(v_messages_3707_);
lean_dec(v___x_3706_);
v___x_3708_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3707_);
v___x_3709_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3705_, v_val_3701_, v___x_3708_);
lean_dec_ref(v___x_3708_);
lean_dec(v_val_3701_);
v___x_3710_ = lean_box(v___x_3709_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set_tag(v___x_3703_, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3710_);
v___x_3712_ = v___x_3703_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3710_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
lean_dec(v___x_3700_);
v___x_3715_ = lean_box(v___x_3699_);
v___x_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
return v___x_3716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3717_, v_a_3718_, v_a_3719_);
lean_dec(v_a_3719_);
lean_dec_ref(v_a_3718_);
lean_dec(v_stx_3717_);
return v_res_3721_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3722_, lean_object* v_fileMap_3723_, lean_object* v_c_3724_){
_start:
{
lean_object* v___y_3726_; lean_object* v_kind_3730_; lean_object* v_ref_3731_; lean_object* v___y_3733_; 
v_kind_3730_ = lean_ctor_get(v_c_3724_, 0);
lean_inc(v_kind_3730_);
v_ref_3731_ = lean_ctor_get(v_c_3724_, 1);
lean_inc(v_ref_3731_);
lean_dec_ref(v_c_3724_);
if (lean_obj_tag(v_kind_3730_) == 0)
{
lean_object* v_insertPos_3749_; 
lean_dec(v_ref_3731_);
v_insertPos_3749_ = lean_ctor_get(v_kind_3730_, 1);
lean_inc(v_insertPos_3749_);
v___y_3733_ = v_insertPos_3749_;
goto v___jp_3732_;
}
else
{
uint8_t v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = 0;
v___x_3751_ = l_Lean_Syntax_getPos_x3f(v_ref_3731_, v___x_3750_);
lean_dec(v_ref_3731_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_unsigned_to_nat(0u);
v___y_3733_ = v___x_3752_;
goto v___jp_3732_;
}
else
{
lean_object* v_val_3753_; 
v_val_3753_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_val_3753_);
lean_dec_ref_known(v___x_3751_, 1);
v___y_3733_ = v_val_3753_;
goto v___jp_3732_;
}
}
v___jp_3725_:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3727_ = l_List_lengthTR___redArg(v___y_3726_);
lean_dec(v___y_3726_);
v___x_3728_ = lean_unsigned_to_nat(1u);
v___x_3729_ = lean_nat_dec_eq(v___x_3727_, v___x_3728_);
lean_dec(v___x_3727_);
return v___x_3729_;
}
v___jp_3732_:
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3723_, v_tree_3722_, v___y_3733_);
if (lean_obj_tag(v___x_3734_) == 1)
{
lean_object* v_tail_3735_; 
v_tail_3735_ = lean_ctor_get(v___x_3734_, 1);
if (lean_obj_tag(v_tail_3735_) == 0)
{
if (lean_obj_tag(v_kind_3730_) == 0)
{
lean_object* v_head_3736_; lean_object* v_tacticSeq_3737_; uint8_t v___x_3738_; lean_object* v___x_3739_; 
v_head_3736_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_head_3736_);
lean_dec_ref_known(v___x_3734_, 2);
v_tacticSeq_3737_ = lean_ctor_get(v_kind_3730_, 0);
lean_inc(v_tacticSeq_3737_);
lean_dec_ref_known(v_kind_3730_, 2);
v___x_3738_ = 0;
v___x_3739_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3737_, v___x_3738_);
lean_dec(v_tacticSeq_3737_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_tacticInfo_3740_; lean_object* v_goalsBefore_3741_; 
v_tacticInfo_3740_ = lean_ctor_get(v_head_3736_, 1);
lean_inc_ref(v_tacticInfo_3740_);
lean_dec(v_head_3736_);
v_goalsBefore_3741_ = lean_ctor_get(v_tacticInfo_3740_, 2);
lean_inc(v_goalsBefore_3741_);
lean_dec_ref(v_tacticInfo_3740_);
v___y_3726_ = v_goalsBefore_3741_;
goto v___jp_3725_;
}
else
{
lean_object* v_tacticInfo_3742_; lean_object* v_goalsAfter_3743_; 
lean_dec_ref_known(v___x_3739_, 1);
v_tacticInfo_3742_ = lean_ctor_get(v_head_3736_, 1);
lean_inc_ref(v_tacticInfo_3742_);
lean_dec(v_head_3736_);
v_goalsAfter_3743_ = lean_ctor_get(v_tacticInfo_3742_, 4);
lean_inc(v_goalsAfter_3743_);
lean_dec_ref(v_tacticInfo_3742_);
v___y_3726_ = v_goalsAfter_3743_;
goto v___jp_3725_;
}
}
else
{
lean_object* v_head_3744_; lean_object* v_tacticInfo_3745_; lean_object* v_goalsBefore_3746_; 
v_head_3744_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_head_3744_);
lean_dec_ref_known(v___x_3734_, 2);
v_tacticInfo_3745_ = lean_ctor_get(v_head_3744_, 1);
lean_inc_ref(v_tacticInfo_3745_);
lean_dec(v_head_3744_);
v_goalsBefore_3746_ = lean_ctor_get(v_tacticInfo_3745_, 2);
lean_inc(v_goalsBefore_3746_);
lean_dec_ref(v_tacticInfo_3745_);
v___y_3726_ = v_goalsBefore_3746_;
goto v___jp_3725_;
}
}
else
{
uint8_t v___x_3747_; 
lean_dec_ref_known(v___x_3734_, 2);
lean_dec(v_kind_3730_);
v___x_3747_ = 0;
return v___x_3747_;
}
}
else
{
uint8_t v___x_3748_; 
lean_dec(v___x_3734_);
lean_dec(v_kind_3730_);
v___x_3748_ = 0;
return v___x_3748_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3754_, lean_object* v_fileMap_3755_, lean_object* v_c_3756_){
_start:
{
uint8_t v_res_3757_; lean_object* v_r_3758_; 
v_res_3757_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3754_, v_fileMap_3755_, v_c_3756_);
v_r_3758_ = lean_box(v_res_3757_);
return v_r_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v_infoState_3762_; lean_object* v_trees_3763_; lean_object* v___x_3764_; 
v___x_3761_ = lean_st_ref_get(v___y_3759_);
v_infoState_3762_ = lean_ctor_get(v___x_3761_, 8);
lean_inc_ref(v_infoState_3762_);
lean_dec(v___x_3761_);
v_trees_3763_ = lean_ctor_get(v_infoState_3762_, 2);
lean_inc_ref(v_trees_3763_);
lean_dec_ref(v_infoState_3762_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_trees_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3765_);
lean_dec(v___y_3765_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
return v_res_3775_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3778_ = l_Lean_stringToMessageData(v___x_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3779_, lean_object* v___x_3780_, lean_object* v___x_3781_, lean_object* v_as_3782_, size_t v_sz_3783_, size_t v_i_3784_, lean_object* v_b_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_a_3790_; uint8_t v___x_3794_; 
v___x_3794_ = lean_usize_dec_lt(v_i_3784_, v_sz_3783_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; 
lean_dec_ref(v___x_3780_);
lean_dec_ref(v_tree_3779_);
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v_b_3785_);
return v___x_3795_;
}
else
{
lean_object* v___x_3796_; lean_object* v_a_3797_; uint8_t v___x_3798_; 
v___x_3796_ = lean_box(0);
v_a_3797_ = lean_array_uget_borrowed(v_as_3782_, v_i_3784_);
lean_inc(v_a_3797_);
lean_inc_ref(v___x_3780_);
lean_inc_ref(v_tree_3779_);
v___x_3798_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3779_, v___x_3780_, v_a_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v_scopes_3804_; lean_object* v___x_3805_; lean_object* v_opts_3806_; uint8_t v_hasTrace_3807_; 
v___x_3799_ = l_Lean_inheritedTraceOptions;
v___x_3800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3801_ = lean_st_ref_get(v___x_3799_);
v___x_3802_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3803_ = lean_st_ref_get(v___y_3787_);
v_scopes_3804_ = lean_ctor_get(v___x_3803_, 2);
lean_inc(v_scopes_3804_);
lean_dec(v___x_3803_);
v___x_3805_ = l_List_head_x21___redArg(v___x_3802_, v_scopes_3804_);
lean_dec(v_scopes_3804_);
v_opts_3806_ = lean_ctor_get(v___x_3805_, 1);
lean_inc_ref(v_opts_3806_);
lean_dec(v___x_3805_);
v_hasTrace_3807_ = lean_ctor_get_uint8(v_opts_3806_, sizeof(void*)*1);
if (v_hasTrace_3807_ == 0)
{
lean_dec_ref(v_opts_3806_);
lean_dec(v___x_3801_);
v_a_3790_ = v___x_3796_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3808_; uint8_t v___x_3809_; 
v___x_3808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3809_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3801_, v_opts_3806_, v___x_3808_);
lean_dec_ref(v_opts_3806_);
lean_dec(v___x_3801_);
if (v___x_3809_ == 0)
{
v_a_3790_ = v___x_3796_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3811_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3800_, v___x_3810_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_dec_ref_known(v___x_3811_, 1);
v_a_3790_ = v___x_3796_;
goto v___jp_3789_;
}
else
{
lean_dec_ref(v___x_3780_);
lean_dec_ref(v_tree_3779_);
return v___x_3811_;
}
}
}
}
else
{
lean_object* v_kind_3812_; 
v_kind_3812_ = lean_ctor_get(v_a_3797_, 0);
if (lean_obj_tag(v_kind_3812_) == 0)
{
lean_object* v_ref_3813_; lean_object* v_tacticSeq_3814_; lean_object* v_insertPos_3815_; lean_object* v___x_3816_; 
v_ref_3813_ = lean_ctor_get(v_a_3797_, 1);
v_tacticSeq_3814_ = lean_ctor_get(v_kind_3812_, 0);
v_insertPos_3815_ = lean_ctor_get(v_kind_3812_, 1);
lean_inc(v_a_3797_);
v___x_3816_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3797_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3818_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
lean_inc(v_insertPos_3815_);
lean_inc(v_ref_3813_);
v___x_3818_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3814_, v_ref_3813_, v_insertPos_3815_, v_a_3817_, v___x_3781_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_dec_ref_known(v___x_3818_, 1);
v_a_3790_ = v___x_3796_;
goto v___jp_3789_;
}
else
{
lean_dec_ref(v___x_3780_);
lean_dec_ref(v_tree_3779_);
return v___x_3818_;
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref(v___x_3780_);
lean_dec_ref(v_tree_3779_);
v_a_3819_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3816_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3816_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v___x_3827_; 
lean_inc(v_a_3797_);
v___x_3827_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3797_, v___y_3786_, v___y_3787_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_dec_ref_known(v___x_3827_, 1);
v_a_3790_ = v___x_3796_;
goto v___jp_3789_;
}
else
{
lean_dec_ref(v___x_3780_);
lean_dec_ref(v_tree_3779_);
return v___x_3827_;
}
}
}
}
v___jp_3789_:
{
size_t v___x_3791_; size_t v___x_3792_; 
v___x_3791_ = ((size_t)1ULL);
v___x_3792_ = lean_usize_add(v_i_3784_, v___x_3791_);
v_i_3784_ = v___x_3792_;
v_b_3785_ = v_a_3790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3828_, lean_object* v___x_3829_, lean_object* v___x_3830_, lean_object* v_as_3831_, lean_object* v_sz_3832_, lean_object* v_i_3833_, lean_object* v_b_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
size_t v_sz_boxed_3838_; size_t v_i_boxed_3839_; lean_object* v_res_3840_; 
v_sz_boxed_3838_ = lean_unbox_usize(v_sz_3832_);
lean_dec(v_sz_3832_);
v_i_boxed_3839_ = lean_unbox_usize(v_i_3833_);
lean_dec(v_i_3833_);
v_res_3840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3828_, v___x_3829_, v___x_3830_, v_as_3831_, v_sz_boxed_3838_, v_i_boxed_3839_, v_b_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec_ref(v_as_3831_);
lean_dec(v___x_3830_);
return v_res_3840_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3846_ = l_Lean_stringToMessageData(v___x_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3847_, lean_object* v___x_3848_, lean_object* v___x_3849_, lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v_as_3852_, size_t v_sz_3853_, size_t v_i_3854_, lean_object* v_b_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
uint8_t v___x_3859_; 
v___x_3859_ = lean_usize_dec_lt(v_i_3854_, v_sz_3853_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_dec_ref(v___x_3850_);
lean_dec(v_stx_3847_);
v___x_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3860_, 0, v_b_3855_);
return v___x_3860_;
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v_a_3864_; lean_object* v___x_3865_; 
lean_dec_ref(v_b_3855_);
v___x_3861_ = lean_box(0);
v___x_3862_ = l_Lean_inheritedTraceOptions;
v___x_3863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3864_ = lean_array_uget_borrowed(v_as_3852_, v_i_3854_);
lean_inc(v_a_3864_);
lean_inc(v_stx_3847_);
v___x_3865_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3847_, v___x_3848_, v_a_3864_, v___x_3849_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v_scopes_3888_; lean_object* v___x_3889_; lean_object* v_opts_3890_; uint8_t v_hasTrace_3891_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3865_, 1);
v___x_3885_ = lean_st_ref_get(v___x_3862_);
v___x_3886_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3887_ = lean_st_ref_get(v___y_3857_);
v_scopes_3888_ = lean_ctor_get(v___x_3887_, 2);
lean_inc(v_scopes_3888_);
lean_dec(v___x_3887_);
v___x_3889_ = l_List_head_x21___redArg(v___x_3886_, v_scopes_3888_);
lean_dec(v_scopes_3888_);
v_opts_3890_ = lean_ctor_get(v___x_3889_, 1);
lean_inc_ref(v_opts_3890_);
lean_dec(v___x_3889_);
v_hasTrace_3891_ = lean_ctor_get_uint8(v_opts_3890_, sizeof(void*)*1);
if (v_hasTrace_3891_ == 0)
{
lean_dec_ref(v_opts_3890_);
lean_dec(v___x_3885_);
v___y_3868_ = v___y_3856_;
v___y_3869_ = v___y_3857_;
goto v___jp_3867_;
}
else
{
lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3892_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3893_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3885_, v_opts_3890_, v___x_3892_);
lean_dec_ref(v_opts_3890_);
lean_dec(v___x_3885_);
if (v___x_3893_ == 0)
{
v___y_3868_ = v___y_3856_;
v___y_3869_ = v___y_3857_;
goto v___jp_3867_;
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3895_ = lean_array_get_size(v_a_3866_);
v___x_3896_ = l_Nat_reprFast(v___x_3895_);
v___x_3897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
v___x_3898_ = l_Lean_MessageData_ofFormat(v___x_3897_);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3894_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3863_, v___x_3899_, v___y_3856_, v___y_3857_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_dec_ref_known(v___x_3900_, 1);
v___y_3868_ = v___y_3856_;
v___y_3869_ = v___y_3857_;
goto v___jp_3867_;
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec(v_a_3866_);
lean_dec_ref(v___x_3850_);
lean_dec(v_stx_3847_);
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
v___jp_3867_:
{
size_t v_sz_3870_; size_t v___x_3871_; lean_object* v___x_3872_; 
v_sz_3870_ = lean_array_size(v_a_3866_);
v___x_3871_ = ((size_t)0ULL);
lean_inc_ref(v___x_3850_);
lean_inc(v_a_3864_);
v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3864_, v___x_3850_, v___x_3851_, v_a_3866_, v_sz_3870_, v___x_3871_, v___x_3861_, v___y_3868_, v___y_3869_);
lean_dec(v_a_3866_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v___x_3873_; size_t v___x_3874_; size_t v___x_3875_; 
lean_dec_ref_known(v___x_3872_, 1);
v___x_3873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3874_ = ((size_t)1ULL);
v___x_3875_ = lean_usize_add(v_i_3854_, v___x_3874_);
v_i_3854_ = v___x_3875_;
v_b_3855_ = v___x_3873_;
goto _start;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v___x_3850_);
lean_dec(v_stx_3847_);
v_a_3877_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3872_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3872_);
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
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec_ref(v___x_3850_);
lean_dec(v_stx_3847_);
v_a_3909_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3865_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3865_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3917_, lean_object* v___x_3918_, lean_object* v___x_3919_, lean_object* v___x_3920_, lean_object* v___x_3921_, lean_object* v_as_3922_, lean_object* v_sz_3923_, lean_object* v_i_3924_, lean_object* v_b_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
size_t v_sz_boxed_3929_; size_t v_i_boxed_3930_; lean_object* v_res_3931_; 
v_sz_boxed_3929_ = lean_unbox_usize(v_sz_3923_);
lean_dec(v_sz_3923_);
v_i_boxed_3930_ = lean_unbox_usize(v_i_3924_);
lean_dec(v_i_3924_);
v_res_3931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3917_, v___x_3918_, v___x_3919_, v___x_3920_, v___x_3921_, v_as_3922_, v_sz_boxed_3929_, v_i_boxed_3930_, v_b_3925_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec_ref(v_as_3922_);
lean_dec(v___x_3921_);
lean_dec_ref(v___x_3919_);
lean_dec_ref(v___x_3918_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3932_, lean_object* v___x_3933_, lean_object* v___x_3934_, lean_object* v___x_3935_, lean_object* v___x_3936_, lean_object* v_as_3937_, size_t v_sz_3938_, size_t v_i_3939_, lean_object* v_b_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
uint8_t v___x_3944_; 
v___x_3944_ = lean_usize_dec_lt(v_i_3939_, v_sz_3938_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3945_; 
lean_dec_ref(v___x_3935_);
lean_dec(v_stx_3932_);
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_b_3940_);
return v___x_3945_;
}
else
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v_a_3949_; lean_object* v___x_3950_; 
lean_dec_ref(v_b_3940_);
v___x_3946_ = lean_box(0);
v___x_3947_ = l_Lean_inheritedTraceOptions;
v___x_3948_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3949_ = lean_array_uget_borrowed(v_as_3937_, v_i_3939_);
lean_inc(v_a_3949_);
lean_inc(v_stx_3932_);
v___x_3950_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3932_, v___x_3933_, v_a_3949_, v___x_3934_, v___y_3941_, v___y_3942_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v_scopes_3973_; lean_object* v___x_3974_; lean_object* v_opts_3975_; uint8_t v_hasTrace_3976_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
v___x_3970_ = lean_st_ref_get(v___x_3947_);
v___x_3971_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3972_ = lean_st_ref_get(v___y_3942_);
v_scopes_3973_ = lean_ctor_get(v___x_3972_, 2);
lean_inc(v_scopes_3973_);
lean_dec(v___x_3972_);
v___x_3974_ = l_List_head_x21___redArg(v___x_3971_, v_scopes_3973_);
lean_dec(v_scopes_3973_);
v_opts_3975_ = lean_ctor_get(v___x_3974_, 1);
lean_inc_ref(v_opts_3975_);
lean_dec(v___x_3974_);
v_hasTrace_3976_ = lean_ctor_get_uint8(v_opts_3975_, sizeof(void*)*1);
if (v_hasTrace_3976_ == 0)
{
lean_dec_ref(v_opts_3975_);
lean_dec(v___x_3970_);
v___y_3953_ = v___y_3941_;
v___y_3954_ = v___y_3942_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3977_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3978_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3970_, v_opts_3975_, v___x_3977_);
lean_dec_ref(v_opts_3975_);
lean_dec(v___x_3970_);
if (v___x_3978_ == 0)
{
v___y_3953_ = v___y_3941_;
v___y_3954_ = v___y_3942_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3979_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3980_ = lean_array_get_size(v_a_3951_);
v___x_3981_ = l_Nat_reprFast(v___x_3980_);
v___x_3982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
v___x_3983_ = l_Lean_MessageData_ofFormat(v___x_3982_);
v___x_3984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3979_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3948_, v___x_3984_, v___y_3941_, v___y_3942_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_dec_ref_known(v___x_3985_, 1);
v___y_3953_ = v___y_3941_;
v___y_3954_ = v___y_3942_;
goto v___jp_3952_;
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec(v_a_3951_);
lean_dec_ref(v___x_3935_);
lean_dec(v_stx_3932_);
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3985_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
v___jp_3952_:
{
size_t v_sz_3955_; size_t v___x_3956_; lean_object* v___x_3957_; 
v_sz_3955_ = lean_array_size(v_a_3951_);
v___x_3956_ = ((size_t)0ULL);
lean_inc_ref(v___x_3935_);
lean_inc(v_a_3949_);
v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3949_, v___x_3935_, v___x_3936_, v_a_3951_, v_sz_3955_, v___x_3956_, v___x_3946_, v___y_3953_, v___y_3954_);
lean_dec(v_a_3951_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v___x_3958_; size_t v___x_3959_; size_t v___x_3960_; lean_object* v___x_3961_; 
lean_dec_ref_known(v___x_3957_, 1);
v___x_3958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3959_ = ((size_t)1ULL);
v___x_3960_ = lean_usize_add(v_i_3939_, v___x_3959_);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3932_, v___x_3933_, v___x_3934_, v___x_3935_, v___x_3936_, v_as_3937_, v_sz_3938_, v___x_3960_, v___x_3958_, v___y_3941_, v___y_3942_);
return v___x_3961_;
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v___x_3935_);
lean_dec(v_stx_3932_);
v_a_3962_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3957_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3957_);
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
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v___x_3935_);
lean_dec(v_stx_3932_);
v_a_3994_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3950_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3950_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_4002_, lean_object* v___x_4003_, lean_object* v___x_4004_, lean_object* v___x_4005_, lean_object* v___x_4006_, lean_object* v_as_4007_, lean_object* v_sz_4008_, lean_object* v_i_4009_, lean_object* v_b_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
size_t v_sz_boxed_4014_; size_t v_i_boxed_4015_; lean_object* v_res_4016_; 
v_sz_boxed_4014_ = lean_unbox_usize(v_sz_4008_);
lean_dec(v_sz_4008_);
v_i_boxed_4015_ = lean_unbox_usize(v_i_4009_);
lean_dec(v_i_4009_);
v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4002_, v___x_4003_, v___x_4004_, v___x_4005_, v___x_4006_, v_as_4007_, v_sz_boxed_4014_, v_i_boxed_4015_, v_b_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec_ref(v_as_4007_);
lean_dec(v___x_4006_);
lean_dec_ref(v___x_4004_);
lean_dec_ref(v___x_4003_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_4020_, lean_object* v___x_4021_, lean_object* v___x_4022_, lean_object* v___x_4023_, lean_object* v___x_4024_, lean_object* v_as_4025_, size_t v_sz_4026_, size_t v_i_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
uint8_t v___x_4032_; 
v___x_4032_ = lean_usize_dec_lt(v_i_4027_, v_sz_4026_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; 
lean_dec_ref(v___x_4023_);
lean_dec(v_stx_4020_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v_b_4028_);
return v___x_4033_;
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v_a_4037_; lean_object* v___x_4038_; 
lean_dec_ref(v_b_4028_);
v___x_4034_ = lean_box(0);
v___x_4035_ = l_Lean_inheritedTraceOptions;
v___x_4036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4037_ = lean_array_uget_borrowed(v_as_4025_, v_i_4027_);
lean_inc(v_a_4037_);
lean_inc(v_stx_4020_);
v___x_4038_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4020_, v___x_4021_, v_a_4037_, v___x_4022_, v___y_4029_, v___y_4030_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v_scopes_4061_; lean_object* v___x_4062_; lean_object* v_opts_4063_; uint8_t v_hasTrace_4064_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v___x_4038_, 1);
v___x_4058_ = lean_st_ref_get(v___x_4035_);
v___x_4059_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4060_ = lean_st_ref_get(v___y_4030_);
v_scopes_4061_ = lean_ctor_get(v___x_4060_, 2);
lean_inc(v_scopes_4061_);
lean_dec(v___x_4060_);
v___x_4062_ = l_List_head_x21___redArg(v___x_4059_, v_scopes_4061_);
lean_dec(v_scopes_4061_);
v_opts_4063_ = lean_ctor_get(v___x_4062_, 1);
lean_inc_ref(v_opts_4063_);
lean_dec(v___x_4062_);
v_hasTrace_4064_ = lean_ctor_get_uint8(v_opts_4063_, sizeof(void*)*1);
if (v_hasTrace_4064_ == 0)
{
lean_dec_ref(v_opts_4063_);
lean_dec(v___x_4058_);
v___y_4041_ = v___y_4029_;
v___y_4042_ = v___y_4030_;
goto v___jp_4040_;
}
else
{
lean_object* v___x_4065_; uint8_t v___x_4066_; 
v___x_4065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4058_, v_opts_4063_, v___x_4065_);
lean_dec_ref(v_opts_4063_);
lean_dec(v___x_4058_);
if (v___x_4066_ == 0)
{
v___y_4041_ = v___y_4029_;
v___y_4042_ = v___y_4030_;
goto v___jp_4040_;
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4068_ = lean_array_get_size(v_a_4039_);
v___x_4069_ = l_Nat_reprFast(v___x_4068_);
v___x_4070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
v___x_4071_ = l_Lean_MessageData_ofFormat(v___x_4070_);
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4067_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4036_, v___x_4072_, v___y_4029_, v___y_4030_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_dec_ref_known(v___x_4073_, 1);
v___y_4041_ = v___y_4029_;
v___y_4042_ = v___y_4030_;
goto v___jp_4040_;
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v_a_4039_);
lean_dec_ref(v___x_4023_);
lean_dec(v_stx_4020_);
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
}
v___jp_4040_:
{
size_t v_sz_4043_; size_t v___x_4044_; lean_object* v___x_4045_; 
v_sz_4043_ = lean_array_size(v_a_4039_);
v___x_4044_ = ((size_t)0ULL);
lean_inc_ref(v___x_4023_);
lean_inc(v_a_4037_);
v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4037_, v___x_4023_, v___x_4024_, v_a_4039_, v_sz_4043_, v___x_4044_, v___x_4034_, v___y_4041_, v___y_4042_);
lean_dec(v_a_4039_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v___x_4046_; size_t v___x_4047_; size_t v___x_4048_; 
lean_dec_ref_known(v___x_4045_, 1);
v___x_4046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4047_ = ((size_t)1ULL);
v___x_4048_ = lean_usize_add(v_i_4027_, v___x_4047_);
v_i_4027_ = v___x_4048_;
v_b_4028_ = v___x_4046_;
goto _start;
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
lean_dec_ref(v___x_4023_);
lean_dec(v_stx_4020_);
v_a_4050_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4045_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4045_);
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
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec_ref(v___x_4023_);
lean_dec(v_stx_4020_);
v_a_4082_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4038_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4038_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4090_, lean_object* v___x_4091_, lean_object* v___x_4092_, lean_object* v___x_4093_, lean_object* v___x_4094_, lean_object* v_as_4095_, lean_object* v_sz_4096_, lean_object* v_i_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
size_t v_sz_boxed_4102_; size_t v_i_boxed_4103_; lean_object* v_res_4104_; 
v_sz_boxed_4102_ = lean_unbox_usize(v_sz_4096_);
lean_dec(v_sz_4096_);
v_i_boxed_4103_ = lean_unbox_usize(v_i_4097_);
lean_dec(v_i_4097_);
v_res_4104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4090_, v___x_4091_, v___x_4092_, v___x_4093_, v___x_4094_, v_as_4095_, v_sz_boxed_4102_, v_i_boxed_4103_, v_b_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec_ref(v_as_4095_);
lean_dec(v___x_4094_);
lean_dec_ref(v___x_4092_);
lean_dec_ref(v___x_4091_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4105_, lean_object* v___x_4106_, lean_object* v___x_4107_, lean_object* v___x_4108_, lean_object* v___x_4109_, lean_object* v_as_4110_, size_t v_sz_4111_, size_t v_i_4112_, lean_object* v_b_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v___x_4117_; 
v___x_4117_ = lean_usize_dec_lt(v_i_4112_, v_sz_4111_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; 
lean_dec_ref(v___x_4108_);
lean_dec(v_stx_4105_);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v_b_4113_);
return v___x_4118_;
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v_a_4122_; lean_object* v___x_4123_; 
lean_dec_ref(v_b_4113_);
v___x_4119_ = lean_box(0);
v___x_4120_ = l_Lean_inheritedTraceOptions;
v___x_4121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4122_ = lean_array_uget_borrowed(v_as_4110_, v_i_4112_);
lean_inc(v_a_4122_);
lean_inc(v_stx_4105_);
v___x_4123_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4105_, v___x_4106_, v_a_4122_, v___x_4107_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v_scopes_4146_; lean_object* v___x_4147_; lean_object* v_opts_4148_; uint8_t v_hasTrace_4149_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref_known(v___x_4123_, 1);
v___x_4143_ = lean_st_ref_get(v___x_4120_);
v___x_4144_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4145_ = lean_st_ref_get(v___y_4115_);
v_scopes_4146_ = lean_ctor_get(v___x_4145_, 2);
lean_inc(v_scopes_4146_);
lean_dec(v___x_4145_);
v___x_4147_ = l_List_head_x21___redArg(v___x_4144_, v_scopes_4146_);
lean_dec(v_scopes_4146_);
v_opts_4148_ = lean_ctor_get(v___x_4147_, 1);
lean_inc_ref(v_opts_4148_);
lean_dec(v___x_4147_);
v_hasTrace_4149_ = lean_ctor_get_uint8(v_opts_4148_, sizeof(void*)*1);
if (v_hasTrace_4149_ == 0)
{
lean_dec_ref(v_opts_4148_);
lean_dec(v___x_4143_);
v___y_4126_ = v___y_4114_;
v___y_4127_ = v___y_4115_;
goto v___jp_4125_;
}
else
{
lean_object* v___x_4150_; uint8_t v___x_4151_; 
v___x_4150_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4151_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4143_, v_opts_4148_, v___x_4150_);
lean_dec_ref(v_opts_4148_);
lean_dec(v___x_4143_);
if (v___x_4151_ == 0)
{
v___y_4126_ = v___y_4114_;
v___y_4127_ = v___y_4115_;
goto v___jp_4125_;
}
else
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4152_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4153_ = lean_array_get_size(v_a_4124_);
v___x_4154_ = l_Nat_reprFast(v___x_4153_);
v___x_4155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
v___x_4156_ = l_Lean_MessageData_ofFormat(v___x_4155_);
v___x_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4152_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4121_, v___x_4157_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_dec_ref_known(v___x_4158_, 1);
v___y_4126_ = v___y_4114_;
v___y_4127_ = v___y_4115_;
goto v___jp_4125_;
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec(v_a_4124_);
lean_dec_ref(v___x_4108_);
lean_dec(v_stx_4105_);
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
v___jp_4125_:
{
size_t v_sz_4128_; size_t v___x_4129_; lean_object* v___x_4130_; 
v_sz_4128_ = lean_array_size(v_a_4124_);
v___x_4129_ = ((size_t)0ULL);
lean_inc_ref(v___x_4108_);
lean_inc(v_a_4122_);
v___x_4130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4122_, v___x_4108_, v___x_4109_, v_a_4124_, v_sz_4128_, v___x_4129_, v___x_4119_, v___y_4126_, v___y_4127_);
lean_dec(v_a_4124_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v___x_4131_; size_t v___x_4132_; size_t v___x_4133_; lean_object* v___x_4134_; 
lean_dec_ref_known(v___x_4130_, 1);
v___x_4131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4132_ = ((size_t)1ULL);
v___x_4133_ = lean_usize_add(v_i_4112_, v___x_4132_);
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4105_, v___x_4106_, v___x_4107_, v___x_4108_, v___x_4109_, v_as_4110_, v_sz_4111_, v___x_4133_, v___x_4131_, v___y_4114_, v___y_4115_);
return v___x_4134_;
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v___x_4108_);
lean_dec(v_stx_4105_);
v_a_4135_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4130_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4130_);
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
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_dec_ref(v___x_4108_);
lean_dec(v_stx_4105_);
v_a_4167_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4123_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4123_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4175_, lean_object* v___x_4176_, lean_object* v___x_4177_, lean_object* v___x_4178_, lean_object* v___x_4179_, lean_object* v_as_4180_, lean_object* v_sz_4181_, lean_object* v_i_4182_, lean_object* v_b_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
size_t v_sz_boxed_4187_; size_t v_i_boxed_4188_; lean_object* v_res_4189_; 
v_sz_boxed_4187_ = lean_unbox_usize(v_sz_4181_);
lean_dec(v_sz_4181_);
v_i_boxed_4188_ = lean_unbox_usize(v_i_4182_);
lean_dec(v_i_4182_);
v_res_4189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4175_, v___x_4176_, v___x_4177_, v___x_4178_, v___x_4179_, v_as_4180_, v_sz_boxed_4187_, v_i_boxed_4188_, v_b_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec_ref(v_as_4180_);
lean_dec(v___x_4179_);
lean_dec_ref(v___x_4177_);
lean_dec_ref(v___x_4176_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4190_, lean_object* v_stx_4191_, lean_object* v___x_4192_, lean_object* v___x_4193_, lean_object* v___x_4194_, lean_object* v___x_4195_, lean_object* v_n_4196_, lean_object* v_b_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
if (lean_obj_tag(v_n_4196_) == 0)
{
lean_object* v_cs_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; size_t v_sz_4204_; size_t v___x_4205_; lean_object* v___x_4206_; 
v_cs_4201_ = lean_ctor_get(v_n_4196_, 0);
v___x_4202_ = lean_box(0);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set(v___x_4203_, 1, v_b_4197_);
v_sz_4204_ = lean_array_size(v_cs_4201_);
v___x_4205_ = ((size_t)0ULL);
v___x_4206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4190_, v_stx_4191_, v___x_4192_, v___x_4193_, v___x_4194_, v___x_4195_, v_cs_4201_, v_sz_4204_, v___x_4205_, v___x_4203_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4221_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4221_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4221_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v_fst_4211_; 
v_fst_4211_ = lean_ctor_get(v_a_4207_, 0);
if (lean_obj_tag(v_fst_4211_) == 0)
{
lean_object* v_snd_4212_; lean_object* v___x_4213_; lean_object* v___x_4215_; 
v_snd_4212_ = lean_ctor_get(v_a_4207_, 1);
lean_inc(v_snd_4212_);
lean_dec(v_a_4207_);
v___x_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4213_, 0, v_snd_4212_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4213_);
v___x_4215_ = v___x_4209_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
lean_object* v_val_4217_; lean_object* v___x_4219_; 
lean_inc_ref(v_fst_4211_);
lean_dec(v_a_4207_);
v_val_4217_ = lean_ctor_get(v_fst_4211_, 0);
lean_inc(v_val_4217_);
lean_dec_ref_known(v_fst_4211_, 1);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v_val_4217_);
v___x_4219_ = v___x_4209_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_val_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
v_a_4222_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4206_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4206_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
else
{
lean_object* v_vs_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; size_t v_sz_4233_; size_t v___x_4234_; lean_object* v___x_4235_; 
v_vs_4230_ = lean_ctor_get(v_n_4196_, 0);
v___x_4231_ = lean_box(0);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
lean_ctor_set(v___x_4232_, 1, v_b_4197_);
v_sz_4233_ = lean_array_size(v_vs_4230_);
v___x_4234_ = ((size_t)0ULL);
v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4191_, v___x_4192_, v___x_4193_, v___x_4194_, v___x_4195_, v_vs_4230_, v_sz_4233_, v___x_4234_, v___x_4232_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4250_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4238_ = v___x_4235_;
v_isShared_4239_ = v_isSharedCheck_4250_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4250_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v_fst_4240_; 
v_fst_4240_ = lean_ctor_get(v_a_4236_, 0);
if (lean_obj_tag(v_fst_4240_) == 0)
{
lean_object* v_snd_4241_; lean_object* v___x_4242_; lean_object* v___x_4244_; 
v_snd_4241_ = lean_ctor_get(v_a_4236_, 1);
lean_inc(v_snd_4241_);
lean_dec(v_a_4236_);
v___x_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4242_, 0, v_snd_4241_);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v___x_4242_);
v___x_4244_ = v___x_4238_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
else
{
lean_object* v_val_4246_; lean_object* v___x_4248_; 
lean_inc_ref(v_fst_4240_);
lean_dec(v_a_4236_);
v_val_4246_ = lean_ctor_get(v_fst_4240_, 0);
lean_inc(v_val_4246_);
lean_dec_ref_known(v_fst_4240_, 1);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v_val_4246_);
v___x_4248_ = v___x_4238_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_val_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
v_a_4251_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4235_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4235_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4259_, lean_object* v_stx_4260_, lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v___x_4264_, lean_object* v_as_4265_, size_t v_sz_4266_, size_t v_i_4267_, lean_object* v_b_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v___x_4272_; 
v___x_4272_ = lean_usize_dec_lt(v_i_4267_, v_sz_4266_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; 
lean_dec_ref(v___x_4263_);
lean_dec(v_stx_4260_);
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v_b_4268_);
return v___x_4273_;
}
else
{
lean_object* v_snd_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4308_; 
v_snd_4274_ = lean_ctor_get(v_b_4268_, 1);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_b_4268_);
if (v_isSharedCheck_4308_ == 0)
{
lean_object* v_unused_4309_; 
v_unused_4309_ = lean_ctor_get(v_b_4268_, 0);
lean_dec(v_unused_4309_);
v___x_4276_ = v_b_4268_;
v_isShared_4277_ = v_isSharedCheck_4308_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_snd_4274_);
lean_dec(v_b_4268_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4308_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4278_; lean_object* v_a_4279_; lean_object* v___x_4280_; 
v___x_4278_ = lean_box(0);
v_a_4279_ = lean_array_uget_borrowed(v_as_4265_, v_i_4267_);
lean_inc(v_snd_4274_);
lean_inc_ref(v___x_4263_);
lean_inc(v_stx_4260_);
v___x_4280_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4259_, v_stx_4260_, v___x_4261_, v___x_4262_, v___x_4263_, v___x_4264_, v_a_4279_, v_snd_4274_, v___y_4269_, v___y_4270_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4299_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4283_ = v___x_4280_;
v_isShared_4284_ = v_isSharedCheck_4299_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4280_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4299_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
if (lean_obj_tag(v_a_4281_) == 0)
{
lean_object* v___x_4285_; lean_object* v___x_4287_; 
lean_dec_ref(v___x_4263_);
lean_dec(v_stx_4260_);
v___x_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4285_, 0, v_a_4281_);
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 0, v___x_4285_);
v___x_4287_ = v___x_4276_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4285_);
lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_snd_4274_);
v___x_4287_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
lean_object* v___x_4289_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4287_);
v___x_4289_ = v___x_4283_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; 
lean_del_object(v___x_4283_);
lean_dec(v_snd_4274_);
v_a_4292_ = lean_ctor_get(v_a_4281_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v_a_4281_, 1);
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 1, v_a_4292_);
lean_ctor_set(v___x_4276_, 0, v___x_4278_);
v___x_4294_ = v___x_4276_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4278_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_a_4292_);
v___x_4294_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
size_t v___x_4295_; size_t v___x_4296_; 
v___x_4295_ = ((size_t)1ULL);
v___x_4296_ = lean_usize_add(v_i_4267_, v___x_4295_);
v_i_4267_ = v___x_4296_;
v_b_4268_ = v___x_4294_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_del_object(v___x_4276_);
lean_dec(v_snd_4274_);
lean_dec_ref(v___x_4263_);
lean_dec(v_stx_4260_);
v_a_4300_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4280_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4280_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4310_, lean_object* v_stx_4311_, lean_object* v___x_4312_, lean_object* v___x_4313_, lean_object* v___x_4314_, lean_object* v___x_4315_, lean_object* v_as_4316_, lean_object* v_sz_4317_, lean_object* v_i_4318_, lean_object* v_b_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
size_t v_sz_boxed_4323_; size_t v_i_boxed_4324_; lean_object* v_res_4325_; 
v_sz_boxed_4323_ = lean_unbox_usize(v_sz_4317_);
lean_dec(v_sz_4317_);
v_i_boxed_4324_ = lean_unbox_usize(v_i_4318_);
lean_dec(v_i_4318_);
v_res_4325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4310_, v_stx_4311_, v___x_4312_, v___x_4313_, v___x_4314_, v___x_4315_, v_as_4316_, v_sz_boxed_4323_, v_i_boxed_4324_, v_b_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec_ref(v_as_4316_);
lean_dec(v___x_4315_);
lean_dec_ref(v___x_4313_);
lean_dec_ref(v___x_4312_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4326_, lean_object* v_stx_4327_, lean_object* v___x_4328_, lean_object* v___x_4329_, lean_object* v___x_4330_, lean_object* v___x_4331_, lean_object* v_n_4332_, lean_object* v_b_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4326_, v_stx_4327_, v___x_4328_, v___x_4329_, v___x_4330_, v___x_4331_, v_n_4332_, v_b_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec_ref(v_n_4332_);
lean_dec(v___x_4331_);
lean_dec_ref(v___x_4329_);
lean_dec_ref(v___x_4328_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4338_, lean_object* v___x_4339_, lean_object* v_stx_4340_, lean_object* v___x_4341_, lean_object* v___x_4342_, lean_object* v_t_4343_, lean_object* v_init_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v_root_4348_; lean_object* v_tail_4349_; lean_object* v___x_4350_; 
v_root_4348_ = lean_ctor_get(v_t_4343_, 0);
v_tail_4349_ = lean_ctor_get(v_t_4343_, 1);
lean_inc_ref(v___x_4338_);
lean_inc(v_stx_4340_);
v___x_4350_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4344_, v_stx_4340_, v___x_4341_, v___x_4342_, v___x_4338_, v___x_4339_, v_root_4348_, v_init_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4387_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4387_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4387_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
if (lean_obj_tag(v_a_4351_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; 
lean_dec(v_stx_4340_);
lean_dec_ref(v___x_4338_);
v_a_4355_ = lean_ctor_get(v_a_4351_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v_a_4351_, 1);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v_a_4355_);
v___x_4357_ = v___x_4353_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4355_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; size_t v_sz_4362_; size_t v___x_4363_; lean_object* v___x_4364_; 
lean_del_object(v___x_4353_);
v_a_4359_ = lean_ctor_get(v_a_4351_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v_a_4351_, 1);
v___x_4360_ = lean_box(0);
v___x_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
lean_ctor_set(v___x_4361_, 1, v_a_4359_);
v_sz_4362_ = lean_array_size(v_tail_4349_);
v___x_4363_ = ((size_t)0ULL);
v___x_4364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4340_, v___x_4341_, v___x_4342_, v___x_4338_, v___x_4339_, v_tail_4349_, v_sz_4362_, v___x_4363_, v___x_4361_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4378_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4367_ = v___x_4364_;
v_isShared_4368_ = v_isSharedCheck_4378_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4364_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4378_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v_fst_4369_; 
v_fst_4369_ = lean_ctor_get(v_a_4365_, 0);
if (lean_obj_tag(v_fst_4369_) == 0)
{
lean_object* v_snd_4370_; lean_object* v___x_4372_; 
v_snd_4370_ = lean_ctor_get(v_a_4365_, 1);
lean_inc(v_snd_4370_);
lean_dec(v_a_4365_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 0, v_snd_4370_);
v___x_4372_ = v___x_4367_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_snd_4370_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
else
{
lean_object* v_val_4374_; lean_object* v___x_4376_; 
lean_inc_ref(v_fst_4369_);
lean_dec(v_a_4365_);
v_val_4374_ = lean_ctor_get(v_fst_4369_, 0);
lean_inc(v_val_4374_);
lean_dec_ref_known(v_fst_4369_, 1);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 0, v_val_4374_);
v___x_4376_ = v___x_4367_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_val_4374_);
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
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
v_a_4379_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4364_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4364_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec(v_stx_4340_);
lean_dec_ref(v___x_4338_);
v_a_4388_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4350_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4350_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4396_, lean_object* v___x_4397_, lean_object* v_stx_4398_, lean_object* v___x_4399_, lean_object* v___x_4400_, lean_object* v_t_4401_, lean_object* v_init_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4396_, v___x_4397_, v_stx_4398_, v___x_4399_, v___x_4400_, v_t_4401_, v_init_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec_ref(v_t_4401_);
lean_dec_ref(v___x_4400_);
lean_dec_ref(v___x_4399_);
lean_dec(v___x_4397_);
return v_res_4406_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4409_ = l_Lean_stringToMessageData(v___x_4408_);
return v___x_4409_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4414_ = l_Lean_stringToMessageData(v___x_4413_);
return v___x_4414_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4416_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4417_ = l_Lean_stringToMessageData(v___x_4416_);
return v___x_4417_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4420_ = l_Lean_stringToMessageData(v___x_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v_scopes_4430_; lean_object* v___x_4431_; lean_object* v_opts_4432_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; uint8_t v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; uint8_t v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; uint8_t v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; uint8_t v___y_4476_; lean_object* v___y_4477_; uint8_t v___y_4486_; lean_object* v___y_4487_; uint8_t v___y_4488_; lean_object* v___y_4489_; uint8_t v___y_4490_; lean_object* v___y_4491_; uint8_t v___y_4500_; uint8_t v___y_4501_; uint8_t v___y_4502_; uint8_t v___y_4536_; lean_object* v___x_4543_; uint8_t v___x_4544_; 
v___x_4428_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4429_ = lean_st_ref_get(v___y_4423_);
v_scopes_4430_ = lean_ctor_get(v___x_4429_, 2);
lean_inc(v_scopes_4430_);
lean_dec(v___x_4429_);
v___x_4431_ = l_List_head_x21___redArg(v___x_4428_, v_scopes_4430_);
lean_dec(v_scopes_4430_);
v_opts_4432_ = lean_ctor_get(v___x_4431_, 1);
lean_inc_ref(v_opts_4432_);
lean_dec(v___x_4431_);
v___x_4543_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4544_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4432_, v___x_4543_);
if (v___x_4544_ == 0)
{
lean_object* v___x_4545_; uint8_t v___x_4546_; 
v___x_4545_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4546_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4432_, v___x_4545_);
v___y_4536_ = v___x_4546_;
goto v___jp_4535_;
}
else
{
v___y_4536_ = v___x_4544_;
goto v___jp_4535_;
}
v___jp_4425_:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4426_ = lean_box(0);
v___x_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
return v___x_4427_;
}
v___jp_4433_:
{
lean_object* v___x_4438_; lean_object* v_line_4439_; lean_object* v___x_4440_; lean_object* v_messages_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v_a_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
lean_inc_ref_n(v___y_4435_, 2);
v___x_4438_ = l_Lean_FileMap_toPosition(v___y_4435_, v___y_4437_);
lean_dec(v___y_4437_);
v_line_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_line_4439_);
lean_dec_ref(v___x_4438_);
v___x_4440_ = lean_st_ref_get(v___y_4434_);
v_messages_4441_ = lean_ctor_get(v___x_4440_, 1);
lean_inc_ref(v_messages_4441_);
lean_dec(v___x_4440_);
v___x_4442_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4441_);
v___x_4443_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4434_);
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_a_4444_);
lean_dec_ref(v___x_4443_);
v___x_4445_ = lean_box(0);
v___x_4446_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4435_, v_line_4439_, v_stx_4421_, v_opts_4432_, v___x_4442_, v_a_4444_, v___x_4445_, v___y_4436_, v___y_4434_);
lean_dec(v_a_4444_);
lean_dec_ref(v___x_4442_);
lean_dec_ref(v_opts_4432_);
lean_dec(v_line_4439_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4453_ == 0)
{
lean_object* v_unused_4454_; 
v_unused_4454_ = lean_ctor_get(v___x_4446_, 0);
lean_dec(v_unused_4454_);
v___x_4448_ = v___x_4446_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_dec(v___x_4446_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v___x_4445_);
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4445_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
else
{
return v___x_4446_;
}
}
v___jp_4455_:
{
lean_object* v_fileMap_4459_; lean_object* v___x_4460_; 
v_fileMap_4459_ = lean_ctor_get(v___y_4457_, 1);
v___x_4460_ = l_Lean_Syntax_getPos_x3f(v_stx_4421_, v___y_4456_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v___x_4461_; 
v___x_4461_ = lean_unsigned_to_nat(0u);
v___y_4434_ = v___y_4458_;
v___y_4435_ = v_fileMap_4459_;
v___y_4436_ = v___y_4457_;
v___y_4437_ = v___x_4461_;
goto v___jp_4433_;
}
else
{
lean_object* v_val_4462_; 
v_val_4462_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_val_4462_);
lean_dec_ref_known(v___x_4460_, 1);
v___y_4434_ = v___y_4458_;
v___y_4435_ = v_fileMap_4459_;
v___y_4436_ = v___y_4457_;
v___y_4437_ = v_val_4462_;
goto v___jp_4433_;
}
}
v___jp_4463_:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_inc_ref(v___y_4467_);
v___x_4468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___y_4467_);
v___x_4469_ = l_Lean_MessageData_ofFormat(v___x_4468_);
v___x_4470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___y_4466_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
lean_inc(v___y_4465_);
v___x_4471_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___y_4465_, v___x_4470_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_dec_ref_known(v___x_4471_, 1);
v___y_4456_ = v___y_4464_;
v___y_4457_ = v___y_4422_;
v___y_4458_ = v___y_4423_;
goto v___jp_4455_;
}
else
{
lean_dec_ref(v_opts_4432_);
lean_dec(v_stx_4421_);
return v___x_4471_;
}
}
v___jp_4472_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_inc_ref(v___y_4477_);
v___x_4478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___y_4477_);
v___x_4479_ = l_Lean_MessageData_ofFormat(v___x_4478_);
v___x_4480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4480_, 0, v___y_4474_);
lean_ctor_set(v___x_4480_, 1, v___x_4479_);
v___x_4481_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
if (v___y_4473_ == 0)
{
lean_object* v___x_4483_; 
v___x_4483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4464_ = v___y_4476_;
v___y_4465_ = v___y_4475_;
v___y_4466_ = v___x_4482_;
v___y_4467_ = v___x_4483_;
goto v___jp_4463_;
}
else
{
lean_object* v___x_4484_; 
v___x_4484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4464_ = v___y_4476_;
v___y_4465_ = v___y_4475_;
v___y_4466_ = v___x_4482_;
v___y_4467_ = v___x_4484_;
goto v___jp_4463_;
}
}
v___jp_4485_:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
lean_inc_ref(v___y_4491_);
v___x_4492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4492_, 0, v___y_4491_);
v___x_4493_ = l_Lean_MessageData_ofFormat(v___x_4492_);
lean_inc_ref(v___y_4487_);
v___x_4494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___y_4487_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___x_4495_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4494_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
if (v___y_4490_ == 0)
{
lean_object* v___x_4497_; 
v___x_4497_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4473_ = v___y_4486_;
v___y_4474_ = v___x_4496_;
v___y_4475_ = v___y_4489_;
v___y_4476_ = v___y_4488_;
v___y_4477_ = v___x_4497_;
goto v___jp_4472_;
}
else
{
lean_object* v___x_4498_; 
v___x_4498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4473_ = v___y_4486_;
v___y_4474_ = v___x_4496_;
v___y_4475_ = v___y_4489_;
v___y_4476_ = v___y_4488_;
v___y_4477_ = v___x_4498_;
goto v___jp_4472_;
}
}
v___jp_4499_:
{
lean_object* v___x_4503_; lean_object* v_a_4504_; uint8_t v___x_4505_; 
v___x_4503_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4421_, v___y_4422_, v___y_4423_);
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref(v___x_4503_);
v___x_4505_ = lean_unbox(v_a_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v_scopes_4510_; lean_object* v___x_4511_; lean_object* v_opts_4512_; uint8_t v_hasTrace_4513_; 
v___x_4506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4507_ = l_Lean_inheritedTraceOptions;
v___x_4508_ = lean_st_ref_get(v___x_4507_);
v___x_4509_ = lean_st_ref_get(v___y_4423_);
v_scopes_4510_ = lean_ctor_get(v___x_4509_, 2);
lean_inc(v_scopes_4510_);
lean_dec(v___x_4509_);
v___x_4511_ = l_List_head_x21___redArg(v___x_4428_, v_scopes_4510_);
lean_dec(v_scopes_4510_);
v_opts_4512_ = lean_ctor_get(v___x_4511_, 1);
lean_inc_ref(v_opts_4512_);
lean_dec(v___x_4511_);
v_hasTrace_4513_ = lean_ctor_get_uint8(v_opts_4512_, sizeof(void*)*1);
if (v_hasTrace_4513_ == 0)
{
uint8_t v___x_4514_; 
lean_dec_ref(v_opts_4512_);
lean_dec(v___x_4508_);
v___x_4514_ = lean_unbox(v_a_4504_);
lean_dec(v_a_4504_);
v___y_4456_ = v___x_4514_;
v___y_4457_ = v___y_4422_;
v___y_4458_ = v___y_4423_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4515_; uint8_t v___x_4516_; 
v___x_4515_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4516_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4508_, v_opts_4512_, v___x_4515_);
lean_dec_ref(v_opts_4512_);
lean_dec(v___x_4508_);
if (v___x_4516_ == 0)
{
uint8_t v___x_4517_; 
v___x_4517_ = lean_unbox(v_a_4504_);
lean_dec(v_a_4504_);
v___y_4456_ = v___x_4517_;
v___y_4457_ = v___y_4422_;
v___y_4458_ = v___y_4423_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4518_; 
v___x_4518_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4501_ == 0)
{
lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4520_ = lean_unbox(v_a_4504_);
lean_dec(v_a_4504_);
v___y_4486_ = v___y_4500_;
v___y_4487_ = v___x_4518_;
v___y_4488_ = v___x_4520_;
v___y_4489_ = v___x_4506_;
v___y_4490_ = v___y_4502_;
v___y_4491_ = v___x_4519_;
goto v___jp_4485_;
}
else
{
lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4522_ = lean_unbox(v_a_4504_);
lean_dec(v_a_4504_);
v___y_4486_ = v___y_4500_;
v___y_4487_ = v___x_4518_;
v___y_4488_ = v___x_4522_;
v___y_4489_ = v___x_4506_;
v___y_4490_ = v___y_4502_;
v___y_4491_ = v___x_4521_;
goto v___jp_4485_;
}
}
}
}
else
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v_scopes_4527_; lean_object* v___x_4528_; lean_object* v_opts_4529_; uint8_t v_hasTrace_4530_; 
lean_dec(v_a_4504_);
lean_dec_ref(v_opts_4432_);
lean_dec(v_stx_4421_);
v___x_4523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4524_ = l_Lean_inheritedTraceOptions;
v___x_4525_ = lean_st_ref_get(v___x_4524_);
v___x_4526_ = lean_st_ref_get(v___y_4423_);
v_scopes_4527_ = lean_ctor_get(v___x_4526_, 2);
lean_inc(v_scopes_4527_);
lean_dec(v___x_4526_);
v___x_4528_ = l_List_head_x21___redArg(v___x_4428_, v_scopes_4527_);
lean_dec(v_scopes_4527_);
v_opts_4529_ = lean_ctor_get(v___x_4528_, 1);
lean_inc_ref(v_opts_4529_);
lean_dec(v___x_4528_);
v_hasTrace_4530_ = lean_ctor_get_uint8(v_opts_4529_, sizeof(void*)*1);
if (v_hasTrace_4530_ == 0)
{
lean_dec_ref(v_opts_4529_);
lean_dec(v___x_4525_);
goto v___jp_4425_;
}
else
{
lean_object* v___x_4531_; uint8_t v___x_4532_; 
v___x_4531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4525_, v_opts_4529_, v___x_4531_);
lean_dec_ref(v_opts_4529_);
lean_dec(v___x_4525_);
if (v___x_4532_ == 0)
{
goto v___jp_4425_;
}
else
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4534_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4523_, v___x_4533_, v___y_4422_, v___y_4423_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_dec_ref_known(v___x_4534_, 1);
goto v___jp_4425_;
}
else
{
return v___x_4534_;
}
}
}
}
}
v___jp_4535_:
{
lean_object* v___x_4537_; uint8_t v___x_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4537_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4538_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4432_, v___x_4537_);
v___x_4539_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4540_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4432_, v___x_4539_);
if (v___y_4536_ == 0)
{
if (v___x_4538_ == 0)
{
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
lean_dec_ref(v_opts_4432_);
lean_dec(v_stx_4421_);
v___x_4541_ = lean_box(0);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
else
{
v___y_4500_ = v___x_4540_;
v___y_4501_ = v___y_4536_;
v___y_4502_ = v___x_4538_;
goto v___jp_4499_;
}
}
else
{
v___y_4500_ = v___x_4540_;
v___y_4501_ = v___y_4536_;
v___y_4502_ = v___x_4538_;
goto v___jp_4499_;
}
}
else
{
v___y_4500_ = v___x_4540_;
v___y_4501_ = v___y_4536_;
v___y_4502_ = v___x_4538_;
goto v___jp_4499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4547_, v___y_4548_, v___y_4549_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4565_ = l_Lean_Elab_Command_addLinter(v___x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4567_;
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
