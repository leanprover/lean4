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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_inheritedTraceOptions;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25;
static lean_once_cell_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26;
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
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_NameSet_empty;
v___x_301_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
lean_ctor_set(v___x_302_, 2, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_304_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__5);
v___x_305_ = 1;
v___x_306_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_303_);
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*3, v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_maxRecDepth;
v___x_311_ = l_Lean_Options_empty;
v___x_312_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static uint16_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25(void){
_start:
{
uint16_t v___x_313_; uint16_t v___x_314_; uint16_t v___x_315_; 
v___x_313_ = 512;
v___x_314_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_315_ = lean_uint16_land(v___x_314_, v___x_313_);
return v___x_315_;
}
}
static uint8_t _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26(void){
_start:
{
uint16_t v___x_316_; uint16_t v___x_317_; uint8_t v___x_318_; 
v___x_316_ = 0;
v___x_317_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__25);
v___x_318_ = lean_uint16_dec_eq(v___x_317_, v___x_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(lean_object* v_env_319_, lean_object* v_mctx_320_, lean_object* v_lctx_321_, lean_object* v_opts_322_, lean_object* v_namingCtx_323_, lean_object* v_x_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_fileName_340_; lean_object* v_fileMap_341_; lean_object* v_ref_342_; lean_object* v_cancelTk_x3f_343_; lean_object* v_a_345_; lean_object* v_a_352_; lean_object* v_currNamespace_354_; lean_object* v_openDecls_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint16_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint16_t v___y_374_; lean_object* v___y_375_; lean_object* v_fileName_376_; lean_object* v_fileMap_377_; lean_object* v_currNamespace_378_; lean_object* v_openDecls_379_; lean_object* v_initHeartbeats_380_; lean_object* v_maxHeartbeats_381_; lean_object* v_quotContext_382_; lean_object* v_currMacroScope_383_; lean_object* v_cancelTk_x3f_384_; lean_object* v_inheritedTraceOptions_385_; lean_object* v_currRecDepth_386_; lean_object* v_ref_387_; uint8_t v_suppressElabErrors_388_; uint8_t v_isRecordingDeps_389_; lean_object* v___y_390_; lean_object* v___y_459_; uint16_t v___y_460_; lean_object* v___y_461_; uint8_t v___y_462_; lean_object* v___y_463_; lean_object* v_fileName_500_; lean_object* v_fileMap_501_; lean_object* v_currNamespace_502_; lean_object* v_openDecls_503_; lean_object* v_initHeartbeats_504_; lean_object* v_maxHeartbeats_505_; lean_object* v_quotContext_506_; lean_object* v_currMacroScope_507_; lean_object* v_cancelTk_x3f_508_; lean_object* v_inheritedTraceOptions_509_; lean_object* v_currRecDepth_510_; lean_object* v_ref_511_; uint8_t v_suppressElabErrors_512_; uint8_t v_isRecordingDeps_513_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___y_530_; lean_object* v_env_551_; uint8_t v___x_552_; uint8_t v___x_553_; 
v___x_328_ = lean_box(1);
v___x_329_ = 0;
v___x_330_ = l_Lean_Environment_setExporting(v_env_319_, v___x_329_);
v___x_331_ = 1;
v___x_332_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__2);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__3));
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_336_, 0, v___x_332_);
lean_ctor_set(v___x_336_, 1, v___x_328_);
lean_ctor_set(v___x_336_, 2, v_lctx_321_);
lean_ctor_set(v___x_336_, 3, v___x_334_);
lean_ctor_set(v___x_336_, 4, v___x_335_);
lean_ctor_set(v___x_336_, 5, v___x_333_);
lean_ctor_set(v___x_336_, 6, v___x_335_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*7, v___x_329_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*7 + 1, v___x_329_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*7 + 2, v___x_329_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*7 + 3, v___x_331_);
v___x_337_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__6);
v___x_338_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__8);
v___x_339_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__9);
v_fileName_340_ = lean_ctor_get(v_a_325_, 0);
v_fileMap_341_ = lean_ctor_get(v_a_325_, 1);
v_ref_342_ = lean_ctor_get(v_a_325_, 7);
v_cancelTk_x3f_343_ = lean_ctor_get(v_a_325_, 9);
v_currNamespace_354_ = lean_ctor_get(v_namingCtx_323_, 0);
lean_inc(v_currNamespace_354_);
v_openDecls_355_ = lean_ctor_get(v_namingCtx_323_, 1);
lean_inc(v_openDecls_355_);
lean_dec_ref(v_namingCtx_323_);
v___x_356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_356_, 0, v_mctx_320_);
lean_ctor_set(v___x_356_, 1, v___x_337_);
lean_ctor_set(v___x_356_, 2, v___x_328_);
lean_ctor_set(v___x_356_, 3, v___x_338_);
lean_ctor_set(v___x_356_, 4, v___x_339_);
v___x_357_ = l_Lean_Options_empty;
v___x_358_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__10);
v___x_359_ = lean_box(0);
v___x_360_ = l_Lean_firstFrontendMacroScope;
v___x_361_ = lean_box(0);
v___x_362_ = lean_uint16_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__11);
v___x_363_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__12);
v___x_364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__15));
v___x_365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__16));
v___x_366_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__17);
v___x_367_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__18);
v___x_368_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__19);
v___x_369_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__20);
v___x_370_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_370_, 0, v___x_330_);
lean_ctor_set(v___x_370_, 1, v___x_363_);
lean_ctor_set(v___x_370_, 2, v___x_364_);
lean_ctor_set(v___x_370_, 3, v___x_365_);
lean_ctor_set(v___x_370_, 4, v___x_366_);
lean_ctor_set(v___x_370_, 5, v___x_367_);
lean_ctor_set(v___x_370_, 6, v___x_334_);
lean_ctor_set(v___x_370_, 7, v___x_368_);
lean_ctor_set(v___x_370_, 8, v___x_369_);
lean_ctor_set(v___x_370_, 9, v___x_334_);
v___x_371_ = lean_io_get_num_heartbeats();
v___x_372_ = lean_st_mk_ref(v___x_370_);
v___x_526_ = l_Lean_inheritedTraceOptions;
v___x_527_ = lean_st_ref_get(v___x_526_);
v___x_528_ = lean_st_ref_get(v___x_372_);
v_env_551_ = lean_ctor_get(v___x_528_, 0);
lean_inc_ref(v_env_551_);
lean_dec(v___x_528_);
v___x_552_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_551_);
lean_dec_ref(v_env_551_);
v___x_553_ = lean_uint8_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__26);
if (v___x_553_ == 0)
{
if (v___x_552_ == 0)
{
v___y_530_ = v___x_331_;
goto v___jp_529_;
}
else
{
v_fileName_500_ = v_fileName_340_;
v_fileMap_501_ = v_fileMap_341_;
v_currNamespace_502_ = v_currNamespace_354_;
v_openDecls_503_ = v_openDecls_355_;
v_initHeartbeats_504_ = v___x_371_;
v_maxHeartbeats_505_ = v___x_358_;
v_quotContext_506_ = v___x_359_;
v_currMacroScope_507_ = v___x_360_;
v_cancelTk_x3f_508_ = v_cancelTk_x3f_343_;
v_inheritedTraceOptions_509_ = v___x_527_;
v_currRecDepth_510_ = v___x_333_;
v_ref_511_ = v___x_361_;
v_suppressElabErrors_512_ = v___x_329_;
v_isRecordingDeps_513_ = v___x_329_;
goto v___jp_499_;
}
}
else
{
if (v___x_552_ == 0)
{
v_fileName_500_ = v_fileName_340_;
v_fileMap_501_ = v_fileMap_341_;
v_currNamespace_502_ = v_currNamespace_354_;
v_openDecls_503_ = v_openDecls_355_;
v_initHeartbeats_504_ = v___x_371_;
v_maxHeartbeats_505_ = v___x_358_;
v_quotContext_506_ = v___x_359_;
v_currMacroScope_507_ = v___x_360_;
v_cancelTk_x3f_508_ = v_cancelTk_x3f_343_;
v_inheritedTraceOptions_509_ = v___x_527_;
v_currRecDepth_510_ = v___x_333_;
v_ref_511_ = v___x_361_;
v_suppressElabErrors_512_ = v___x_329_;
v_isRecordingDeps_513_ = v___x_329_;
goto v___jp_499_;
}
else
{
v___y_530_ = v___x_329_;
goto v___jp_529_;
}
}
v___jp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_346_ = lean_io_error_to_string(v_a_345_);
v___x_347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___x_348_ = l_Lean_MessageData_ofFormat(v___x_347_);
lean_inc(v_ref_342_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_ref_342_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
v___jp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = lean_mk_io_user_error(v_a_352_);
v_a_345_ = v___x_353_;
goto v___jp_344_;
}
v___jp_373_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_391_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope_spec__0(v_opts_322_, v___y_375_);
v___x_392_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_392_, 0, v_fileName_376_);
lean_ctor_set(v___x_392_, 1, v_fileMap_377_);
lean_ctor_set(v___x_392_, 2, v_opts_322_);
lean_ctor_set(v___x_392_, 3, v___x_391_);
lean_ctor_set(v___x_392_, 4, v_currNamespace_378_);
lean_ctor_set(v___x_392_, 5, v_openDecls_379_);
lean_ctor_set(v___x_392_, 6, v_initHeartbeats_380_);
lean_ctor_set(v___x_392_, 7, v_maxHeartbeats_381_);
lean_ctor_set(v___x_392_, 8, v_quotContext_382_);
lean_ctor_set(v___x_392_, 9, v_currMacroScope_383_);
lean_ctor_set(v___x_392_, 10, v_cancelTk_x3f_384_);
lean_ctor_set(v___x_392_, 11, v_inheritedTraceOptions_385_);
v___x_393_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_currRecDepth_386_);
lean_ctor_set(v___x_393_, 2, v_ref_387_);
lean_ctor_set_uint16(v___x_393_, sizeof(void*)*3, v___y_374_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*3 + 2, v_suppressElabErrors_388_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*3 + 3, v_isRecordingDeps_389_);
v___x_394_ = lean_st_mk_ref(v___x_356_);
lean_inc(v___x_394_);
v___x_395_ = lean_apply_5(v_x_324_, v___x_336_, v___x_394_, v___x_393_, v___y_390_, lean_box(0));
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_442_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_442_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_442_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_442_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_traceState_403_; lean_object* v_traceState_404_; lean_object* v_env_405_; lean_object* v_messages_406_; lean_object* v_scopes_407_; lean_object* v_usedQuotCtxts_408_; lean_object* v_nextMacroScope_409_; lean_object* v_maxRecDepth_410_; lean_object* v_ngen_411_; lean_object* v_auxDeclNGen_412_; lean_object* v_infoState_413_; lean_object* v_snapshotTasks_414_; lean_object* v_prevLinterStates_415_; lean_object* v_codeQualityEntryTasks_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_440_; 
v___x_400_ = lean_st_ref_get(v___x_394_);
lean_dec(v___x_394_);
lean_dec(v___x_400_);
v___x_401_ = lean_st_ref_get(v___x_372_);
lean_dec(v___x_372_);
v___x_402_ = lean_st_ref_take(v_a_326_);
v_traceState_403_ = lean_ctor_get(v___x_402_, 9);
lean_inc_ref(v_traceState_403_);
v_traceState_404_ = lean_ctor_get(v___x_401_, 4);
lean_inc_ref(v_traceState_404_);
v_env_405_ = lean_ctor_get(v___x_402_, 0);
v_messages_406_ = lean_ctor_get(v___x_402_, 1);
v_scopes_407_ = lean_ctor_get(v___x_402_, 2);
v_usedQuotCtxts_408_ = lean_ctor_get(v___x_402_, 3);
v_nextMacroScope_409_ = lean_ctor_get(v___x_402_, 4);
v_maxRecDepth_410_ = lean_ctor_get(v___x_402_, 5);
v_ngen_411_ = lean_ctor_get(v___x_402_, 6);
v_auxDeclNGen_412_ = lean_ctor_get(v___x_402_, 7);
v_infoState_413_ = lean_ctor_get(v___x_402_, 8);
v_snapshotTasks_414_ = lean_ctor_get(v___x_402_, 10);
v_prevLinterStates_415_ = lean_ctor_get(v___x_402_, 11);
v_codeQualityEntryTasks_416_ = lean_ctor_get(v___x_402_, 12);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_402_, 9);
lean_dec(v_unused_441_);
v___x_418_ = v___x_402_;
v_isShared_419_ = v_isSharedCheck_440_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_codeQualityEntryTasks_416_);
lean_inc(v_prevLinterStates_415_);
lean_inc(v_snapshotTasks_414_);
lean_inc(v_infoState_413_);
lean_inc(v_auxDeclNGen_412_);
lean_inc(v_ngen_411_);
lean_inc(v_maxRecDepth_410_);
lean_inc(v_nextMacroScope_409_);
lean_inc(v_usedQuotCtxts_408_);
lean_inc(v_scopes_407_);
lean_inc(v_messages_406_);
lean_inc(v_env_405_);
lean_dec(v___x_402_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_440_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_messages_420_; uint64_t v_tid_421_; lean_object* v_traces_422_; lean_object* v_traces_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_439_; 
v_messages_420_ = lean_ctor_get(v___x_401_, 7);
lean_inc_ref(v_messages_420_);
lean_dec(v___x_401_);
v_tid_421_ = lean_ctor_get_uint64(v_traceState_403_, sizeof(void*)*1);
v_traces_422_ = lean_ctor_get(v_traceState_403_, 0);
lean_inc_ref(v_traces_422_);
lean_dec_ref(v_traceState_403_);
v_traces_423_ = lean_ctor_get(v_traceState_404_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_traceState_404_);
if (v_isSharedCheck_439_ == 0)
{
v___x_425_ = v_traceState_404_;
v_isShared_426_ = v_isSharedCheck_439_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_traces_423_);
lean_dec(v_traceState_404_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_439_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_427_ = l_Lean_MessageLog_append(v_messages_406_, v_messages_420_);
v___x_428_ = l_Lean_PersistentArray_append___redArg(v_traces_422_, v_traces_423_);
lean_dec_ref(v_traces_423_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_428_);
v___x_430_ = v___x_425_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_438_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
lean_ctor_set_uint64(v___x_430_, sizeof(void*)*1, v_tid_421_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 9, v___x_430_);
lean_ctor_set(v___x_418_, 1, v___x_427_);
v___x_432_ = v___x_418_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_env_405_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_scopes_407_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_usedQuotCtxts_408_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_nextMacroScope_409_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v_maxRecDepth_410_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_ngen_411_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_auxDeclNGen_412_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_infoState_413_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_437_, 10, v_snapshotTasks_414_);
lean_ctor_set(v_reuseFailAlloc_437_, 11, v_prevLinterStates_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 12, v_codeQualityEntryTasks_416_);
v___x_432_ = v_reuseFailAlloc_437_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_st_ref_put(v_a_326_, v___x_432_);
if (v_isShared_399_ == 0)
{
v___x_435_ = v___x_398_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_396_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_443_; 
lean_dec(v___x_394_);
lean_dec(v___x_372_);
v_a_443_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_395_, 1);
if (lean_obj_tag(v_a_443_) == 0)
{
lean_object* v_msg_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_msg_444_ = lean_ctor_get(v_a_443_, 1);
lean_inc_ref(v_msg_444_);
lean_dec_ref_known(v_a_443_, 2);
v___x_445_ = l_Lean_MessageData_toString(v_msg_444_);
v___x_446_ = lean_mk_io_user_error(v___x_445_);
v_a_345_ = v___x_446_;
goto v___jp_344_;
}
else
{
lean_object* v_id_447_; lean_object* v___x_448_; 
v_id_447_ = lean_ctor_get(v_a_443_, 0);
lean_inc(v_id_447_);
lean_dec_ref_known(v_a_443_, 2);
v___x_448_ = l_Lean_InternalExceptionId_getName(v_id_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_id_447_);
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__21));
v___x_451_ = l_Lean_Name_toString(v_a_449_, v___x_331_);
v___x_452_ = lean_string_append(v___x_450_, v___x_451_);
lean_dec_ref(v___x_451_);
v_a_352_ = v___x_452_;
goto v___jp_351_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref_known(v___x_448_, 1);
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__22));
v___x_454_ = l_Nat_reprFast(v_id_447_);
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__23));
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
v_a_352_ = v___x_457_;
goto v___jp_351_;
}
}
}
}
v___jp_458_:
{
lean_object* v___x_464_; lean_object* v_env_465_; lean_object* v_nextMacroScope_466_; lean_object* v_ngen_467_; lean_object* v_auxDeclNGen_468_; lean_object* v_traceState_469_; lean_object* v_recordedDeps_470_; lean_object* v_messages_471_; lean_object* v_infoState_472_; lean_object* v_snapshotTasks_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_497_; 
v___x_464_ = lean_st_ref_take(v___y_459_);
v_env_465_ = lean_ctor_get(v___x_464_, 0);
v_nextMacroScope_466_ = lean_ctor_get(v___x_464_, 1);
v_ngen_467_ = lean_ctor_get(v___x_464_, 2);
v_auxDeclNGen_468_ = lean_ctor_get(v___x_464_, 3);
v_traceState_469_ = lean_ctor_get(v___x_464_, 4);
v_recordedDeps_470_ = lean_ctor_get(v___x_464_, 6);
v_messages_471_ = lean_ctor_get(v___x_464_, 7);
v_infoState_472_ = lean_ctor_get(v___x_464_, 8);
v_snapshotTasks_473_ = lean_ctor_get(v___x_464_, 9);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_464_, 5);
lean_dec(v_unused_498_);
v___x_475_ = v___x_464_;
v_isShared_476_ = v_isSharedCheck_497_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snapshotTasks_473_);
lean_inc(v_infoState_472_);
lean_inc(v_messages_471_);
lean_inc(v_recordedDeps_470_);
lean_inc(v_traceState_469_);
lean_inc(v_auxDeclNGen_468_);
lean_inc(v_ngen_467_);
lean_inc(v_nextMacroScope_466_);
lean_inc(v_env_465_);
lean_dec(v___x_464_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_497_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l_Lean_Kernel_enableDiag(v_env_465_, v___y_462_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 5, v___x_367_);
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_nextMacroScope_466_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_ngen_467_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_auxDeclNGen_468_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_traceState_469_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_recordedDeps_470_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_messages_471_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_infoState_472_);
lean_ctor_set(v_reuseFailAlloc_496_, 9, v_snapshotTasks_473_);
v___x_479_ = v_reuseFailAlloc_496_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; lean_object* v_toCold_481_; lean_object* v_currRecDepth_482_; lean_object* v_ref_483_; uint8_t v_suppressElabErrors_484_; uint8_t v_isRecordingDeps_485_; lean_object* v_fileName_486_; lean_object* v_fileMap_487_; lean_object* v_currNamespace_488_; lean_object* v_openDecls_489_; lean_object* v_initHeartbeats_490_; lean_object* v_maxHeartbeats_491_; lean_object* v_quotContext_492_; lean_object* v_currMacroScope_493_; lean_object* v_cancelTk_x3f_494_; lean_object* v_inheritedTraceOptions_495_; 
v___x_480_ = lean_st_ref_put(v___y_459_, v___x_479_);
v_toCold_481_ = lean_ctor_get(v___y_463_, 0);
lean_inc_ref(v_toCold_481_);
v_currRecDepth_482_ = lean_ctor_get(v___y_463_, 1);
lean_inc(v_currRecDepth_482_);
v_ref_483_ = lean_ctor_get(v___y_463_, 2);
lean_inc(v_ref_483_);
v_suppressElabErrors_484_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*3 + 2);
v_isRecordingDeps_485_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*3 + 3);
lean_dec_ref(v___y_463_);
v_fileName_486_ = lean_ctor_get(v_toCold_481_, 0);
lean_inc_ref(v_fileName_486_);
v_fileMap_487_ = lean_ctor_get(v_toCold_481_, 1);
lean_inc_ref(v_fileMap_487_);
v_currNamespace_488_ = lean_ctor_get(v_toCold_481_, 4);
lean_inc(v_currNamespace_488_);
v_openDecls_489_ = lean_ctor_get(v_toCold_481_, 5);
lean_inc(v_openDecls_489_);
v_initHeartbeats_490_ = lean_ctor_get(v_toCold_481_, 6);
lean_inc(v_initHeartbeats_490_);
v_maxHeartbeats_491_ = lean_ctor_get(v_toCold_481_, 7);
lean_inc(v_maxHeartbeats_491_);
v_quotContext_492_ = lean_ctor_get(v_toCold_481_, 8);
lean_inc(v_quotContext_492_);
v_currMacroScope_493_ = lean_ctor_get(v_toCold_481_, 9);
lean_inc(v_currMacroScope_493_);
v_cancelTk_x3f_494_ = lean_ctor_get(v_toCold_481_, 10);
lean_inc(v_cancelTk_x3f_494_);
v_inheritedTraceOptions_495_ = lean_ctor_get(v_toCold_481_, 11);
lean_inc_ref(v_inheritedTraceOptions_495_);
lean_dec_ref(v_toCold_481_);
v___y_374_ = v___y_460_;
v___y_375_ = v___y_461_;
v_fileName_376_ = v_fileName_486_;
v_fileMap_377_ = v_fileMap_487_;
v_currNamespace_378_ = v_currNamespace_488_;
v_openDecls_379_ = v_openDecls_489_;
v_initHeartbeats_380_ = v_initHeartbeats_490_;
v_maxHeartbeats_381_ = v_maxHeartbeats_491_;
v_quotContext_382_ = v_quotContext_492_;
v_currMacroScope_383_ = v_currMacroScope_493_;
v_cancelTk_x3f_384_ = v_cancelTk_x3f_494_;
v_inheritedTraceOptions_385_ = v_inheritedTraceOptions_495_;
v_currRecDepth_386_ = v_currRecDepth_482_;
v_ref_387_ = v_ref_483_;
v_suppressElabErrors_388_ = v_suppressElabErrors_484_;
v_isRecordingDeps_389_ = v_isRecordingDeps_485_;
v___y_390_ = v___y_459_;
goto v___jp_373_;
}
}
}
v___jp_499_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint16_t v___x_518_; lean_object* v___x_519_; lean_object* v_env_520_; uint8_t v___x_521_; uint16_t v___x_522_; uint16_t v___x_523_; uint16_t v___x_524_; uint8_t v___x_525_; 
v___x_514_ = l_Lean_maxRecDepth;
v___x_515_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__24);
lean_inc_ref(v_inheritedTraceOptions_509_);
lean_inc(v_cancelTk_x3f_508_);
lean_inc(v_currMacroScope_507_);
lean_inc(v_quotContext_506_);
lean_inc(v_maxHeartbeats_505_);
lean_inc(v_initHeartbeats_504_);
lean_inc(v_openDecls_503_);
lean_inc(v_currNamespace_502_);
lean_inc_ref(v_fileMap_501_);
lean_inc_ref(v_fileName_500_);
v___x_516_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_516_, 0, v_fileName_500_);
lean_ctor_set(v___x_516_, 1, v_fileMap_501_);
lean_ctor_set(v___x_516_, 2, v___x_357_);
lean_ctor_set(v___x_516_, 3, v___x_515_);
lean_ctor_set(v___x_516_, 4, v_currNamespace_502_);
lean_ctor_set(v___x_516_, 5, v_openDecls_503_);
lean_ctor_set(v___x_516_, 6, v_initHeartbeats_504_);
lean_ctor_set(v___x_516_, 7, v_maxHeartbeats_505_);
lean_ctor_set(v___x_516_, 8, v_quotContext_506_);
lean_ctor_set(v___x_516_, 9, v_currMacroScope_507_);
lean_ctor_set(v___x_516_, 10, v_cancelTk_x3f_508_);
lean_ctor_set(v___x_516_, 11, v_inheritedTraceOptions_509_);
lean_inc(v_ref_511_);
lean_inc(v_currRecDepth_510_);
v___x_517_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v_currRecDepth_510_);
lean_ctor_set(v___x_517_, 2, v_ref_511_);
lean_ctor_set_uint16(v___x_517_, sizeof(void*)*3, v___x_362_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*3 + 2, v_suppressElabErrors_512_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*3 + 3, v_isRecordingDeps_513_);
v___x_518_ = l_Lean_OptionFlags_ofOptions(v_opts_322_);
v___x_519_ = lean_st_ref_get(v___x_372_);
v_env_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc_ref(v_env_520_);
lean_dec(v___x_519_);
v___x_521_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_520_);
lean_dec_ref(v_env_520_);
v___x_522_ = 512;
v___x_523_ = lean_uint16_land(v___x_518_, v___x_522_);
v___x_524_ = 0;
v___x_525_ = lean_uint16_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
if (v___x_521_ == 0)
{
lean_dec(v_currRecDepth_510_);
lean_dec_ref(v_inheritedTraceOptions_509_);
lean_dec(v_initHeartbeats_504_);
lean_dec(v_openDecls_503_);
lean_dec(v_currNamespace_502_);
lean_inc(v___x_372_);
v___y_459_ = v___x_372_;
v___y_460_ = v___x_518_;
v___y_461_ = v___x_514_;
v___y_462_ = v___x_331_;
v___y_463_ = v___x_517_;
goto v___jp_458_;
}
else
{
lean_dec_ref_known(v___x_517_, 3);
lean_inc(v___x_372_);
lean_inc(v_ref_511_);
lean_inc(v_cancelTk_x3f_508_);
lean_inc(v_currMacroScope_507_);
lean_inc(v_quotContext_506_);
lean_inc(v_maxHeartbeats_505_);
lean_inc_ref(v_fileMap_501_);
lean_inc_ref(v_fileName_500_);
v___y_374_ = v___x_518_;
v___y_375_ = v___x_514_;
v_fileName_376_ = v_fileName_500_;
v_fileMap_377_ = v_fileMap_501_;
v_currNamespace_378_ = v_currNamespace_502_;
v_openDecls_379_ = v_openDecls_503_;
v_initHeartbeats_380_ = v_initHeartbeats_504_;
v_maxHeartbeats_381_ = v_maxHeartbeats_505_;
v_quotContext_382_ = v_quotContext_506_;
v_currMacroScope_383_ = v_currMacroScope_507_;
v_cancelTk_x3f_384_ = v_cancelTk_x3f_508_;
v_inheritedTraceOptions_385_ = v_inheritedTraceOptions_509_;
v_currRecDepth_386_ = v_currRecDepth_510_;
v_ref_387_ = v_ref_511_;
v_suppressElabErrors_388_ = v_suppressElabErrors_512_;
v_isRecordingDeps_389_ = v_isRecordingDeps_513_;
v___y_390_ = v___x_372_;
goto v___jp_373_;
}
}
else
{
if (v___x_521_ == 0)
{
lean_dec_ref_known(v___x_517_, 3);
lean_inc(v___x_372_);
lean_inc(v_ref_511_);
lean_inc(v_cancelTk_x3f_508_);
lean_inc(v_currMacroScope_507_);
lean_inc(v_quotContext_506_);
lean_inc(v_maxHeartbeats_505_);
lean_inc_ref(v_fileMap_501_);
lean_inc_ref(v_fileName_500_);
v___y_374_ = v___x_518_;
v___y_375_ = v___x_514_;
v_fileName_376_ = v_fileName_500_;
v_fileMap_377_ = v_fileMap_501_;
v_currNamespace_378_ = v_currNamespace_502_;
v_openDecls_379_ = v_openDecls_503_;
v_initHeartbeats_380_ = v_initHeartbeats_504_;
v_maxHeartbeats_381_ = v_maxHeartbeats_505_;
v_quotContext_382_ = v_quotContext_506_;
v_currMacroScope_383_ = v_currMacroScope_507_;
v_cancelTk_x3f_384_ = v_cancelTk_x3f_508_;
v_inheritedTraceOptions_385_ = v_inheritedTraceOptions_509_;
v_currRecDepth_386_ = v_currRecDepth_510_;
v_ref_387_ = v_ref_511_;
v_suppressElabErrors_388_ = v_suppressElabErrors_512_;
v_isRecordingDeps_389_ = v_isRecordingDeps_513_;
v___y_390_ = v___x_372_;
goto v___jp_373_;
}
else
{
lean_dec(v_currRecDepth_510_);
lean_dec_ref(v_inheritedTraceOptions_509_);
lean_dec(v_initHeartbeats_504_);
lean_dec(v_openDecls_503_);
lean_dec(v_currNamespace_502_);
lean_inc(v___x_372_);
v___y_459_ = v___x_372_;
v___y_460_ = v___x_518_;
v___y_461_ = v___x_514_;
v___y_462_ = v___x_329_;
v___y_463_ = v___x_517_;
goto v___jp_458_;
}
}
}
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v_env_532_; lean_object* v_nextMacroScope_533_; lean_object* v_ngen_534_; lean_object* v_auxDeclNGen_535_; lean_object* v_traceState_536_; lean_object* v_recordedDeps_537_; lean_object* v_messages_538_; lean_object* v_infoState_539_; lean_object* v_snapshotTasks_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_549_; 
v___x_531_ = lean_st_ref_take(v___x_372_);
v_env_532_ = lean_ctor_get(v___x_531_, 0);
v_nextMacroScope_533_ = lean_ctor_get(v___x_531_, 1);
v_ngen_534_ = lean_ctor_get(v___x_531_, 2);
v_auxDeclNGen_535_ = lean_ctor_get(v___x_531_, 3);
v_traceState_536_ = lean_ctor_get(v___x_531_, 4);
v_recordedDeps_537_ = lean_ctor_get(v___x_531_, 6);
v_messages_538_ = lean_ctor_get(v___x_531_, 7);
v_infoState_539_ = lean_ctor_get(v___x_531_, 8);
v_snapshotTasks_540_ = lean_ctor_get(v___x_531_, 9);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v___x_531_, 5);
lean_dec(v_unused_550_);
v___x_542_ = v___x_531_;
v_isShared_543_ = v_isSharedCheck_549_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_snapshotTasks_540_);
lean_inc(v_infoState_539_);
lean_inc(v_messages_538_);
lean_inc(v_recordedDeps_537_);
lean_inc(v_traceState_536_);
lean_inc(v_auxDeclNGen_535_);
lean_inc(v_ngen_534_);
lean_inc(v_nextMacroScope_533_);
lean_inc(v_env_532_);
lean_dec(v___x_531_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_549_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = l_Lean_Kernel_enableDiag(v_env_532_, v___y_530_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 5, v___x_367_);
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_nextMacroScope_533_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_ngen_534_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_auxDeclNGen_535_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v_traceState_536_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_548_, 6, v_recordedDeps_537_);
lean_ctor_set(v_reuseFailAlloc_548_, 7, v_messages_538_);
lean_ctor_set(v_reuseFailAlloc_548_, 8, v_infoState_539_);
lean_ctor_set(v_reuseFailAlloc_548_, 9, v_snapshotTasks_540_);
v___x_546_ = v_reuseFailAlloc_548_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; 
v___x_547_ = lean_st_ref_put(v___x_372_, v___x_546_);
v_fileName_500_ = v_fileName_340_;
v_fileMap_501_ = v_fileMap_341_;
v_currNamespace_502_ = v_currNamespace_354_;
v_openDecls_503_ = v_openDecls_355_;
v_initHeartbeats_504_ = v___x_371_;
v_maxHeartbeats_505_ = v___x_358_;
v_quotContext_506_ = v___x_359_;
v_currMacroScope_507_ = v___x_360_;
v_cancelTk_x3f_508_ = v_cancelTk_x3f_343_;
v_inheritedTraceOptions_509_ = v___x_527_;
v_currRecDepth_510_ = v___x_333_;
v_ref_511_ = v___x_361_;
v_suppressElabErrors_512_ = v___x_329_;
v_isRecordingDeps_513_ = v___x_329_;
goto v___jp_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___boxed(lean_object* v_env_554_, lean_object* v_mctx_555_, lean_object* v_lctx_556_, lean_object* v_opts_557_, lean_object* v_namingCtx_558_, lean_object* v_x_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_554_, v_mctx_555_, v_lctx_556_, v_opts_557_, v_namingCtx_558_, v_x_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(lean_object* v_00_u03b1_564_, lean_object* v_env_565_, lean_object* v_mctx_566_, lean_object* v_lctx_567_, lean_object* v_opts_568_, lean_object* v_namingCtx_569_, lean_object* v_x_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_565_, v_mctx_566_, v_lctx_567_, v_opts_568_, v_namingCtx_569_, v_x_570_, v_a_571_, v_a_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___boxed(lean_object* v_00_u03b1_575_, lean_object* v_env_576_, lean_object* v_mctx_577_, lean_object* v_lctx_578_, lean_object* v_opts_579_, lean_object* v_namingCtx_580_, lean_object* v_x_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope(v_00_u03b1_575_, v_env_576_, v_mctx_577_, v_lctx_578_, v_opts_579_, v_namingCtx_580_, v_x_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
return v_res_585_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(lean_object* v_stx_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Syntax_getKind(v_stx_589_);
if (lean_obj_tag(v___x_590_) == 1)
{
lean_object* v_pre_591_; 
v_pre_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_pre_591_);
if (lean_obj_tag(v_pre_591_) == 1)
{
lean_object* v_pre_592_; 
v_pre_592_ = lean_ctor_get(v_pre_591_, 0);
lean_inc(v_pre_592_);
if (lean_obj_tag(v_pre_592_) == 1)
{
lean_object* v_pre_593_; 
v_pre_593_ = lean_ctor_get(v_pre_592_, 0);
lean_inc(v_pre_593_);
if (lean_obj_tag(v_pre_593_) == 1)
{
lean_object* v_pre_594_; 
v_pre_594_ = lean_ctor_get(v_pre_593_, 0);
if (lean_obj_tag(v_pre_594_) == 0)
{
lean_object* v_str_595_; lean_object* v_str_596_; lean_object* v_str_597_; lean_object* v_str_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_str_595_ = lean_ctor_get(v___x_590_, 1);
lean_inc_ref(v_str_595_);
lean_dec_ref_known(v___x_590_, 2);
v_str_596_ = lean_ctor_get(v_pre_591_, 1);
lean_inc_ref(v_str_596_);
lean_dec_ref_known(v_pre_591_, 2);
v_str_597_ = lean_ctor_get(v_pre_592_, 1);
lean_inc_ref(v_str_597_);
lean_dec_ref_known(v_pre_592_, 2);
v_str_598_ = lean_ctor_get(v_pre_593_, 1);
lean_inc_ref(v_str_598_);
lean_dec_ref_known(v_pre_593_, 2);
v___x_599_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_600_ = lean_string_dec_eq(v_str_598_, v___x_599_);
lean_dec_ref(v_str_598_);
if (v___x_600_ == 0)
{
lean_dec_ref(v_str_597_);
lean_dec_ref(v_str_596_);
lean_dec_ref(v_str_595_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_602_ = lean_string_dec_eq(v_str_597_, v___x_601_);
lean_dec_ref(v_str_597_);
if (v___x_602_ == 0)
{
lean_dec_ref(v_str_596_);
lean_dec_ref(v_str_595_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_604_ = lean_string_dec_eq(v_str_596_, v___x_603_);
lean_dec_ref(v_str_596_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_str_595_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__1));
v___x_606_ = lean_string_dec_eq(v_str_595_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__2));
v___x_608_ = lean_string_dec_eq(v_str_595_, v___x_607_);
lean_dec_ref(v_str_595_);
return v___x_608_;
}
else
{
lean_dec_ref(v_str_595_);
return v___x_606_;
}
}
}
}
}
else
{
uint8_t v___x_609_; 
lean_dec_ref_known(v_pre_593_, 2);
lean_dec_ref_known(v_pre_592_, 2);
lean_dec_ref_known(v_pre_591_, 2);
lean_dec_ref_known(v___x_590_, 2);
v___x_609_ = 0;
return v___x_609_;
}
}
else
{
uint8_t v___x_610_; 
lean_dec_ref_known(v_pre_592_, 2);
lean_dec(v_pre_593_);
lean_dec_ref_known(v_pre_591_, 2);
lean_dec_ref_known(v___x_590_, 2);
v___x_610_ = 0;
return v___x_610_;
}
}
else
{
uint8_t v___x_611_; 
lean_dec(v_pre_592_);
lean_dec_ref_known(v_pre_591_, 2);
lean_dec_ref_known(v___x_590_, 2);
v___x_611_ = 0;
return v___x_611_;
}
}
else
{
uint8_t v___x_612_; 
lean_dec_ref_known(v___x_590_, 2);
lean_dec(v_pre_591_);
v___x_612_ = 0;
return v___x_612_;
}
}
else
{
uint8_t v___x_613_; 
lean_dec(v___x_590_);
v___x_613_ = 0;
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___boxed(lean_object* v_stx_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_614_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(lean_object* v_x_617_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_unsigned_to_nat(0u);
return v___x_618_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_unsigned_to_nat(1u);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx___boxed(lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorIdx(v_x_620_);
lean_dec(v_x_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(lean_object* v_t_622_, lean_object* v_k_623_){
_start:
{
if (lean_obj_tag(v_t_622_) == 0)
{
lean_object* v_tacticSeq_624_; lean_object* v_insertPos_625_; lean_object* v___x_626_; 
v_tacticSeq_624_ = lean_ctor_get(v_t_622_, 0);
lean_inc(v_tacticSeq_624_);
v_insertPos_625_ = lean_ctor_get(v_t_622_, 1);
lean_inc(v_insertPos_625_);
lean_dec_ref_known(v_t_622_, 2);
v___x_626_ = lean_apply_2(v_k_623_, v_tacticSeq_624_, v_insertPos_625_);
return v___x_626_;
}
else
{
return v_k_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(lean_object* v_motive_627_, lean_object* v_ctorIdx_628_, lean_object* v_t_629_, lean_object* v_h_630_, lean_object* v_k_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_629_, v_k_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___boxed(lean_object* v_motive_633_, lean_object* v_ctorIdx_634_, lean_object* v_t_635_, lean_object* v_h_636_, lean_object* v_k_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim(v_motive_633_, v_ctorIdx_634_, v_t_635_, v_h_636_, v_k_637_);
lean_dec(v_ctorIdx_634_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim___redArg(lean_object* v_t_639_, lean_object* v_unsolvedGoal_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_639_, v_unsolvedGoal_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_unsolvedGoal_elim(lean_object* v_motive_642_, lean_object* v_t_643_, lean_object* v_h_644_, lean_object* v_unsolvedGoal_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_643_, v_unsolvedGoal_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim___redArg(lean_object* v_t_647_, lean_object* v_sorryTactic_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_647_, v_sorryTactic_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_sorryTactic_elim(lean_object* v_motive_650_, lean_object* v_t_651_, lean_object* v_h_652_, lean_object* v_sorryTactic_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_TriggerKind_ctorElim___redArg(v_t_651_, v_sorryTactic_653_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1(void){
_start:
{
uint32_t v___x_658_; lean_object* v___x_659_; 
v___x_658_ = 32;
v___x_659_ = lean_box_uint32(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(lean_object* v_tacticSeq_660_, lean_object* v_fileMap_661_){
_start:
{
uint8_t v___x_662_; lean_object* v___x_663_; 
v___x_662_ = 0;
v___x_663_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_660_, v___x_662_);
if (lean_obj_tag(v___x_663_) == 1)
{
lean_object* v_val_664_; lean_object* v___x_665_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = l_Lean_Syntax_getTailPos_x3f(v_tacticSeq_660_, v___x_662_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v_val_666_; lean_object* v_startPos_667_; lean_object* v_line_668_; lean_object* v_column_669_; lean_object* v_endPos_670_; lean_object* v_line_671_; uint8_t v___x_672_; 
v_val_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v___x_665_, 1);
lean_inc_ref(v_fileMap_661_);
v_startPos_667_ = l_Lean_FileMap_toPosition(v_fileMap_661_, v_val_664_);
lean_dec(v_val_664_);
v_line_668_ = lean_ctor_get(v_startPos_667_, 0);
lean_inc(v_line_668_);
v_column_669_ = lean_ctor_get(v_startPos_667_, 1);
lean_inc(v_column_669_);
lean_dec_ref(v_startPos_667_);
v_endPos_670_ = l_Lean_FileMap_toPosition(v_fileMap_661_, v_val_666_);
lean_dec(v_val_666_);
v_line_671_ = lean_ctor_get(v_endPos_670_, 0);
lean_inc(v_line_671_);
lean_dec_ref(v_endPos_670_);
v___x_672_ = lean_nat_dec_eq(v_line_668_, v_line_671_);
lean_dec(v_line_671_);
lean_dec(v_line_668_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__0));
v___x_674_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed__const__1;
v___x_675_ = l_List_replicateTR___redArg(v_column_669_, v___x_674_);
v___x_676_ = lean_string_mk(v___x_675_);
v___x_677_ = lean_string_append(v___x_673_, v___x_676_);
lean_dec_ref(v___x_676_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; 
lean_dec(v_column_669_);
v___x_678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__1));
return v___x_678_;
}
}
else
{
lean_object* v___x_679_; 
lean_dec(v___x_665_);
lean_dec(v_val_664_);
lean_dec_ref(v_fileMap_661_);
v___x_679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_679_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v___x_663_);
lean_dec_ref(v_fileMap_661_);
v___x_680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___closed__2));
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep___boxed(lean_object* v_tacticSeq_681_, lean_object* v_fileMap_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_681_, v_fileMap_682_);
lean_dec(v_tacticSeq_681_);
return v_res_683_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_686_ = lean_string_utf8_byte_size(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_687_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__1);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___x_688_);
lean_ctor_set(v___x_690_, 2, v___x_687_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(lean_object* v_p_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
lean_inc(v_p_691_);
v___x_694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_p_691_);
lean_ctor_set(v___x_694_, 2, v___x_693_);
lean_ctor_set(v___x_694_, 3, v_p_691_);
v___x_695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_692_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(lean_object* v_range_696_){
_start:
{
lean_object* v_start_697_; lean_object* v_stop_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_708_; 
v_start_697_ = lean_ctor_get(v_range_696_, 0);
v_stop_698_ = lean_ctor_get(v_range_696_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_range_696_);
if (v_isSharedCheck_708_ == 0)
{
v___x_700_ = v_range_696_;
v_isShared_701_ = v_isSharedCheck_708_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_stop_698_);
lean_inc(v_start_697_);
lean_dec(v_range_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_708_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_703_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__2);
v___x_704_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_start_697_);
lean_ctor_set(v___x_704_, 2, v___x_703_);
lean_ctor_set(v___x_704_, 3, v_stop_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 2);
lean_ctor_set(v___x_700_, 1, v___x_702_);
lean_ctor_set(v___x_700_, 0, v___x_704_);
v___x_706_ = v___x_700_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_702_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(lean_object* v_mc_x3f_709_, lean_object* v_nc_x3f_710_, lean_object* v_msg_711_, lean_object* v_acc_712_){
_start:
{
switch(lean_obj_tag(v_msg_711_))
{
case 3:
{
lean_object* v_a_713_; lean_object* v_a_714_; lean_object* v___x_715_; 
lean_dec(v_mc_x3f_709_);
v_a_713_ = lean_ctor_get(v_msg_711_, 0);
v_a_714_ = lean_ctor_get(v_msg_711_, 1);
lean_inc_ref(v_a_713_);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v_a_713_);
v_mc_x3f_709_ = v___x_715_;
v_msg_711_ = v_a_714_;
goto _start;
}
case 4:
{
lean_object* v_a_717_; lean_object* v_a_718_; lean_object* v___x_719_; 
lean_dec(v_nc_x3f_710_);
v_a_717_ = lean_ctor_get(v_msg_711_, 0);
v_a_718_ = lean_ctor_get(v_msg_711_, 1);
lean_inc_ref(v_a_717_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v_a_717_);
v_nc_x3f_710_ = v___x_719_;
v_msg_711_ = v_a_718_;
goto _start;
}
case 5:
{
lean_object* v_a_721_; 
v_a_721_ = lean_ctor_get(v_msg_711_, 1);
v_msg_711_ = v_a_721_;
goto _start;
}
case 6:
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v_msg_711_, 0);
v_msg_711_ = v_a_723_;
goto _start;
}
case 8:
{
lean_object* v_a_725_; 
v_a_725_ = lean_ctor_get(v_msg_711_, 1);
v_msg_711_ = v_a_725_;
goto _start;
}
case 7:
{
lean_object* v_a_727_; lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_727_ = lean_ctor_get(v_msg_711_, 0);
v_a_728_ = lean_ctor_get(v_msg_711_, 1);
lean_inc(v_nc_x3f_710_);
lean_inc(v_mc_x3f_709_);
v___x_729_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_709_, v_nc_x3f_710_, v_a_727_, v_acc_712_);
v_msg_711_ = v_a_728_;
v_acc_712_ = v___x_729_;
goto _start;
}
case 2:
{
lean_object* v_a_731_; 
v_a_731_ = lean_ctor_get(v_msg_711_, 1);
v_msg_711_ = v_a_731_;
goto _start;
}
case 9:
{
lean_object* v_msg_733_; lean_object* v_children_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_msg_733_ = lean_ctor_get(v_msg_711_, 1);
v_children_734_ = lean_ctor_get(v_msg_711_, 2);
lean_inc(v_nc_x3f_710_);
lean_inc(v_mc_x3f_709_);
v___x_735_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_709_, v_nc_x3f_710_, v_msg_733_, v_acc_712_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_array_get_size(v_children_734_);
v___x_738_ = lean_nat_dec_lt(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec(v_nc_x3f_710_);
lean_dec(v_mc_x3f_709_);
return v___x_735_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = lean_nat_dec_le(v___x_737_, v___x_737_);
if (v___x_739_ == 0)
{
if (v___x_738_ == 0)
{
lean_dec(v_nc_x3f_710_);
lean_dec(v_mc_x3f_709_);
return v___x_735_;
}
else
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_737_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_709_, v_nc_x3f_710_, v_children_734_, v___x_740_, v___x_741_, v___x_735_);
return v___x_742_;
}
}
else
{
size_t v___x_743_; size_t v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_737_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_709_, v_nc_x3f_710_, v_children_734_, v___x_743_, v___x_744_, v___x_735_);
return v___x_745_;
}
}
}
case 1:
{
if (lean_obj_tag(v_mc_x3f_709_) == 1)
{
if (lean_obj_tag(v_nc_x3f_710_) == 1)
{
lean_object* v_a_746_; lean_object* v_val_747_; lean_object* v_val_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_a_746_ = lean_ctor_get(v_msg_711_, 0);
v_val_747_ = lean_ctor_get(v_mc_x3f_709_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v_mc_x3f_709_, 1);
v_val_748_ = lean_ctor_get(v_nc_x3f_710_, 0);
lean_inc(v_val_748_);
lean_dec_ref_known(v_nc_x3f_710_, 1);
lean_inc(v_a_746_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_val_748_);
lean_ctor_set(v___x_749_, 1, v_a_746_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_val_747_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = lean_array_push(v_acc_712_, v___x_750_);
return v___x_751_;
}
else
{
lean_dec_ref_known(v_mc_x3f_709_, 1);
lean_dec(v_nc_x3f_710_);
return v_acc_712_;
}
}
else
{
lean_dec(v_nc_x3f_710_);
lean_dec(v_mc_x3f_709_);
return v_acc_712_;
}
}
default: 
{
lean_dec(v_nc_x3f_710_);
lean_dec(v_mc_x3f_709_);
return v_acc_712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(lean_object* v_mc_x3f_752_, lean_object* v_nc_x3f_753_, lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_, lean_object* v_b_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; size_t v___x_761_; size_t v___x_762_; 
v___x_759_ = lean_array_uget_borrowed(v_as_754_, v_i_755_);
lean_inc(v_nc_x3f_753_);
lean_inc(v_mc_x3f_752_);
v___x_760_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_752_, v_nc_x3f_753_, v___x_759_, v_b_757_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_755_, v___x_761_);
v_i_755_ = v___x_762_;
v_b_757_ = v___x_760_;
goto _start;
}
else
{
lean_dec(v_nc_x3f_753_);
lean_dec(v_mc_x3f_752_);
return v_b_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0___boxed(lean_object* v_mc_x3f_764_, lean_object* v_nc_x3f_765_, lean_object* v_as_766_, lean_object* v_i_767_, lean_object* v_stop_768_, lean_object* v_b_769_){
_start:
{
size_t v_i_boxed_770_; size_t v_stop_boxed_771_; lean_object* v_res_772_; 
v_i_boxed_770_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_stop_boxed_771_ = lean_unbox_usize(v_stop_768_);
lean_dec(v_stop_768_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go_spec__0(v_mc_x3f_764_, v_nc_x3f_765_, v_as_766_, v_i_boxed_770_, v_stop_boxed_771_, v_b_769_);
lean_dec_ref(v_as_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go___boxed(lean_object* v_mc_x3f_773_, lean_object* v_nc_x3f_774_, lean_object* v_msg_775_, lean_object* v_acc_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v_mc_x3f_773_, v_nc_x3f_774_, v_msg_775_, v_acc_776_);
lean_dec_ref(v_msg_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(lean_object* v_msg_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_box(0);
v___x_782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___closed__0));
v___x_783_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage_go(v___x_781_, v___x_781_, v_msg_780_, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage___boxed(lean_object* v_msg_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_msg_784_);
lean_dec_ref(v_msg_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(lean_object* v_range_788_, lean_object* v_stx_789_){
_start:
{
lean_object* v___x_790_; 
lean_inc(v_stx_789_);
v___x_790_ = l_Lean_Syntax_getKind(v_stx_789_);
if (lean_obj_tag(v___x_790_) == 1)
{
lean_object* v_pre_791_; 
v_pre_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_pre_791_);
if (lean_obj_tag(v_pre_791_) == 1)
{
lean_object* v_pre_792_; 
v_pre_792_ = lean_ctor_get(v_pre_791_, 0);
lean_inc(v_pre_792_);
if (lean_obj_tag(v_pre_792_) == 1)
{
lean_object* v_pre_793_; 
v_pre_793_ = lean_ctor_get(v_pre_792_, 0);
lean_inc(v_pre_793_);
if (lean_obj_tag(v_pre_793_) == 1)
{
lean_object* v_pre_794_; 
v_pre_794_ = lean_ctor_get(v_pre_793_, 0);
if (lean_obj_tag(v_pre_794_) == 0)
{
lean_object* v_str_795_; lean_object* v_str_796_; lean_object* v_str_797_; lean_object* v_str_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_str_795_ = lean_ctor_get(v___x_790_, 1);
lean_inc_ref(v_str_795_);
lean_dec_ref_known(v___x_790_, 2);
v_str_796_ = lean_ctor_get(v_pre_791_, 1);
lean_inc_ref(v_str_796_);
lean_dec_ref_known(v_pre_791_, 2);
v_str_797_ = lean_ctor_get(v_pre_792_, 1);
lean_inc_ref(v_str_797_);
lean_dec_ref_known(v_pre_792_, 2);
v_str_798_ = lean_ctor_get(v_pre_793_, 1);
lean_inc_ref(v_str_798_);
lean_dec_ref_known(v_pre_793_, 2);
v___x_799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__7_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_800_ = lean_string_dec_eq(v_str_798_, v___x_799_);
lean_dec_ref(v_str_798_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
lean_dec_ref(v_str_797_);
lean_dec_ref(v_str_796_);
lean_dec_ref(v_str_795_);
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_801_ = lean_box(0);
return v___x_801_;
}
else
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic___closed__0));
v___x_803_ = lean_string_dec_eq(v_str_797_, v___x_802_);
lean_dec_ref(v_str_797_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec_ref(v_str_796_);
lean_dec_ref(v_str_795_);
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_804_ = lean_box(0);
return v___x_804_;
}
else
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__11_00___x40_Lean_Elab_Tactic_AutoTry_3400009768____hygCtx___hyg_4_));
v___x_806_ = lean_string_dec_eq(v_str_796_, v___x_805_);
lean_dec_ref(v_str_796_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_dec_ref(v_str_795_);
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_807_ = lean_box(0);
return v___x_807_;
}
else
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__0));
v___x_809_ = lean_string_dec_eq(v_str_795_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f___closed__1));
v___x_811_ = lean_string_dec_eq(v_str_795_, v___x_810_);
lean_dec_ref(v_str_795_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_812_ = lean_box(0);
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v_body_814_; lean_object* v___y_816_; lean_object* v___x_819_; 
v___x_813_ = lean_unsigned_to_nat(1u);
v_body_814_ = l_Lean_Syntax_getArg(v_stx_789_, v___x_813_);
v___x_819_ = l_Lean_Syntax_getTailPos_x3f(v_body_814_, v___x_809_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_unsigned_to_nat(2u);
v___x_821_ = l_Lean_Syntax_getArg(v_stx_789_, v___x_820_);
lean_dec(v_stx_789_);
v___x_822_ = l_Lean_Syntax_getPos_x3f(v___x_821_, v___x_809_);
lean_dec(v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_stop_823_; 
v_stop_823_ = lean_ctor_get(v_range_788_, 1);
lean_inc(v_stop_823_);
lean_dec_ref(v_range_788_);
v___y_816_ = v_stop_823_;
goto v___jp_815_;
}
else
{
lean_object* v_val_824_; 
lean_dec_ref(v_range_788_);
v_val_824_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v___x_822_, 1);
v___y_816_ = v_val_824_;
goto v___jp_815_;
}
}
else
{
lean_object* v_val_825_; 
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v_val_825_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v___x_819_, 1);
v___y_816_ = v_val_825_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_body_814_);
lean_ctor_set(v___x_817_, 1, v___y_816_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
}
else
{
lean_object* v___x_826_; lean_object* v_body_827_; lean_object* v___y_829_; uint8_t v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v_str_795_);
v___x_826_ = lean_unsigned_to_nat(0u);
v_body_827_ = l_Lean_Syntax_getArg(v_stx_789_, v___x_826_);
lean_dec(v_stx_789_);
v___x_832_ = 0;
v___x_833_ = l_Lean_Syntax_getTailPos_x3f(v_body_827_, v___x_832_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_stop_834_; 
v_stop_834_ = lean_ctor_get(v_range_788_, 1);
lean_inc(v_stop_834_);
lean_dec_ref(v_range_788_);
v___y_829_ = v_stop_834_;
goto v___jp_828_;
}
else
{
lean_object* v_val_835_; 
lean_dec_ref(v_range_788_);
v_val_835_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v___x_833_, 1);
v___y_829_ = v_val_835_;
goto v___jp_828_;
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_body_827_);
lean_ctor_set(v___x_830_, 1, v___y_829_);
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
}
}
}
else
{
lean_object* v___x_836_; 
lean_dec_ref_known(v_pre_793_, 2);
lean_dec_ref_known(v_pre_792_, 2);
lean_dec_ref_known(v_pre_791_, 2);
lean_dec_ref_known(v___x_790_, 2);
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_836_ = lean_box(0);
return v___x_836_;
}
}
else
{
lean_object* v___x_837_; 
lean_dec(v_pre_793_);
lean_dec_ref_known(v_pre_792_, 2);
lean_dec_ref_known(v_pre_791_, 2);
lean_dec_ref_known(v___x_790_, 2);
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_837_ = lean_box(0);
return v___x_837_;
}
}
else
{
lean_object* v___x_838_; 
lean_dec(v_pre_792_);
lean_dec_ref_known(v_pre_791_, 2);
lean_dec_ref_known(v___x_790_, 2);
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_838_ = lean_box(0);
return v___x_838_;
}
}
else
{
lean_object* v___x_839_; 
lean_dec_ref_known(v___x_790_, 2);
lean_dec(v_pre_791_);
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_839_ = lean_box(0);
return v___x_839_;
}
}
else
{
lean_object* v___x_840_; 
lean_dec(v___x_790_);
lean_dec(v_stx_789_);
lean_dec_ref(v_range_788_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(lean_object* v_range_844_, lean_object* v_stx_845_){
_start:
{
lean_object* v___x_846_; 
lean_inc(v_stx_845_);
lean_inc_ref(v_range_844_);
v___x_846_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_seqBodyAndInsertPos_x3f(v_range_844_, v_stx_845_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_dec(v_stx_845_);
lean_dec_ref(v_range_844_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; size_t v_sz_850_; size_t v___x_851_; lean_object* v___x_852_; lean_object* v_fst_853_; 
lean_dec(v___x_846_);
v___x_847_ = l_Lean_Syntax_getArgs(v_stx_845_);
lean_dec(v_stx_845_);
v___x_848_ = lean_box(0);
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_850_ = lean_array_size(v___x_847_);
v___x_851_ = ((size_t)0ULL);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_844_, v___x_847_, v_sz_850_, v___x_851_, v___x_849_);
lean_dec_ref(v___x_847_);
v_fst_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_fst_853_);
lean_dec_ref(v___x_852_);
if (lean_obj_tag(v_fst_853_) == 0)
{
return v___x_848_;
}
else
{
lean_object* v_val_854_; 
v_val_854_ = lean_ctor_get(v_fst_853_, 0);
lean_inc(v_val_854_);
lean_dec_ref_known(v_fst_853_, 1);
return v_val_854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(lean_object* v_range_855_, lean_object* v_as_856_, size_t v_sz_857_, size_t v_i_858_, lean_object* v_b_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = lean_usize_dec_lt(v_i_858_, v_sz_857_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_range_855_);
lean_inc_ref(v_b_859_);
return v_b_859_;
}
else
{
lean_object* v___x_861_; lean_object* v_a_862_; lean_object* v___x_863_; 
v___x_861_ = lean_box(0);
v_a_862_ = lean_array_uget_borrowed(v_as_856_, v_i_858_);
lean_inc(v_a_862_);
lean_inc_ref(v_range_855_);
v___x_863_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_855_, v_a_862_);
if (lean_obj_tag(v___x_863_) == 1)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref(v_range_855_);
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_861_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; size_t v___x_867_; size_t v___x_868_; 
lean_dec(v___x_863_);
v___x_866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_858_, v___x_867_);
v_i_858_ = v___x_868_;
v_b_859_ = v___x_866_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___boxed(lean_object* v_range_870_, lean_object* v_as_871_, lean_object* v_sz_872_, lean_object* v_i_873_, lean_object* v_b_874_){
_start:
{
size_t v_sz_boxed_875_; size_t v_i_boxed_876_; lean_object* v_res_877_; 
v_sz_boxed_875_ = lean_unbox_usize(v_sz_872_);
lean_dec(v_sz_872_);
v_i_boxed_876_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0(v_range_870_, v_as_871_, v_sz_boxed_875_, v_i_boxed_876_, v_b_874_);
lean_dec_ref(v_b_874_);
lean_dec_ref(v_as_871_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(lean_object* v_range_878_, lean_object* v_stx_879_){
_start:
{
uint8_t v___x_880_; lean_object* v___x_881_; 
v___x_880_ = 0;
v___x_881_ = l_Lean_Syntax_getRange_x3f(v_stx_879_, v___x_880_);
if (lean_obj_tag(v___x_881_) == 1)
{
lean_object* v_val_882_; uint8_t v___x_883_; 
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l_Lean_Syntax_Range_includes(v_val_882_, v_range_878_, v___x_880_, v___x_880_);
lean_dec(v_val_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
lean_dec(v_stx_879_);
lean_dec_ref(v_range_878_);
v___x_884_ = lean_box(0);
return v___x_884_;
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; size_t v_sz_887_; size_t v___x_888_; lean_object* v___x_889_; lean_object* v_fst_890_; 
v___x_885_ = l_Lean_Syntax_getArgs(v_stx_879_);
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v_sz_887_ = lean_array_size(v___x_885_);
v___x_888_ = ((size_t)0ULL);
lean_inc_ref(v_range_878_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_878_, v___x_885_, v_sz_887_, v___x_888_, v___x_886_);
lean_dec_ref(v___x_885_);
v_fst_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_fst_890_);
lean_dec_ref(v___x_889_);
if (lean_obj_tag(v_fst_890_) == 0)
{
lean_object* v___x_891_; 
v___x_891_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree(v_range_878_, v_stx_879_);
return v___x_891_;
}
else
{
lean_object* v_val_892_; 
lean_dec(v_stx_879_);
lean_dec_ref(v_range_878_);
v_val_892_ = lean_ctor_get(v_fst_890_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v_fst_890_, 1);
return v_val_892_;
}
}
}
else
{
lean_object* v___x_893_; 
lean_dec(v___x_881_);
lean_dec(v_stx_879_);
lean_dec_ref(v_range_878_);
v___x_893_ = lean_box(0);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(lean_object* v_range_894_, lean_object* v_as_895_, size_t v_sz_896_, size_t v_i_897_, lean_object* v_b_898_){
_start:
{
uint8_t v___x_899_; 
v___x_899_ = lean_usize_dec_lt(v_i_897_, v_sz_896_);
if (v___x_899_ == 0)
{
lean_dec_ref(v_range_894_);
lean_inc_ref(v_b_898_);
return v_b_898_;
}
else
{
lean_object* v___x_900_; lean_object* v_a_901_; lean_object* v___x_902_; 
v___x_900_ = lean_box(0);
v_a_901_ = lean_array_uget_borrowed(v_as_895_, v_i_897_);
lean_inc(v_a_901_);
lean_inc_ref(v_range_894_);
v___x_902_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_894_, v_a_901_);
if (lean_obj_tag(v___x_902_) == 1)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec_ref(v_range_894_);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_900_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; size_t v___x_906_; size_t v___x_907_; 
lean_dec(v___x_902_);
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_outermostSeqInSubtree_spec__0___closed__0));
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_add(v_i_897_, v___x_906_);
v_i_897_ = v___x_907_;
v_b_898_ = v___x_905_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0___boxed(lean_object* v_range_909_, lean_object* v_as_910_, lean_object* v_sz_911_, lean_object* v_i_912_, lean_object* v_b_913_){
_start:
{
size_t v_sz_boxed_914_; size_t v_i_boxed_915_; lean_object* v_res_916_; 
v_sz_boxed_914_ = lean_unbox_usize(v_sz_911_);
lean_dec(v_sz_911_);
v_i_boxed_915_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_res_916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind_spec__0(v_range_909_, v_as_910_, v_sz_boxed_914_, v_i_boxed_915_, v_b_913_);
lean_dec_ref(v_b_913_);
lean_dec_ref(v_as_910_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody(lean_object* v_cmd_917_, lean_object* v_range_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v_range_918_, v_cmd_917_);
return v___x_919_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(lean_object* v_opts_920_, lean_object* v_opt_921_){
_start:
{
lean_object* v_name_922_; lean_object* v_defValue_923_; lean_object* v_map_924_; lean_object* v___x_925_; 
v_name_922_ = lean_ctor_get(v_opt_921_, 0);
v_defValue_923_ = lean_ctor_get(v_opt_921_, 1);
v_map_924_ = lean_ctor_get(v_opts_920_, 0);
v___x_925_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_924_, v_name_922_);
if (lean_obj_tag(v___x_925_) == 0)
{
uint8_t v___x_926_; 
v___x_926_ = lean_unbox(v_defValue_923_);
return v___x_926_;
}
else
{
lean_object* v_val_927_; 
v_val_927_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v___x_925_, 1);
if (lean_obj_tag(v_val_927_) == 1)
{
uint8_t v_v_928_; 
v_v_928_ = lean_ctor_get_uint8(v_val_927_, 0);
lean_dec_ref_known(v_val_927_, 0);
return v_v_928_;
}
else
{
uint8_t v___x_929_; 
lean_dec(v_val_927_);
v___x_929_ = lean_unbox(v_defValue_923_);
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0___boxed(lean_object* v_opts_930_, lean_object* v_opt_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_930_, v_opt_931_);
lean_dec_ref(v_opt_931_);
lean_dec_ref(v_opts_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(lean_object* v_ctx_934_, lean_object* v_info_935_, lean_object* v_acc_936_){
_start:
{
if (lean_obj_tag(v_info_935_) == 0)
{
lean_object* v_i_937_; lean_object* v_toElabInfo_938_; lean_object* v_mctxBefore_939_; lean_object* v_goalsBefore_940_; lean_object* v_stx_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_959_; 
v_i_937_ = lean_ctor_get(v_info_935_, 0);
lean_inc_ref(v_i_937_);
lean_dec_ref_known(v_info_935_, 1);
v_toElabInfo_938_ = lean_ctor_get(v_i_937_, 0);
lean_inc_ref(v_toElabInfo_938_);
v_mctxBefore_939_ = lean_ctor_get(v_i_937_, 1);
lean_inc_ref(v_mctxBefore_939_);
v_goalsBefore_940_ = lean_ctor_get(v_i_937_, 2);
lean_inc(v_goalsBefore_940_);
lean_dec_ref(v_i_937_);
v_stx_941_ = lean_ctor_get(v_toElabInfo_938_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v_toElabInfo_938_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_toElabInfo_938_, 0);
lean_dec(v_unused_960_);
v___x_943_ = v_toElabInfo_938_;
v_isShared_944_ = v_isSharedCheck_959_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_stx_941_);
lean_dec(v_toElabInfo_938_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_959_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v___x_945_; 
lean_inc(v_stx_941_);
v___x_945_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_isSorryTactic(v_stx_941_);
if (v___x_945_ == 0)
{
lean_del_object(v___x_943_);
lean_dec(v_stx_941_);
lean_dec(v_goalsBefore_940_);
lean_dec_ref(v_mctxBefore_939_);
return v_acc_936_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = l_List_head_x3f___redArg(v_goalsBefore_940_);
lean_dec(v_goalsBefore_940_);
if (lean_obj_tag(v___x_946_) == 1)
{
lean_object* v_toCommandContextInfo_947_; lean_object* v_val_948_; lean_object* v_env_949_; lean_object* v_options_950_; lean_object* v_currNamespace_951_; lean_object* v_openDecls_952_; lean_object* v_namingCtx_954_; 
v_toCommandContextInfo_947_ = lean_ctor_get(v_ctx_934_, 0);
v_val_948_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v___x_946_, 1);
v_env_949_ = lean_ctor_get(v_toCommandContextInfo_947_, 0);
v_options_950_ = lean_ctor_get(v_toCommandContextInfo_947_, 4);
v_currNamespace_951_ = lean_ctor_get(v_toCommandContextInfo_947_, 5);
v_openDecls_952_ = lean_ctor_get(v_toCommandContextInfo_947_, 6);
lean_inc(v_openDecls_952_);
lean_inc(v_currNamespace_951_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v_openDecls_952_);
lean_ctor_set(v___x_943_, 0, v_currNamespace_951_);
v_namingCtx_954_ = v___x_943_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_currNamespace_951_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_openDecls_952_);
v_namingCtx_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = lean_box(1);
lean_inc_ref(v_options_950_);
lean_inc_ref(v_env_949_);
v___x_956_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v_stx_941_);
lean_ctor_set(v___x_956_, 2, v_env_949_);
lean_ctor_set(v___x_956_, 3, v_mctxBefore_939_);
lean_ctor_set(v___x_956_, 4, v_options_950_);
lean_ctor_set(v___x_956_, 5, v_namingCtx_954_);
lean_ctor_set(v___x_956_, 6, v_val_948_);
v___x_957_ = lean_array_push(v_acc_936_, v___x_956_);
return v___x_957_;
}
}
else
{
lean_dec(v___x_946_);
lean_del_object(v___x_943_);
lean_dec(v_stx_941_);
lean_dec_ref(v_mctxBefore_939_);
return v_acc_936_;
}
}
}
}
else
{
lean_dec_ref(v_info_935_);
return v_acc_936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0___boxed(lean_object* v_ctx_961_, lean_object* v_info_962_, lean_object* v_acc_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___lam__0(v_ctx_961_, v_info_962_, v_acc_963_);
lean_dec_ref(v_ctx_961_);
return v_res_964_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(lean_object* v_x_969_){
_start:
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___closed__1));
v___x_971_ = lean_name_eq(v_x_969_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0___boxed(lean_object* v_x_972_){
_start:
{
uint8_t v_res_973_; lean_object* v_r_974_; 
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___lam__0(v_x_972_);
lean_dec(v_x_972_);
v_r_974_ = lean_box(v_res_973_);
return v_r_974_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
if (lean_obj_tag(v_x_976_) == 0)
{
uint8_t v___x_977_; 
v___x_977_ = 0;
return v___x_977_;
}
else
{
lean_object* v_key_978_; lean_object* v_tail_979_; uint8_t v___y_981_; lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; uint8_t v___x_987_; 
v_key_978_ = lean_ctor_get(v_x_976_, 0);
v_tail_979_ = lean_ctor_get(v_x_976_, 2);
v_fst_983_ = lean_ctor_get(v_key_978_, 0);
v_snd_984_ = lean_ctor_get(v_key_978_, 1);
v_fst_985_ = lean_ctor_get(v_a_975_, 0);
v_snd_986_ = lean_ctor_get(v_a_975_, 1);
v___x_987_ = l_Lean_Syntax_instBEqRange_beq(v_fst_983_, v_fst_985_);
if (v___x_987_ == 0)
{
v___y_981_ = v___x_987_;
goto v___jp_980_;
}
else
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_instBEqMVarId_beq(v_snd_984_, v_snd_986_);
v___y_981_ = v___x_988_;
goto v___jp_980_;
}
v___jp_980_:
{
if (v___y_981_ == 0)
{
v_x_976_ = v_tail_979_;
goto _start;
}
else
{
return v___y_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg___boxed(lean_object* v_a_989_, lean_object* v_x_990_){
_start:
{
uint8_t v_res_991_; lean_object* v_r_992_; 
v_res_991_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_989_, v_x_990_);
lean_dec(v_x_990_);
lean_dec_ref(v_a_989_);
v_r_992_ = lean_box(v_res_991_);
return v_r_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
return v_x_993_;
}
else
{
lean_object* v_key_995_; lean_object* v_value_996_; lean_object* v_tail_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1024_; 
v_key_995_ = lean_ctor_get(v_x_994_, 0);
v_value_996_ = lean_ctor_get(v_x_994_, 1);
v_tail_997_ = lean_ctor_get(v_x_994_, 2);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_x_994_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_999_ = v_x_994_;
v_isShared_1000_ = v_isSharedCheck_1024_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_tail_997_);
lean_inc(v_value_996_);
lean_inc(v_key_995_);
lean_dec(v_x_994_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1024_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_fst_1001_; lean_object* v_snd_1002_; lean_object* v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; uint64_t v___x_1006_; uint64_t v___x_1007_; uint64_t v___x_1008_; uint64_t v_fold_1009_; uint64_t v___x_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v_fst_1001_ = lean_ctor_get(v_key_995_, 0);
v_snd_1002_ = lean_ctor_get(v_key_995_, 1);
v___x_1003_ = lean_array_get_size(v_x_993_);
v___x_1004_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1001_);
v___x_1005_ = l_Lean_instHashableMVarId_hash(v_snd_1002_);
v___x_1006_ = lean_uint64_mix_hash(v___x_1004_, v___x_1005_);
v___x_1007_ = 32ULL;
v___x_1008_ = lean_uint64_shift_right(v___x_1006_, v___x_1007_);
v_fold_1009_ = lean_uint64_xor(v___x_1006_, v___x_1008_);
v___x_1010_ = 16ULL;
v___x_1011_ = lean_uint64_shift_right(v_fold_1009_, v___x_1010_);
v___x_1012_ = lean_uint64_xor(v_fold_1009_, v___x_1011_);
v___x_1013_ = lean_uint64_to_usize(v___x_1012_);
v___x_1014_ = lean_usize_of_nat(v___x_1003_);
v___x_1015_ = ((size_t)1ULL);
v___x_1016_ = lean_usize_sub(v___x_1014_, v___x_1015_);
v___x_1017_ = lean_usize_land(v___x_1013_, v___x_1016_);
v___x_1018_ = lean_array_uget_borrowed(v_x_993_, v___x_1017_);
lean_inc(v___x_1018_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 2, v___x_1018_);
v___x_1020_ = v___x_999_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_key_995_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_value_996_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_array_uset(v_x_993_, v___x_1017_, v___x_1020_);
v_x_993_ = v___x_1021_;
v_x_994_ = v_tail_997_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(lean_object* v_i_1025_, lean_object* v_source_1026_, lean_object* v_target_1027_){
_start:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_array_get_size(v_source_1026_);
v___x_1029_ = lean_nat_dec_lt(v_i_1025_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_dec_ref(v_source_1026_);
lean_dec(v_i_1025_);
return v_target_1027_;
}
else
{
lean_object* v_es_1030_; lean_object* v___x_1031_; lean_object* v_source_1032_; lean_object* v_target_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_es_1030_ = lean_array_fget(v_source_1026_, v_i_1025_);
v___x_1031_ = lean_box(0);
v_source_1032_ = lean_array_fset(v_source_1026_, v_i_1025_, v___x_1031_);
v_target_1033_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_target_1027_, v_es_1030_);
v___x_1034_ = lean_unsigned_to_nat(1u);
v___x_1035_ = lean_nat_add(v_i_1025_, v___x_1034_);
lean_dec(v_i_1025_);
v_i_1025_ = v___x_1035_;
v_source_1026_ = v_source_1032_;
v_target_1027_ = v_target_1033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(lean_object* v_data_1037_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_nbuckets_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1038_ = lean_array_get_size(v_data_1037_);
v___x_1039_ = lean_unsigned_to_nat(2u);
v_nbuckets_1040_ = lean_nat_mul(v___x_1038_, v___x_1039_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_mk_array(v_nbuckets_1040_, v___x_1042_);
v___x_1044_ = lean_array_propagate_mark(v_data_1037_, v___x_1043_);
v___x_1045_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v___x_1041_, v_data_1037_, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(lean_object* v_m_1046_, lean_object* v_a_1047_, lean_object* v_b_1048_){
_start:
{
lean_object* v_size_1049_; lean_object* v_buckets_1050_; lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1053_; uint64_t v___x_1054_; uint64_t v___x_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; uint64_t v___x_1058_; uint64_t v_fold_1059_; uint64_t v___x_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; lean_object* v_bkt_1068_; uint8_t v___x_1069_; 
v_size_1049_ = lean_ctor_get(v_m_1046_, 0);
v_buckets_1050_ = lean_ctor_get(v_m_1046_, 1);
v_fst_1051_ = lean_ctor_get(v_a_1047_, 0);
v_snd_1052_ = lean_ctor_get(v_a_1047_, 1);
v___x_1053_ = lean_array_get_size(v_buckets_1050_);
v___x_1054_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1051_);
v___x_1055_ = l_Lean_instHashableMVarId_hash(v_snd_1052_);
v___x_1056_ = lean_uint64_mix_hash(v___x_1054_, v___x_1055_);
v___x_1057_ = 32ULL;
v___x_1058_ = lean_uint64_shift_right(v___x_1056_, v___x_1057_);
v_fold_1059_ = lean_uint64_xor(v___x_1056_, v___x_1058_);
v___x_1060_ = 16ULL;
v___x_1061_ = lean_uint64_shift_right(v_fold_1059_, v___x_1060_);
v___x_1062_ = lean_uint64_xor(v_fold_1059_, v___x_1061_);
v___x_1063_ = lean_uint64_to_usize(v___x_1062_);
v___x_1064_ = lean_usize_of_nat(v___x_1053_);
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_sub(v___x_1064_, v___x_1065_);
v___x_1067_ = lean_usize_land(v___x_1063_, v___x_1066_);
v_bkt_1068_ = lean_array_uget_borrowed(v_buckets_1050_, v___x_1067_);
v___x_1069_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1047_, v_bkt_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1090_; 
lean_inc_ref(v_buckets_1050_);
lean_inc(v_size_1049_);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_m_1046_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; 
v_unused_1091_ = lean_ctor_get(v_m_1046_, 1);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_m_1046_, 0);
lean_dec(v_unused_1092_);
v___x_1071_ = v_m_1046_;
v_isShared_1072_ = v_isSharedCheck_1090_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v_m_1046_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1090_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v_size_x27_1074_; lean_object* v___x_1075_; lean_object* v_buckets_x27_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1073_ = lean_unsigned_to_nat(1u);
v_size_x27_1074_ = lean_nat_add(v_size_1049_, v___x_1073_);
lean_dec(v_size_1049_);
lean_inc(v_bkt_1068_);
v___x_1075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1047_);
lean_ctor_set(v___x_1075_, 1, v_b_1048_);
lean_ctor_set(v___x_1075_, 2, v_bkt_1068_);
v_buckets_x27_1076_ = lean_array_uset(v_buckets_1050_, v___x_1067_, v___x_1075_);
v___x_1077_ = lean_unsigned_to_nat(4u);
v___x_1078_ = lean_nat_mul(v_size_x27_1074_, v___x_1077_);
v___x_1079_ = lean_unsigned_to_nat(3u);
v___x_1080_ = lean_nat_div(v___x_1078_, v___x_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_array_get_size(v_buckets_x27_1076_);
v___x_1082_ = lean_nat_dec_le(v___x_1080_, v___x_1081_);
lean_dec(v___x_1080_);
if (v___x_1082_ == 0)
{
lean_object* v_val_1083_; lean_object* v___x_1085_; 
v_val_1083_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_buckets_x27_1076_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_val_1083_);
lean_ctor_set(v___x_1071_, 0, v_size_x27_1074_);
v___x_1085_ = v___x_1071_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_size_x27_1074_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_val_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
else
{
lean_object* v___x_1088_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_buckets_x27_1076_);
lean_ctor_set(v___x_1071_, 0, v_size_x27_1074_);
v___x_1088_ = v___x_1071_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_size_x27_1074_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_buckets_x27_1076_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_dec(v_b_1048_);
lean_dec_ref(v_a_1047_);
return v_m_1046_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(lean_object* v_m_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_buckets_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v_fold_1104_; uint64_t v___x_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_buckets_1095_ = lean_ctor_get(v_m_1093_, 1);
v_fst_1096_ = lean_ctor_get(v_a_1094_, 0);
v_snd_1097_ = lean_ctor_get(v_a_1094_, 1);
v___x_1098_ = lean_array_get_size(v_buckets_1095_);
v___x_1099_ = l_Lean_Syntax_instHashableRange_hash(v_fst_1096_);
v___x_1100_ = l_Lean_instHashableMVarId_hash(v_snd_1097_);
v___x_1101_ = lean_uint64_mix_hash(v___x_1099_, v___x_1100_);
v___x_1102_ = 32ULL;
v___x_1103_ = lean_uint64_shift_right(v___x_1101_, v___x_1102_);
v_fold_1104_ = lean_uint64_xor(v___x_1101_, v___x_1103_);
v___x_1105_ = 16ULL;
v___x_1106_ = lean_uint64_shift_right(v_fold_1104_, v___x_1105_);
v___x_1107_ = lean_uint64_xor(v_fold_1104_, v___x_1106_);
v___x_1108_ = lean_uint64_to_usize(v___x_1107_);
v___x_1109_ = lean_usize_of_nat(v___x_1098_);
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_sub(v___x_1109_, v___x_1110_);
v___x_1112_ = lean_usize_land(v___x_1108_, v___x_1111_);
v___x_1113_ = lean_array_uget_borrowed(v_buckets_1095_, v___x_1112_);
v___x_1114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_1094_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg___boxed(lean_object* v_m_1115_, lean_object* v_a_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_1115_, v_a_1116_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_m_1115_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(lean_object* v___x_1119_, lean_object* v_fst_1120_, lean_object* v_snd_1121_, lean_object* v___x_1122_, lean_object* v_as_1123_, size_t v_sz_1124_, size_t v_i_1125_, lean_object* v_b_1126_){
_start:
{
lean_object* v_a_1129_; uint8_t v___x_1133_; 
v___x_1133_ = lean_usize_dec_lt(v_i_1125_, v_sz_1124_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___x_1122_);
lean_dec(v_snd_1121_);
lean_dec(v_fst_1120_);
lean_dec_ref(v___x_1119_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_b_1126_);
return v___x_1134_;
}
else
{
lean_object* v_a_1135_; lean_object* v_snd_1136_; lean_object* v_fst_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1173_; 
v_a_1135_ = lean_array_uget(v_as_1123_, v_i_1125_);
v_snd_1136_ = lean_ctor_get(v_a_1135_, 1);
v_fst_1137_ = lean_ctor_get(v_a_1135_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_a_1135_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1139_ = v_a_1135_;
v_isShared_1140_ = v_isSharedCheck_1173_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_snd_1136_);
lean_inc(v_fst_1137_);
lean_dec(v_a_1135_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1173_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_fst_1141_; lean_object* v_snd_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1172_; 
v_fst_1141_ = lean_ctor_get(v_snd_1136_, 0);
v_snd_1142_ = lean_ctor_get(v_snd_1136_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_snd_1136_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1144_ = v_snd_1136_;
v_isShared_1145_ = v_isSharedCheck_1172_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_snd_1142_);
lean_inc(v_fst_1141_);
lean_dec(v_snd_1136_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1172_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_fst_1146_; lean_object* v_snd_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1171_; 
v_fst_1146_ = lean_ctor_get(v_b_1126_, 0);
v_snd_1147_ = lean_ctor_get(v_b_1126_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_b_1126_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1149_ = v_b_1126_;
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_snd_1147_);
lean_inc(v_fst_1146_);
lean_dec(v_b_1126_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
lean_inc(v_snd_1142_);
lean_inc_ref(v___x_1119_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v_snd_1142_);
lean_ctor_set(v___x_1149_, 0, v___x_1119_);
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_snd_1142_);
v___x_1152_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_snd_1147_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v_env_1154_; lean_object* v_mctx_1155_; lean_object* v_opts_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v_env_1154_ = lean_ctor_get(v_fst_1137_, 0);
lean_inc_ref(v_env_1154_);
v_mctx_1155_ = lean_ctor_get(v_fst_1137_, 1);
lean_inc_ref(v_mctx_1155_);
v_opts_1156_ = lean_ctor_get(v_fst_1137_, 3);
lean_inc_ref(v_opts_1156_);
lean_dec(v_fst_1137_);
v___x_1157_ = lean_box(0);
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_snd_1147_, v___x_1152_, v___x_1157_);
lean_inc(v_snd_1121_);
lean_inc(v_fst_1120_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_snd_1121_);
lean_ctor_set(v___x_1139_, 0, v_fst_1120_);
v___x_1160_ = v___x_1139_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_fst_1120_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_snd_1121_);
v___x_1160_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
lean_inc(v___x_1122_);
v___x_1161_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1122_);
lean_ctor_set(v___x_1161_, 2, v_env_1154_);
lean_ctor_set(v___x_1161_, 3, v_mctx_1155_);
lean_ctor_set(v___x_1161_, 4, v_opts_1156_);
lean_ctor_set(v___x_1161_, 5, v_fst_1141_);
lean_ctor_set(v___x_1161_, 6, v_snd_1142_);
v___x_1162_ = lean_array_push(v_fst_1146_, v___x_1161_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v___x_1158_);
lean_ctor_set(v___x_1144_, 0, v___x_1162_);
v___x_1164_ = v___x_1144_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v___x_1158_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
v_a_1129_ = v___x_1164_;
goto v___jp_1128_;
}
}
}
else
{
lean_object* v___x_1168_; 
lean_dec_ref(v___x_1152_);
lean_dec(v_snd_1142_);
lean_dec(v_fst_1141_);
lean_del_object(v___x_1139_);
lean_dec(v_fst_1137_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_snd_1147_);
lean_ctor_set(v___x_1144_, 0, v_fst_1146_);
v___x_1168_ = v___x_1144_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_fst_1146_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_snd_1147_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v_a_1129_ = v___x_1168_;
goto v___jp_1128_;
}
}
}
}
}
}
}
v___jp_1128_:
{
size_t v___x_1130_; size_t v___x_1131_; 
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_add(v_i_1125_, v___x_1130_);
v_i_1125_ = v___x_1131_;
v_b_1126_ = v_a_1129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg___boxed(lean_object* v___x_1174_, lean_object* v_fst_1175_, lean_object* v_snd_1176_, lean_object* v___x_1177_, lean_object* v_as_1178_, lean_object* v_sz_1179_, lean_object* v_i_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_){
_start:
{
size_t v_sz_boxed_1183_; size_t v_i_boxed_1184_; lean_object* v_res_1185_; 
v_sz_boxed_1183_ = lean_unbox_usize(v_sz_1179_);
lean_dec(v_sz_1179_);
v_i_boxed_1184_ = lean_unbox_usize(v_i_1180_);
lean_dec(v_i_1180_);
v_res_1185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1174_, v_fst_1175_, v_snd_1176_, v___x_1177_, v_as_1178_, v_sz_boxed_1183_, v_i_boxed_1184_, v_b_1181_);
lean_dec_ref(v_as_1178_);
return v_res_1185_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg___closed__4);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
lean_ctor_set(v___x_1190_, 2, v___x_1189_);
lean_ctor_set(v___x_1190_, 3, v___x_1189_);
lean_ctor_set(v___x_1190_, 4, v___x_1188_);
lean_ctor_set(v___x_1190_, 5, v___x_1188_);
lean_ctor_set(v___x_1190_, 6, v___x_1188_);
lean_ctor_set(v___x_1190_, 7, v___x_1188_);
lean_ctor_set(v___x_1190_, 8, v___x_1188_);
lean_ctor_set(v___x_1190_, 9, v___x_1188_);
lean_ctor_set(v___x_1190_, 10, v___x_1188_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(32u);
v___x_1192_ = lean_mk_empty_array_with_capacity(v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3(void){
_start:
{
size_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1194_ = ((size_t)5ULL);
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = lean_unsigned_to_nat(32u);
v___x_1197_ = lean_mk_empty_array_with_capacity(v___x_1196_);
v___x_1198_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__2);
v___x_1199_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1197_);
lean_ctor_set(v___x_1199_, 2, v___x_1195_);
lean_ctor_set(v___x_1199_, 3, v___x_1195_);
lean_ctor_set_usize(v___x_1199_, 4, v___x_1194_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1200_ = lean_box(1);
v___x_1201_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__3);
v___x_1202_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__0);
v___x_1203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1201_);
lean_ctor_set(v___x_1203_, 2, v___x_1200_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(lean_object* v_msgData_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v_env_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_scopes_1211_; lean_object* v___x_1212_; lean_object* v_opts_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1207_ = lean_st_ref_get(v___y_1205_);
v_env_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_env_1208_);
lean_dec(v___x_1207_);
v___x_1209_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1210_ = lean_st_ref_get(v___y_1205_);
v_scopes_1211_ = lean_ctor_get(v___x_1210_, 2);
lean_inc(v_scopes_1211_);
lean_dec(v___x_1210_);
v___x_1212_ = l_List_head_x21___redArg(v___x_1209_, v_scopes_1211_);
lean_dec(v_scopes_1211_);
v_opts_1213_ = lean_ctor_get(v___x_1212_, 1);
lean_inc_ref(v_opts_1213_);
lean_dec(v___x_1212_);
v___x_1214_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__1);
v___x_1215_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___closed__4);
v___x_1216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1216_, 0, v_env_1208_);
lean_ctor_set(v___x_1216_, 1, v___x_1214_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
lean_ctor_set(v___x_1216_, 3, v_opts_1213_);
v___x_1217_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_msgData_1204_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_1219_, v___y_1220_);
lean_dec(v___y_1220_);
return v_res_1222_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1223_; double v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_float_of_nat(v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(lean_object* v_cls_1227_, lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Elab_Command_getRef___redArg(v___y_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1283_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msg_1228_, v___y_1230_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1283_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1283_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v_traceState_1240_; lean_object* v_env_1241_; lean_object* v_messages_1242_; lean_object* v_scopes_1243_; lean_object* v_usedQuotCtxts_1244_; lean_object* v_nextMacroScope_1245_; lean_object* v_maxRecDepth_1246_; lean_object* v_ngen_1247_; lean_object* v_auxDeclNGen_1248_; lean_object* v_infoState_1249_; lean_object* v_snapshotTasks_1250_; lean_object* v_prevLinterStates_1251_; lean_object* v_codeQualityEntryTasks_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1282_; 
v___x_1239_ = lean_st_ref_take(v___y_1230_);
v_traceState_1240_ = lean_ctor_get(v___x_1239_, 9);
v_env_1241_ = lean_ctor_get(v___x_1239_, 0);
v_messages_1242_ = lean_ctor_get(v___x_1239_, 1);
v_scopes_1243_ = lean_ctor_get(v___x_1239_, 2);
v_usedQuotCtxts_1244_ = lean_ctor_get(v___x_1239_, 3);
v_nextMacroScope_1245_ = lean_ctor_get(v___x_1239_, 4);
v_maxRecDepth_1246_ = lean_ctor_get(v___x_1239_, 5);
v_ngen_1247_ = lean_ctor_get(v___x_1239_, 6);
v_auxDeclNGen_1248_ = lean_ctor_get(v___x_1239_, 7);
v_infoState_1249_ = lean_ctor_get(v___x_1239_, 8);
v_snapshotTasks_1250_ = lean_ctor_get(v___x_1239_, 10);
v_prevLinterStates_1251_ = lean_ctor_get(v___x_1239_, 11);
v_codeQualityEntryTasks_1252_ = lean_ctor_get(v___x_1239_, 12);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1254_ = v___x_1239_;
v_isShared_1255_ = v_isSharedCheck_1282_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1252_);
lean_inc(v_prevLinterStates_1251_);
lean_inc(v_snapshotTasks_1250_);
lean_inc(v_traceState_1240_);
lean_inc(v_infoState_1249_);
lean_inc(v_auxDeclNGen_1248_);
lean_inc(v_ngen_1247_);
lean_inc(v_maxRecDepth_1246_);
lean_inc(v_nextMacroScope_1245_);
lean_inc(v_usedQuotCtxts_1244_);
lean_inc(v_scopes_1243_);
lean_inc(v_messages_1242_);
lean_inc(v_env_1241_);
lean_dec(v___x_1239_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1282_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
uint64_t v_tid_1256_; lean_object* v_traces_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1281_; 
v_tid_1256_ = lean_ctor_get_uint64(v_traceState_1240_, sizeof(void*)*1);
v_traces_1257_ = lean_ctor_get(v_traceState_1240_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_traceState_1240_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1259_ = v_traceState_1240_;
v_isShared_1260_ = v_isSharedCheck_1281_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_traces_1257_);
lean_dec(v_traceState_1240_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1281_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; double v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_1264_ = 0;
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_1266_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1266_, 0, v_cls_1227_);
lean_ctor_set(v___x_1266_, 1, v___x_1262_);
lean_ctor_set(v___x_1266_, 2, v___x_1265_);
lean_ctor_set_float(v___x_1266_, sizeof(void*)*3, v___x_1263_);
lean_ctor_set_float(v___x_1266_, sizeof(void*)*3 + 8, v___x_1263_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*3 + 16, v___x_1264_);
v___x_1267_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_1268_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v_a_1235_);
lean_ctor_set(v___x_1268_, 2, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1233_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = l_Lean_PersistentArray_push___redArg(v_traces_1257_, v___x_1269_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1270_);
v___x_1272_ = v___x_1259_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1270_);
lean_ctor_set_uint64(v_reuseFailAlloc_1280_, sizeof(void*)*1, v_tid_1256_);
v___x_1272_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 9, v___x_1272_);
v___x_1274_ = v___x_1254_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_env_1241_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_messages_1242_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_scopes_1243_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_usedQuotCtxts_1244_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_nextMacroScope_1245_);
lean_ctor_set(v_reuseFailAlloc_1279_, 5, v_maxRecDepth_1246_);
lean_ctor_set(v_reuseFailAlloc_1279_, 6, v_ngen_1247_);
lean_ctor_set(v_reuseFailAlloc_1279_, 7, v_auxDeclNGen_1248_);
lean_ctor_set(v_reuseFailAlloc_1279_, 8, v_infoState_1249_);
lean_ctor_set(v_reuseFailAlloc_1279_, 9, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1279_, 10, v_snapshotTasks_1250_);
lean_ctor_set(v_reuseFailAlloc_1279_, 11, v_prevLinterStates_1251_);
lean_ctor_set(v_reuseFailAlloc_1279_, 12, v_codeQualityEntryTasks_1252_);
v___x_1274_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = lean_st_ref_put(v___y_1230_, v___x_1274_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1261_);
v___x_1277_ = v___x_1237_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1261_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_msg_1228_);
lean_dec(v_cls_1227_);
v_a_1284_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1232_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1232_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___boxed(lean_object* v_cls_1292_, lean_object* v_msg_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v_cls_1292_, v_msg_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__2));
v___x_1304_ = l_Lean_Name_append(v___x_1303_, v___x_1302_);
return v___x_1304_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__4));
v___x_1307_ = l_Lean_stringToMessageData(v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__6));
v___x_1310_ = l_Lean_stringToMessageData(v___x_1309_);
return v___x_1310_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__8));
v___x_1313_ = l_Lean_stringToMessageData(v___x_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__10));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(lean_object* v___x_1317_, lean_object* v_val_1318_, lean_object* v_cmd_1319_, uint8_t v_onUnsolved_1320_, uint8_t v___y_1321_, lean_object* v_as_1322_, size_t v_sz_1323_, size_t v_i_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_usize_dec_lt(v_i_1324_, v_sz_1323_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_dec(v_cmd_1319_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_b_1325_);
return v___x_1330_;
}
else
{
lean_object* v_snd_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1479_; 
v_snd_1331_ = lean_ctor_get(v_b_1325_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_b_1325_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_b_1325_, 0);
lean_dec(v_unused_1480_);
v___x_1333_ = v_b_1325_;
v_isShared_1334_ = v_isSharedCheck_1479_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_snd_1331_);
lean_dec(v_b_1325_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1479_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_fst_1335_; lean_object* v_snd_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1478_; 
v_fst_1335_ = lean_ctor_get(v_snd_1331_, 0);
v_snd_1336_ = lean_ctor_get(v_snd_1331_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_snd_1331_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1338_ = v_snd_1331_;
v_isShared_1339_ = v_isSharedCheck_1478_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_snd_1336_);
lean_inc(v_fst_1335_);
lean_dec(v_snd_1331_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1478_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_a_1340_; lean_object* v_pos_1341_; lean_object* v_endPos_1342_; uint8_t v_severity_1343_; lean_object* v_data_1344_; lean_object* v___x_1345_; lean_object* v_a_1347_; 
v_a_1340_ = lean_array_uget_borrowed(v_as_1322_, v_i_1324_);
v_pos_1341_ = lean_ctor_get(v_a_1340_, 1);
v_endPos_1342_ = lean_ctor_get(v_a_1340_, 2);
lean_inc(v_endPos_1342_);
v_severity_1343_ = lean_ctor_get_uint8(v_a_1340_, sizeof(void*)*5 + 1);
v_data_1344_ = lean_ctor_get(v_a_1340_, 4);
v___x_1345_ = lean_box(0);
if (v_severity_1343_ == 2)
{
lean_object* v___f_1360_; uint8_t v___x_1361_; 
v___f_1360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1344_);
v___x_1361_ = l_Lean_MessageData_hasTag(v___f_1360_, v_data_1344_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec(v_endPos_1342_);
lean_del_object(v___x_1333_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_fst_1335_);
lean_ctor_set(v___x_1362_, 1, v_snd_1336_);
v_a_1347_ = v___x_1362_;
goto v___jp_1346_;
}
else
{
if (lean_obj_tag(v_endPos_1342_) == 1)
{
lean_object* v_val_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1475_; 
v_val_1363_ = lean_ctor_get(v_endPos_1342_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_endPos_1342_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1365_ = v_endPos_1342_;
v_isShared_1366_ = v_isSharedCheck_1475_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_val_1363_);
lean_dec(v_endPos_1342_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1475_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; uint8_t v___x_1371_; 
lean_inc_ref(v_pos_1341_);
v___x_1367_ = l_Lean_FileMap_ofPosition(v___x_1317_, v_pos_1341_);
v___x_1368_ = l_Lean_FileMap_ofPosition(v___x_1317_, v_val_1363_);
lean_inc(v___x_1368_);
lean_inc(v___x_1367_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = 0;
v___x_1371_ = l_Lean_Syntax_Range_includes(v_val_1318_, v___x_1369_, v___x_1370_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref_known(v___x_1369_, 2);
lean_dec(v___x_1368_);
lean_dec(v___x_1367_);
lean_del_object(v___x_1365_);
lean_del_object(v___x_1333_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_fst_1335_);
lean_ctor_set(v___x_1372_, 1, v_snd_1336_);
v_a_1347_ = v___x_1372_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1373_; 
lean_inc(v_cmd_1319_);
lean_inc_ref(v___x_1369_);
v___x_1373_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1369_, v_cmd_1319_);
if (lean_obj_tag(v___x_1373_) == 1)
{
lean_object* v_val_1374_; lean_object* v_fst_1375_; lean_object* v_snd_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v___x_1368_);
lean_dec(v___x_1367_);
lean_del_object(v___x_1365_);
v_val_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v_fst_1375_ = lean_ctor_get(v_val_1374_, 0);
v_snd_1376_ = lean_ctor_get(v_val_1374_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_val_1374_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1378_ = v_val_1374_;
v_isShared_1379_ = v_isSharedCheck_1439_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_snd_1376_);
lean_inc(v_fst_1375_);
lean_dec(v_val_1374_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1439_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; uint8_t v___y_1437_; lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Syntax_getPos_x3f(v_fst_1375_, v___x_1370_);
if (lean_obj_tag(v___x_1438_) == 0)
{
v___y_1437_ = v___x_1371_;
goto v___jp_1436_;
}
else
{
lean_dec_ref_known(v___x_1438_, 1);
v___y_1437_ = v___x_1370_;
goto v___jp_1436_;
}
v___jp_1380_:
{
lean_object* v___x_1386_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v_snd_1336_);
lean_ctor_set(v___x_1378_, 0, v_fst_1335_);
v___x_1386_ = v___x_1378_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_fst_1335_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_snd_1336_);
v___x_1386_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v_sz_1387_ = lean_array_size(v___y_1382_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1369_, v_fst_1375_, v_snd_1376_, v___y_1381_, v___y_1382_, v_sz_1387_, v___x_1388_, v___x_1386_);
lean_dec_ref(v___y_1382_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v_fst_1391_ = lean_ctor_get(v_a_1390_, 0);
v_snd_1392_ = lean_ctor_get(v_a_1390_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_a_1390_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v_a_1390_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_snd_1392_);
lean_inc(v_fst_1391_);
lean_dec(v_a_1390_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_fst_1391_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_snd_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
v_a_1347_ = v___x_1397_;
goto v___jp_1346_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_del_object(v___x_1338_);
lean_dec(v_cmd_1319_);
v_a_1400_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1389_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1389_);
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
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
v___jp_1409_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
lean_inc_ref(v___x_1369_);
v___x_1410_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1369_);
v___x_1411_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1344_);
v___x_1412_ = lean_array_get_size(v___x_1411_);
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = lean_nat_dec_eq(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
v___y_1381_ = v___x_1410_;
v___y_1382_ = v___x_1411_;
v___y_1383_ = v___y_1326_;
v___y_1384_ = v___y_1327_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v_scopes_1420_; lean_object* v___x_1421_; lean_object* v_opts_1422_; uint8_t v_hasTrace_1423_; 
v___x_1415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1416_ = l_Lean_inheritedTraceOptions;
v___x_1417_ = lean_st_ref_get(v___x_1416_);
v___x_1418_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1419_ = lean_st_ref_get(v___y_1327_);
v_scopes_1420_ = lean_ctor_get(v___x_1419_, 2);
lean_inc(v_scopes_1420_);
lean_dec(v___x_1419_);
v___x_1421_ = l_List_head_x21___redArg(v___x_1418_, v_scopes_1420_);
lean_dec(v_scopes_1420_);
v_opts_1422_ = lean_ctor_get(v___x_1421_, 1);
lean_inc_ref(v_opts_1422_);
lean_dec(v___x_1421_);
v_hasTrace_1423_ = lean_ctor_get_uint8(v_opts_1422_, sizeof(void*)*1);
if (v_hasTrace_1423_ == 0)
{
lean_dec_ref(v_opts_1422_);
lean_dec(v___x_1417_);
v___y_1381_ = v___x_1410_;
v___y_1382_ = v___x_1411_;
v___y_1383_ = v___y_1326_;
v___y_1384_ = v___y_1327_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1425_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1417_, v_opts_1422_, v___x_1424_);
lean_dec_ref(v_opts_1422_);
lean_dec(v___x_1417_);
if (v___x_1425_ == 0)
{
v___y_1381_ = v___x_1410_;
v___y_1382_ = v___x_1411_;
v___y_1383_ = v___y_1326_;
v___y_1384_ = v___y_1327_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1427_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1415_, v___x_1426_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_dec_ref_known(v___x_1427_, 1);
v___y_1381_ = v___x_1410_;
v___y_1382_ = v___x_1411_;
v___y_1383_ = v___y_1326_;
v___y_1384_ = v___y_1327_;
goto v___jp_1380_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v___x_1411_);
lean_dec(v___x_1410_);
lean_del_object(v___x_1378_);
lean_dec(v_snd_1376_);
lean_dec(v_fst_1375_);
lean_dec_ref_known(v___x_1369_, 2);
lean_del_object(v___x_1338_);
lean_dec(v_snd_1336_);
lean_dec(v_fst_1335_);
lean_dec(v_cmd_1319_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
}
}
v___jp_1436_:
{
if (v_onUnsolved_1320_ == 0)
{
if (v___y_1321_ == 0)
{
lean_del_object(v___x_1378_);
lean_dec(v_snd_1376_);
lean_dec(v_fst_1375_);
lean_dec_ref_known(v___x_1369_, 2);
goto v___jp_1354_;
}
else
{
if (v___y_1437_ == 0)
{
lean_del_object(v___x_1378_);
lean_dec(v_snd_1376_);
lean_dec(v_fst_1375_);
lean_dec_ref_known(v___x_1369_, 2);
goto v___jp_1354_;
}
else
{
lean_del_object(v___x_1333_);
goto v___jp_1409_;
}
}
}
else
{
lean_del_object(v___x_1333_);
goto v___jp_1409_;
}
}
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v_scopes_1445_; lean_object* v___x_1446_; lean_object* v_opts_1447_; uint8_t v_hasTrace_1448_; 
lean_dec(v___x_1373_);
lean_dec_ref_known(v___x_1369_, 2);
lean_del_object(v___x_1333_);
v___x_1440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1441_ = l_Lean_inheritedTraceOptions;
v___x_1442_ = lean_st_ref_get(v___x_1441_);
v___x_1443_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1444_ = lean_st_ref_get(v___y_1327_);
v_scopes_1445_ = lean_ctor_get(v___x_1444_, 2);
lean_inc(v_scopes_1445_);
lean_dec(v___x_1444_);
v___x_1446_ = l_List_head_x21___redArg(v___x_1443_, v_scopes_1445_);
lean_dec(v_scopes_1445_);
v_opts_1447_ = lean_ctor_get(v___x_1446_, 1);
lean_inc_ref(v_opts_1447_);
lean_dec(v___x_1446_);
v_hasTrace_1448_ = lean_ctor_get_uint8(v_opts_1447_, sizeof(void*)*1);
if (v_hasTrace_1448_ == 0)
{
lean_dec_ref(v_opts_1447_);
lean_dec(v___x_1442_);
lean_dec(v___x_1368_);
lean_dec(v___x_1367_);
lean_del_object(v___x_1365_);
goto v___jp_1358_;
}
else
{
lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1450_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1442_, v_opts_1447_, v___x_1449_);
lean_dec_ref(v_opts_1447_);
lean_dec(v___x_1442_);
if (v___x_1450_ == 0)
{
lean_dec(v___x_1368_);
lean_dec(v___x_1367_);
lean_del_object(v___x_1365_);
goto v___jp_1358_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1451_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1452_ = l_Nat_reprFast(v___x_1367_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set_tag(v___x_1365_, 3);
lean_ctor_set(v___x_1365_, 0, v___x_1452_);
v___x_1454_ = v___x_1365_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1455_ = l_Lean_MessageData_ofFormat(v___x_1454_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1451_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Nat_reprFast(v___x_1368_);
v___x_1460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = l_Lean_MessageData_ofFormat(v___x_1460_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1458_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1440_, v___x_1464_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_dec_ref_known(v___x_1465_, 1);
goto v___jp_1358_;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_del_object(v___x_1338_);
lean_dec(v_snd_1336_);
lean_dec(v_fst_1335_);
lean_dec(v_cmd_1319_);
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
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
lean_object* v___x_1476_; 
lean_dec(v_endPos_1342_);
lean_del_object(v___x_1333_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_fst_1335_);
lean_ctor_set(v___x_1476_, 1, v_snd_1336_);
v_a_1347_ = v___x_1476_;
goto v___jp_1346_;
}
}
}
else
{
lean_object* v___x_1477_; 
lean_dec(v_endPos_1342_);
lean_del_object(v___x_1333_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_fst_1335_);
lean_ctor_set(v___x_1477_, 1, v_snd_1336_);
v_a_1347_ = v___x_1477_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___x_1349_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_a_1347_);
lean_ctor_set(v___x_1338_, 0, v___x_1345_);
v___x_1349_ = v___x_1338_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_a_1347_);
v___x_1349_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
size_t v___x_1350_; size_t v___x_1351_; 
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_add(v_i_1324_, v___x_1350_);
v_i_1324_ = v___x_1351_;
v_b_1325_ = v___x_1349_;
goto _start;
}
}
v___jp_1354_:
{
lean_object* v___x_1356_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v_snd_1336_);
lean_ctor_set(v___x_1333_, 0, v_fst_1335_);
v___x_1356_ = v___x_1333_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_fst_1335_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_snd_1336_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
v_a_1347_ = v___x_1356_;
goto v___jp_1346_;
}
}
v___jp_1358_:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_fst_1335_);
lean_ctor_set(v___x_1359_, 1, v_snd_1336_);
v_a_1347_ = v___x_1359_;
goto v___jp_1346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___boxed(lean_object* v___x_1481_, lean_object* v_val_1482_, lean_object* v_cmd_1483_, lean_object* v_onUnsolved_1484_, lean_object* v___y_1485_, lean_object* v_as_1486_, lean_object* v_sz_1487_, lean_object* v_i_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v_onUnsolved_boxed_1493_; uint8_t v___y_11992__boxed_1494_; size_t v_sz_boxed_1495_; size_t v_i_boxed_1496_; lean_object* v_res_1497_; 
v_onUnsolved_boxed_1493_ = lean_unbox(v_onUnsolved_1484_);
v___y_11992__boxed_1494_ = lean_unbox(v___y_1485_);
v_sz_boxed_1495_ = lean_unbox_usize(v_sz_1487_);
lean_dec(v_sz_1487_);
v_i_boxed_1496_ = lean_unbox_usize(v_i_1488_);
lean_dec(v_i_1488_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1481_, v_val_1482_, v_cmd_1483_, v_onUnsolved_boxed_1493_, v___y_11992__boxed_1494_, v_as_1486_, v_sz_boxed_1495_, v_i_boxed_1496_, v_b_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec_ref(v_as_1486_);
lean_dec_ref(v_val_1482_);
lean_dec_ref(v___x_1481_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(lean_object* v___x_1498_, lean_object* v_val_1499_, lean_object* v_cmd_1500_, uint8_t v_onUnsolved_1501_, uint8_t v___y_1502_, lean_object* v_as_1503_, size_t v_sz_1504_, size_t v_i_1505_, lean_object* v_b_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_usize_dec_lt(v_i_1505_, v_sz_1504_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_dec(v_cmd_1500_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_b_1506_);
return v___x_1511_;
}
else
{
lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1660_; 
v_snd_1512_ = lean_ctor_get(v_b_1506_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_b_1506_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_b_1506_, 0);
lean_dec(v_unused_1661_);
v___x_1514_ = v_b_1506_;
v_isShared_1515_ = v_isSharedCheck_1660_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_dec(v_b_1506_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1660_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1659_; 
v_fst_1516_ = lean_ctor_get(v_snd_1512_, 0);
v_snd_1517_ = lean_ctor_get(v_snd_1512_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_snd_1512_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1519_ = v_snd_1512_;
v_isShared_1520_ = v_isSharedCheck_1659_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1517_);
lean_inc(v_fst_1516_);
lean_dec(v_snd_1512_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1659_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_a_1521_; lean_object* v_pos_1522_; lean_object* v_endPos_1523_; uint8_t v_severity_1524_; lean_object* v_data_1525_; lean_object* v___x_1526_; lean_object* v_a_1528_; 
v_a_1521_ = lean_array_uget_borrowed(v_as_1503_, v_i_1505_);
v_pos_1522_ = lean_ctor_get(v_a_1521_, 1);
v_endPos_1523_ = lean_ctor_get(v_a_1521_, 2);
lean_inc(v_endPos_1523_);
v_severity_1524_ = lean_ctor_get_uint8(v_a_1521_, sizeof(void*)*5 + 1);
v_data_1525_ = lean_ctor_get(v_a_1521_, 4);
v___x_1526_ = lean_box(0);
if (v_severity_1524_ == 2)
{
lean_object* v___f_1541_; uint8_t v___x_1542_; 
v___f_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1525_);
v___x_1542_ = l_Lean_MessageData_hasTag(v___f_1541_, v_data_1525_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_dec(v_endPos_1523_);
lean_del_object(v___x_1514_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_fst_1516_);
lean_ctor_set(v___x_1543_, 1, v_snd_1517_);
v_a_1528_ = v___x_1543_;
goto v___jp_1527_;
}
else
{
if (lean_obj_tag(v_endPos_1523_) == 1)
{
lean_object* v_val_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1656_; 
v_val_1544_ = lean_ctor_get(v_endPos_1523_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_endPos_1523_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1546_ = v_endPos_1523_;
v_isShared_1547_ = v_isSharedCheck_1656_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_val_1544_);
lean_dec(v_endPos_1523_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1656_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; uint8_t v___x_1552_; 
lean_inc_ref(v_pos_1522_);
v___x_1548_ = l_Lean_FileMap_ofPosition(v___x_1498_, v_pos_1522_);
v___x_1549_ = l_Lean_FileMap_ofPosition(v___x_1498_, v_val_1544_);
lean_inc(v___x_1549_);
lean_inc(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = 0;
v___x_1552_ = l_Lean_Syntax_Range_includes(v_val_1499_, v___x_1550_, v___x_1551_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref_known(v___x_1550_, 2);
lean_dec(v___x_1549_);
lean_dec(v___x_1548_);
lean_del_object(v___x_1546_);
lean_del_object(v___x_1514_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_fst_1516_);
lean_ctor_set(v___x_1553_, 1, v_snd_1517_);
v_a_1528_ = v___x_1553_;
goto v___jp_1527_;
}
else
{
lean_object* v___x_1554_; 
lean_inc(v_cmd_1500_);
lean_inc_ref(v___x_1550_);
v___x_1554_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1550_, v_cmd_1500_);
if (lean_obj_tag(v___x_1554_) == 1)
{
lean_object* v_val_1555_; lean_object* v_fst_1556_; lean_object* v_snd_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v___x_1549_);
lean_dec(v___x_1548_);
lean_del_object(v___x_1546_);
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v_fst_1556_ = lean_ctor_get(v_val_1555_, 0);
v_snd_1557_ = lean_ctor_get(v_val_1555_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_val_1555_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1559_ = v_val_1555_;
v_isShared_1560_ = v_isSharedCheck_1620_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_snd_1557_);
lean_inc(v_fst_1556_);
lean_dec(v_val_1555_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1620_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; uint8_t v___y_1618_; lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Syntax_getPos_x3f(v_fst_1556_, v___x_1551_);
if (lean_obj_tag(v___x_1619_) == 0)
{
v___y_1618_ = v___x_1552_;
goto v___jp_1617_;
}
else
{
lean_dec_ref_known(v___x_1619_, 1);
v___y_1618_ = v___x_1551_;
goto v___jp_1617_;
}
v___jp_1561_:
{
lean_object* v___x_1567_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v_snd_1517_);
lean_ctor_set(v___x_1559_, 0, v_fst_1516_);
v___x_1567_ = v___x_1559_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_fst_1516_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_snd_1517_);
v___x_1567_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
size_t v_sz_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v_sz_1568_ = lean_array_size(v___y_1563_);
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1550_, v_fst_1556_, v_snd_1557_, v___y_1562_, v___y_1563_, v_sz_1568_, v___x_1569_, v___x_1567_);
lean_dec_ref(v___y_1563_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v_fst_1572_; lean_object* v_snd_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v_fst_1572_ = lean_ctor_get(v_a_1571_, 0);
v_snd_1573_ = lean_ctor_get(v_a_1571_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_a_1571_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v_a_1571_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_snd_1573_);
lean_inc(v_fst_1572_);
lean_dec(v_a_1571_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_fst_1572_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_snd_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v_a_1528_ = v___x_1578_;
goto v___jp_1527_;
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_del_object(v___x_1519_);
lean_dec(v_cmd_1500_);
v_a_1581_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1570_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1570_);
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
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
v___jp_1590_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
lean_inc_ref(v___x_1550_);
v___x_1591_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1550_);
v___x_1592_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1525_);
v___x_1593_ = lean_array_get_size(v___x_1592_);
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_nat_dec_eq(v___x_1593_, v___x_1594_);
if (v___x_1595_ == 0)
{
v___y_1562_ = v___x_1591_;
v___y_1563_ = v___x_1592_;
v___y_1564_ = v___y_1507_;
v___y_1565_ = v___y_1508_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_scopes_1601_; lean_object* v___x_1602_; lean_object* v_opts_1603_; uint8_t v_hasTrace_1604_; 
v___x_1596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1597_ = l_Lean_inheritedTraceOptions;
v___x_1598_ = lean_st_ref_get(v___x_1597_);
v___x_1599_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1600_ = lean_st_ref_get(v___y_1508_);
v_scopes_1601_ = lean_ctor_get(v___x_1600_, 2);
lean_inc(v_scopes_1601_);
lean_dec(v___x_1600_);
v___x_1602_ = l_List_head_x21___redArg(v___x_1599_, v_scopes_1601_);
lean_dec(v_scopes_1601_);
v_opts_1603_ = lean_ctor_get(v___x_1602_, 1);
lean_inc_ref(v_opts_1603_);
lean_dec(v___x_1602_);
v_hasTrace_1604_ = lean_ctor_get_uint8(v_opts_1603_, sizeof(void*)*1);
if (v_hasTrace_1604_ == 0)
{
lean_dec_ref(v_opts_1603_);
lean_dec(v___x_1598_);
v___y_1562_ = v___x_1591_;
v___y_1563_ = v___x_1592_;
v___y_1564_ = v___y_1507_;
v___y_1565_ = v___y_1508_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1606_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1598_, v_opts_1603_, v___x_1605_);
lean_dec_ref(v_opts_1603_);
lean_dec(v___x_1598_);
if (v___x_1606_ == 0)
{
v___y_1562_ = v___x_1591_;
v___y_1563_ = v___x_1592_;
v___y_1564_ = v___y_1507_;
v___y_1565_ = v___y_1508_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1608_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1596_, v___x_1607_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_dec_ref_known(v___x_1608_, 1);
v___y_1562_ = v___x_1591_;
v___y_1563_ = v___x_1592_;
v___y_1564_ = v___y_1507_;
v___y_1565_ = v___y_1508_;
goto v___jp_1561_;
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec_ref(v___x_1592_);
lean_dec(v___x_1591_);
lean_del_object(v___x_1559_);
lean_dec(v_snd_1557_);
lean_dec(v_fst_1556_);
lean_dec_ref_known(v___x_1550_, 2);
lean_del_object(v___x_1519_);
lean_dec(v_snd_1517_);
lean_dec(v_fst_1516_);
lean_dec(v_cmd_1500_);
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
}
}
v___jp_1617_:
{
if (v_onUnsolved_1501_ == 0)
{
if (v___y_1502_ == 0)
{
lean_del_object(v___x_1559_);
lean_dec(v_snd_1557_);
lean_dec(v_fst_1556_);
lean_dec_ref_known(v___x_1550_, 2);
goto v___jp_1535_;
}
else
{
if (v___y_1618_ == 0)
{
lean_del_object(v___x_1559_);
lean_dec(v_snd_1557_);
lean_dec(v_fst_1556_);
lean_dec_ref_known(v___x_1550_, 2);
goto v___jp_1535_;
}
else
{
lean_del_object(v___x_1514_);
goto v___jp_1590_;
}
}
}
else
{
lean_del_object(v___x_1514_);
goto v___jp_1590_;
}
}
}
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_scopes_1626_; lean_object* v___x_1627_; lean_object* v_opts_1628_; uint8_t v_hasTrace_1629_; 
lean_dec(v___x_1554_);
lean_dec_ref_known(v___x_1550_, 2);
lean_del_object(v___x_1514_);
v___x_1621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1622_ = l_Lean_inheritedTraceOptions;
v___x_1623_ = lean_st_ref_get(v___x_1622_);
v___x_1624_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1625_ = lean_st_ref_get(v___y_1508_);
v_scopes_1626_ = lean_ctor_get(v___x_1625_, 2);
lean_inc(v_scopes_1626_);
lean_dec(v___x_1625_);
v___x_1627_ = l_List_head_x21___redArg(v___x_1624_, v_scopes_1626_);
lean_dec(v_scopes_1626_);
v_opts_1628_ = lean_ctor_get(v___x_1627_, 1);
lean_inc_ref(v_opts_1628_);
lean_dec(v___x_1627_);
v_hasTrace_1629_ = lean_ctor_get_uint8(v_opts_1628_, sizeof(void*)*1);
if (v_hasTrace_1629_ == 0)
{
lean_dec_ref(v_opts_1628_);
lean_dec(v___x_1623_);
lean_dec(v___x_1549_);
lean_dec(v___x_1548_);
lean_del_object(v___x_1546_);
goto v___jp_1539_;
}
else
{
lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1623_, v_opts_1628_, v___x_1630_);
lean_dec_ref(v_opts_1628_);
lean_dec(v___x_1623_);
if (v___x_1631_ == 0)
{
lean_dec(v___x_1549_);
lean_dec(v___x_1548_);
lean_del_object(v___x_1546_);
goto v___jp_1539_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1632_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1633_ = l_Nat_reprFast(v___x_1548_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 3);
lean_ctor_set(v___x_1546_, 0, v___x_1633_);
v___x_1635_ = v___x_1546_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1636_ = l_Lean_MessageData_ofFormat(v___x_1635_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1632_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Nat_reprFast(v___x_1549_);
v___x_1641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
v___x_1642_ = l_Lean_MessageData_ofFormat(v___x_1641_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1639_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1621_, v___x_1645_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec_ref_known(v___x_1646_, 1);
goto v___jp_1539_;
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_del_object(v___x_1519_);
lean_dec(v_snd_1517_);
lean_dec(v_fst_1516_);
lean_dec(v_cmd_1500_);
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
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
lean_object* v___x_1657_; 
lean_dec(v_endPos_1523_);
lean_del_object(v___x_1514_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v_fst_1516_);
lean_ctor_set(v___x_1657_, 1, v_snd_1517_);
v_a_1528_ = v___x_1657_;
goto v___jp_1527_;
}
}
}
else
{
lean_object* v___x_1658_; 
lean_dec(v_endPos_1523_);
lean_del_object(v___x_1514_);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v_fst_1516_);
lean_ctor_set(v___x_1658_, 1, v_snd_1517_);
v_a_1528_ = v___x_1658_;
goto v___jp_1527_;
}
v___jp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 1, v_a_1528_);
lean_ctor_set(v___x_1519_, 0, v___x_1526_);
v___x_1530_ = v___x_1519_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_a_1528_);
v___x_1530_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1505_, v___x_1531_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13(v___x_1498_, v_val_1499_, v_cmd_1500_, v_onUnsolved_1501_, v___y_1502_, v_as_1503_, v_sz_1504_, v___x_1532_, v___x_1530_, v___y_1507_, v___y_1508_);
return v___x_1533_;
}
}
v___jp_1535_:
{
lean_object* v___x_1537_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_snd_1517_);
lean_ctor_set(v___x_1514_, 0, v_fst_1516_);
v___x_1537_ = v___x_1514_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_fst_1516_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_snd_1517_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
v_a_1528_ = v___x_1537_;
goto v___jp_1527_;
}
}
v___jp_1539_:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_fst_1516_);
lean_ctor_set(v___x_1540_, 1, v_snd_1517_);
v_a_1528_ = v___x_1540_;
goto v___jp_1527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9___boxed(lean_object* v___x_1662_, lean_object* v_val_1663_, lean_object* v_cmd_1664_, lean_object* v_onUnsolved_1665_, lean_object* v___y_1666_, lean_object* v_as_1667_, lean_object* v_sz_1668_, lean_object* v_i_1669_, lean_object* v_b_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
uint8_t v_onUnsolved_boxed_1674_; uint8_t v___y_12333__boxed_1675_; size_t v_sz_boxed_1676_; size_t v_i_boxed_1677_; lean_object* v_res_1678_; 
v_onUnsolved_boxed_1674_ = lean_unbox(v_onUnsolved_1665_);
v___y_12333__boxed_1675_ = lean_unbox(v___y_1666_);
v_sz_boxed_1676_ = lean_unbox_usize(v_sz_1668_);
lean_dec(v_sz_1668_);
v_i_boxed_1677_ = lean_unbox_usize(v_i_1669_);
lean_dec(v_i_1669_);
v_res_1678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_1662_, v_val_1663_, v_cmd_1664_, v_onUnsolved_boxed_1674_, v___y_12333__boxed_1675_, v_as_1667_, v_sz_boxed_1676_, v_i_boxed_1677_, v_b_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v_as_1667_);
lean_dec_ref(v_val_1663_);
lean_dec_ref(v___x_1662_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(lean_object* v___x_1679_, lean_object* v_val_1680_, lean_object* v_cmd_1681_, uint8_t v_onUnsolved_1682_, uint8_t v___y_1683_, lean_object* v_as_1684_, size_t v_sz_1685_, size_t v_i_1686_, lean_object* v_b_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_usize_dec_lt(v_i_1686_, v_sz_1685_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_dec(v_cmd_1681_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_b_1687_);
return v___x_1692_;
}
else
{
lean_object* v_snd_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1841_; 
v_snd_1693_ = lean_ctor_get(v_b_1687_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_b_1687_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v_b_1687_, 0);
lean_dec(v_unused_1842_);
v___x_1695_ = v_b_1687_;
v_isShared_1696_ = v_isSharedCheck_1841_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_snd_1693_);
lean_dec(v_b_1687_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1841_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_fst_1697_; lean_object* v_snd_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1840_; 
v_fst_1697_ = lean_ctor_get(v_snd_1693_, 0);
v_snd_1698_ = lean_ctor_get(v_snd_1693_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_snd_1693_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1700_ = v_snd_1693_;
v_isShared_1701_ = v_isSharedCheck_1840_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snd_1698_);
lean_inc(v_fst_1697_);
lean_dec(v_snd_1693_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1840_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_a_1702_; lean_object* v_pos_1703_; lean_object* v_endPos_1704_; uint8_t v_severity_1705_; lean_object* v_data_1706_; lean_object* v___x_1707_; lean_object* v_a_1709_; 
v_a_1702_ = lean_array_uget_borrowed(v_as_1684_, v_i_1686_);
v_pos_1703_ = lean_ctor_get(v_a_1702_, 1);
v_endPos_1704_ = lean_ctor_get(v_a_1702_, 2);
lean_inc(v_endPos_1704_);
v_severity_1705_ = lean_ctor_get_uint8(v_a_1702_, sizeof(void*)*5 + 1);
v_data_1706_ = lean_ctor_get(v_a_1702_, 4);
v___x_1707_ = lean_box(0);
if (v_severity_1705_ == 2)
{
lean_object* v___f_1722_; uint8_t v___x_1723_; 
v___f_1722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1706_);
v___x_1723_ = l_Lean_MessageData_hasTag(v___f_1722_, v_data_1706_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_dec(v_endPos_1704_);
lean_del_object(v___x_1695_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_fst_1697_);
lean_ctor_set(v___x_1724_, 1, v_snd_1698_);
v_a_1709_ = v___x_1724_;
goto v___jp_1708_;
}
else
{
if (lean_obj_tag(v_endPos_1704_) == 1)
{
lean_object* v_val_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1837_; 
v_val_1725_ = lean_ctor_get(v_endPos_1704_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_endPos_1704_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1727_ = v_endPos_1704_;
v_isShared_1728_ = v_isSharedCheck_1837_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_val_1725_);
lean_dec(v_endPos_1704_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1837_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; uint8_t v___x_1733_; 
lean_inc_ref(v_pos_1703_);
v___x_1729_ = l_Lean_FileMap_ofPosition(v___x_1679_, v_pos_1703_);
v___x_1730_ = l_Lean_FileMap_ofPosition(v___x_1679_, v_val_1725_);
lean_inc(v___x_1730_);
lean_inc(v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = 0;
v___x_1733_ = l_Lean_Syntax_Range_includes(v_val_1680_, v___x_1731_, v___x_1732_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec_ref_known(v___x_1731_, 2);
lean_dec(v___x_1730_);
lean_dec(v___x_1729_);
lean_del_object(v___x_1727_);
lean_del_object(v___x_1695_);
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v_fst_1697_);
lean_ctor_set(v___x_1734_, 1, v_snd_1698_);
v_a_1709_ = v___x_1734_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1735_; 
lean_inc(v_cmd_1681_);
lean_inc_ref(v___x_1731_);
v___x_1735_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1731_, v_cmd_1681_);
if (lean_obj_tag(v___x_1735_) == 1)
{
lean_object* v_val_1736_; lean_object* v_fst_1737_; lean_object* v_snd_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v___x_1730_);
lean_dec(v___x_1729_);
lean_del_object(v___x_1727_);
v_val_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_val_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v_fst_1737_ = lean_ctor_get(v_val_1736_, 0);
v_snd_1738_ = lean_ctor_get(v_val_1736_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_val_1736_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1740_ = v_val_1736_;
v_isShared_1741_ = v_isSharedCheck_1801_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_snd_1738_);
lean_inc(v_fst_1737_);
lean_dec(v_val_1736_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1801_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; uint8_t v___y_1799_; lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Syntax_getPos_x3f(v_fst_1737_, v___x_1732_);
if (lean_obj_tag(v___x_1800_) == 0)
{
v___y_1799_ = v___x_1733_;
goto v___jp_1798_;
}
else
{
lean_dec_ref_known(v___x_1800_, 1);
v___y_1799_ = v___x_1732_;
goto v___jp_1798_;
}
v___jp_1742_:
{
lean_object* v___x_1748_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v_snd_1698_);
lean_ctor_set(v___x_1740_, 0, v_fst_1697_);
v___x_1748_ = v___x_1740_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_fst_1697_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_snd_1698_);
v___x_1748_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
size_t v_sz_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v_sz_1749_ = lean_array_size(v___y_1744_);
v___x_1750_ = ((size_t)0ULL);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1731_, v_fst_1737_, v_snd_1738_, v___y_1743_, v___y_1744_, v_sz_1749_, v___x_1750_, v___x_1748_);
lean_dec_ref(v___y_1744_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v_fst_1753_ = lean_ctor_get(v_a_1752_, 0);
v_snd_1754_ = lean_ctor_get(v_a_1752_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_a_1752_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v_a_1752_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_inc(v_fst_1753_);
lean_dec(v_a_1752_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_fst_1753_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_snd_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
v_a_1709_ = v___x_1759_;
goto v___jp_1708_;
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_del_object(v___x_1700_);
lean_dec(v_cmd_1681_);
v_a_1762_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1751_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1751_);
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
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
v___jp_1771_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
lean_inc_ref(v___x_1731_);
v___x_1772_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1731_);
v___x_1773_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1706_);
v___x_1774_ = lean_array_get_size(v___x_1773_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_nat_dec_eq(v___x_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
v___y_1743_ = v___x_1772_;
v___y_1744_ = v___x_1773_;
v___y_1745_ = v___y_1688_;
v___y_1746_ = v___y_1689_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_scopes_1782_; lean_object* v___x_1783_; lean_object* v_opts_1784_; uint8_t v_hasTrace_1785_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1778_ = l_Lean_inheritedTraceOptions;
v___x_1779_ = lean_st_ref_get(v___x_1778_);
v___x_1780_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1781_ = lean_st_ref_get(v___y_1689_);
v_scopes_1782_ = lean_ctor_get(v___x_1781_, 2);
lean_inc(v_scopes_1782_);
lean_dec(v___x_1781_);
v___x_1783_ = l_List_head_x21___redArg(v___x_1780_, v_scopes_1782_);
lean_dec(v_scopes_1782_);
v_opts_1784_ = lean_ctor_get(v___x_1783_, 1);
lean_inc_ref(v_opts_1784_);
lean_dec(v___x_1783_);
v_hasTrace_1785_ = lean_ctor_get_uint8(v_opts_1784_, sizeof(void*)*1);
if (v_hasTrace_1785_ == 0)
{
lean_dec_ref(v_opts_1784_);
lean_dec(v___x_1779_);
v___y_1743_ = v___x_1772_;
v___y_1744_ = v___x_1773_;
v___y_1745_ = v___y_1688_;
v___y_1746_ = v___y_1689_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1787_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1779_, v_opts_1784_, v___x_1786_);
lean_dec_ref(v_opts_1784_);
lean_dec(v___x_1779_);
if (v___x_1787_ == 0)
{
v___y_1743_ = v___x_1772_;
v___y_1744_ = v___x_1773_;
v___y_1745_ = v___y_1688_;
v___y_1746_ = v___y_1689_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1789_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1777_, v___x_1788_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_dec_ref_known(v___x_1789_, 1);
v___y_1743_ = v___x_1772_;
v___y_1744_ = v___x_1773_;
v___y_1745_ = v___y_1688_;
v___y_1746_ = v___y_1689_;
goto v___jp_1742_;
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v___x_1773_);
lean_dec(v___x_1772_);
lean_del_object(v___x_1740_);
lean_dec(v_snd_1738_);
lean_dec(v_fst_1737_);
lean_dec_ref_known(v___x_1731_, 2);
lean_del_object(v___x_1700_);
lean_dec(v_snd_1698_);
lean_dec(v_fst_1697_);
lean_dec(v_cmd_1681_);
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
}
v___jp_1798_:
{
if (v_onUnsolved_1682_ == 0)
{
if (v___y_1683_ == 0)
{
lean_del_object(v___x_1740_);
lean_dec(v_snd_1738_);
lean_dec(v_fst_1737_);
lean_dec_ref_known(v___x_1731_, 2);
goto v___jp_1716_;
}
else
{
if (v___y_1799_ == 0)
{
lean_del_object(v___x_1740_);
lean_dec(v_snd_1738_);
lean_dec(v_fst_1737_);
lean_dec_ref_known(v___x_1731_, 2);
goto v___jp_1716_;
}
else
{
lean_del_object(v___x_1695_);
goto v___jp_1771_;
}
}
}
else
{
lean_del_object(v___x_1695_);
goto v___jp_1771_;
}
}
}
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_scopes_1807_; lean_object* v___x_1808_; lean_object* v_opts_1809_; uint8_t v_hasTrace_1810_; 
lean_dec(v___x_1735_);
lean_dec_ref_known(v___x_1731_, 2);
lean_del_object(v___x_1695_);
v___x_1802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1803_ = l_Lean_inheritedTraceOptions;
v___x_1804_ = lean_st_ref_get(v___x_1803_);
v___x_1805_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1806_ = lean_st_ref_get(v___y_1689_);
v_scopes_1807_ = lean_ctor_get(v___x_1806_, 2);
lean_inc(v_scopes_1807_);
lean_dec(v___x_1806_);
v___x_1808_ = l_List_head_x21___redArg(v___x_1805_, v_scopes_1807_);
lean_dec(v_scopes_1807_);
v_opts_1809_ = lean_ctor_get(v___x_1808_, 1);
lean_inc_ref(v_opts_1809_);
lean_dec(v___x_1808_);
v_hasTrace_1810_ = lean_ctor_get_uint8(v_opts_1809_, sizeof(void*)*1);
if (v_hasTrace_1810_ == 0)
{
lean_dec_ref(v_opts_1809_);
lean_dec(v___x_1804_);
lean_dec(v___x_1730_);
lean_dec(v___x_1729_);
lean_del_object(v___x_1727_);
goto v___jp_1720_;
}
else
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1812_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1804_, v_opts_1809_, v___x_1811_);
lean_dec_ref(v_opts_1809_);
lean_dec(v___x_1804_);
if (v___x_1812_ == 0)
{
lean_dec(v___x_1730_);
lean_dec(v___x_1729_);
lean_del_object(v___x_1727_);
goto v___jp_1720_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1813_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1814_ = l_Nat_reprFast(v___x_1729_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 3);
lean_ctor_set(v___x_1727_, 0, v___x_1814_);
v___x_1816_ = v___x_1727_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1817_ = l_Lean_MessageData_ofFormat(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1813_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Nat_reprFast(v___x_1730_);
v___x_1822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
v___x_1823_ = l_Lean_MessageData_ofFormat(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1820_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1802_, v___x_1826_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_dec_ref_known(v___x_1827_, 1);
goto v___jp_1720_;
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_del_object(v___x_1700_);
lean_dec(v_snd_1698_);
lean_dec(v_fst_1697_);
lean_dec(v_cmd_1681_);
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
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
lean_object* v___x_1838_; 
lean_dec(v_endPos_1704_);
lean_del_object(v___x_1695_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_fst_1697_);
lean_ctor_set(v___x_1838_, 1, v_snd_1698_);
v_a_1709_ = v___x_1838_;
goto v___jp_1708_;
}
}
}
else
{
lean_object* v___x_1839_; 
lean_dec(v_endPos_1704_);
lean_del_object(v___x_1695_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_fst_1697_);
lean_ctor_set(v___x_1839_, 1, v_snd_1698_);
v_a_1709_ = v___x_1839_;
goto v___jp_1708_;
}
v___jp_1708_:
{
lean_object* v___x_1711_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v_a_1709_);
lean_ctor_set(v___x_1700_, 0, v___x_1707_);
v___x_1711_ = v___x_1700_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_a_1709_);
v___x_1711_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
size_t v___x_1712_; size_t v___x_1713_; 
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_add(v_i_1686_, v___x_1712_);
v_i_1686_ = v___x_1713_;
v_b_1687_ = v___x_1711_;
goto _start;
}
}
v___jp_1716_:
{
lean_object* v___x_1718_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 1, v_snd_1698_);
lean_ctor_set(v___x_1695_, 0, v_fst_1697_);
v___x_1718_ = v___x_1695_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_fst_1697_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_snd_1698_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v_a_1709_ = v___x_1718_;
goto v___jp_1708_;
}
}
v___jp_1720_:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_fst_1697_);
lean_ctor_set(v___x_1721_, 1, v_snd_1698_);
v_a_1709_ = v___x_1721_;
goto v___jp_1708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13___boxed(lean_object* v___x_1843_, lean_object* v_val_1844_, lean_object* v_cmd_1845_, lean_object* v_onUnsolved_1846_, lean_object* v___y_1847_, lean_object* v_as_1848_, lean_object* v_sz_1849_, lean_object* v_i_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
uint8_t v_onUnsolved_boxed_1855_; uint8_t v___y_12665__boxed_1856_; size_t v_sz_boxed_1857_; size_t v_i_boxed_1858_; lean_object* v_res_1859_; 
v_onUnsolved_boxed_1855_ = lean_unbox(v_onUnsolved_1846_);
v___y_12665__boxed_1856_ = lean_unbox(v___y_1847_);
v_sz_boxed_1857_ = lean_unbox_usize(v_sz_1849_);
lean_dec(v_sz_1849_);
v_i_boxed_1858_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_res_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1843_, v_val_1844_, v_cmd_1845_, v_onUnsolved_boxed_1855_, v___y_12665__boxed_1856_, v_as_1848_, v_sz_boxed_1857_, v_i_boxed_1858_, v_b_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec_ref(v_as_1848_);
lean_dec_ref(v_val_1844_);
lean_dec_ref(v___x_1843_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(lean_object* v___x_1860_, lean_object* v_val_1861_, lean_object* v_cmd_1862_, uint8_t v_onUnsolved_1863_, uint8_t v___y_1864_, lean_object* v_as_1865_, size_t v_sz_1866_, size_t v_i_1867_, lean_object* v_b_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
uint8_t v___x_1872_; 
v___x_1872_ = lean_usize_dec_lt(v_i_1867_, v_sz_1866_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_dec(v_cmd_1862_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_b_1868_);
return v___x_1873_;
}
else
{
lean_object* v_snd_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_2022_; 
v_snd_1874_ = lean_ctor_get(v_b_1868_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_b_1868_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; 
v_unused_2023_ = lean_ctor_get(v_b_1868_, 0);
lean_dec(v_unused_2023_);
v___x_1876_ = v_b_1868_;
v_isShared_1877_ = v_isSharedCheck_2022_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_snd_1874_);
lean_dec(v_b_1868_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_2022_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_2021_; 
v_fst_1878_ = lean_ctor_get(v_snd_1874_, 0);
v_snd_1879_ = lean_ctor_get(v_snd_1874_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_snd_1874_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1881_ = v_snd_1874_;
v_isShared_1882_ = v_isSharedCheck_2021_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snd_1879_);
lean_inc(v_fst_1878_);
lean_dec(v_snd_1874_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_2021_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_a_1883_; lean_object* v_pos_1884_; lean_object* v_endPos_1885_; uint8_t v_severity_1886_; lean_object* v_data_1887_; lean_object* v___x_1888_; lean_object* v_a_1890_; 
v_a_1883_ = lean_array_uget_borrowed(v_as_1865_, v_i_1867_);
v_pos_1884_ = lean_ctor_get(v_a_1883_, 1);
v_endPos_1885_ = lean_ctor_get(v_a_1883_, 2);
lean_inc(v_endPos_1885_);
v_severity_1886_ = lean_ctor_get_uint8(v_a_1883_, sizeof(void*)*5 + 1);
v_data_1887_ = lean_ctor_get(v_a_1883_, 4);
v___x_1888_ = lean_box(0);
if (v_severity_1886_ == 2)
{
lean_object* v___f_1903_; uint8_t v___x_1904_; 
v___f_1903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
lean_inc(v_data_1887_);
v___x_1904_ = l_Lean_MessageData_hasTag(v___f_1903_, v_data_1887_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; 
lean_dec(v_endPos_1885_);
lean_del_object(v___x_1876_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_fst_1878_);
lean_ctor_set(v___x_1905_, 1, v_snd_1879_);
v_a_1890_ = v___x_1905_;
goto v___jp_1889_;
}
else
{
if (lean_obj_tag(v_endPos_1885_) == 1)
{
lean_object* v_val_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_2018_; 
v_val_1906_ = lean_ctor_get(v_endPos_1885_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_endPos_1885_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1908_ = v_endPos_1885_;
v_isShared_1909_ = v_isSharedCheck_2018_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_val_1906_);
lean_dec(v_endPos_1885_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_2018_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; uint8_t v___x_1914_; 
lean_inc_ref(v_pos_1884_);
v___x_1910_ = l_Lean_FileMap_ofPosition(v___x_1860_, v_pos_1884_);
v___x_1911_ = l_Lean_FileMap_ofPosition(v___x_1860_, v_val_1906_);
lean_inc(v___x_1911_);
lean_inc(v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = 0;
v___x_1914_ = l_Lean_Syntax_Range_includes(v_val_1861_, v___x_1912_, v___x_1913_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref_known(v___x_1912_, 2);
lean_dec(v___x_1911_);
lean_dec(v___x_1910_);
lean_del_object(v___x_1908_);
lean_del_object(v___x_1876_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_fst_1878_);
lean_ctor_set(v___x_1915_, 1, v_snd_1879_);
v_a_1890_ = v___x_1915_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1916_; 
lean_inc(v_cmd_1862_);
lean_inc_ref(v___x_1912_);
v___x_1916_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_findTacticSeqBody_walkAndFind(v___x_1912_, v_cmd_1862_);
if (lean_obj_tag(v___x_1916_) == 1)
{
lean_object* v_val_1917_; lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1982_; 
lean_dec(v___x_1911_);
lean_dec(v___x_1910_);
lean_del_object(v___x_1908_);
v_val_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v_fst_1918_ = lean_ctor_get(v_val_1917_, 0);
v_snd_1919_ = lean_ctor_get(v_val_1917_, 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_val_1917_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1921_ = v_val_1917_;
v_isShared_1922_ = v_isSharedCheck_1982_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_snd_1919_);
lean_inc(v_fst_1918_);
lean_dec(v_val_1917_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1982_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; uint8_t v___y_1980_; lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Syntax_getPos_x3f(v_fst_1918_, v___x_1913_);
if (lean_obj_tag(v___x_1981_) == 0)
{
v___y_1980_ = v___x_1914_;
goto v___jp_1979_;
}
else
{
lean_dec_ref_known(v___x_1981_, 1);
v___y_1980_ = v___x_1913_;
goto v___jp_1979_;
}
v___jp_1923_:
{
lean_object* v___x_1929_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v_snd_1879_);
lean_ctor_set(v___x_1921_, 0, v_fst_1878_);
v___x_1929_ = v___x_1921_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_fst_1878_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_snd_1879_);
v___x_1929_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
size_t v_sz_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v_sz_1930_ = lean_array_size(v___y_1924_);
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_1912_, v_fst_1918_, v_snd_1919_, v___y_1925_, v___y_1924_, v_sz_1930_, v___x_1931_, v___x_1929_);
lean_dec_ref(v___y_1924_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_fst_1934_; lean_object* v_snd_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_fst_1934_ = lean_ctor_get(v_a_1933_, 0);
v_snd_1935_ = lean_ctor_get(v_a_1933_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_a_1933_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v_a_1933_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_snd_1935_);
lean_inc(v_fst_1934_);
lean_dec(v_a_1933_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_fst_1934_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_snd_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
v_a_1890_ = v___x_1940_;
goto v___jp_1889_;
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_del_object(v___x_1881_);
lean_dec(v_cmd_1862_);
v_a_1943_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1932_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1932_);
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
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
v___jp_1952_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
lean_inc_ref(v___x_1912_);
v___x_1953_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkRangeStx(v___x_1912_);
v___x_1954_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectGoalsAndCtxFromMessage(v_data_1887_);
v___x_1955_ = lean_array_get_size(v___x_1954_);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_nat_dec_eq(v___x_1955_, v___x_1956_);
if (v___x_1957_ == 0)
{
v___y_1924_ = v___x_1954_;
v___y_1925_ = v___x_1953_;
v___y_1926_ = v___y_1869_;
v___y_1927_ = v___y_1870_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_scopes_1963_; lean_object* v___x_1964_; lean_object* v_opts_1965_; uint8_t v_hasTrace_1966_; 
v___x_1958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1959_ = l_Lean_inheritedTraceOptions;
v___x_1960_ = lean_st_ref_get(v___x_1959_);
v___x_1961_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1962_ = lean_st_ref_get(v___y_1870_);
v_scopes_1963_ = lean_ctor_get(v___x_1962_, 2);
lean_inc(v_scopes_1963_);
lean_dec(v___x_1962_);
v___x_1964_ = l_List_head_x21___redArg(v___x_1961_, v_scopes_1963_);
lean_dec(v_scopes_1963_);
v_opts_1965_ = lean_ctor_get(v___x_1964_, 1);
lean_inc_ref(v_opts_1965_);
lean_dec(v___x_1964_);
v_hasTrace_1966_ = lean_ctor_get_uint8(v_opts_1965_, sizeof(void*)*1);
if (v_hasTrace_1966_ == 0)
{
lean_dec_ref(v_opts_1965_);
lean_dec(v___x_1960_);
v___y_1924_ = v___x_1954_;
v___y_1925_ = v___x_1953_;
v___y_1926_ = v___y_1869_;
v___y_1927_ = v___y_1870_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1960_, v_opts_1965_, v___x_1967_);
lean_dec_ref(v_opts_1965_);
lean_dec(v___x_1960_);
if (v___x_1968_ == 0)
{
v___y_1924_ = v___x_1954_;
v___y_1925_ = v___x_1953_;
v___y_1926_ = v___y_1869_;
v___y_1927_ = v___y_1870_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__5);
v___x_1970_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1958_, v___x_1969_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_dec_ref_known(v___x_1970_, 1);
v___y_1924_ = v___x_1954_;
v___y_1925_ = v___x_1953_;
v___y_1926_ = v___y_1869_;
v___y_1927_ = v___y_1870_;
goto v___jp_1923_;
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v___x_1954_);
lean_dec(v___x_1953_);
lean_del_object(v___x_1921_);
lean_dec(v_snd_1919_);
lean_dec(v_fst_1918_);
lean_dec_ref_known(v___x_1912_, 2);
lean_del_object(v___x_1881_);
lean_dec(v_snd_1879_);
lean_dec(v_fst_1878_);
lean_dec(v_cmd_1862_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
}
}
v___jp_1979_:
{
if (v_onUnsolved_1863_ == 0)
{
if (v___y_1864_ == 0)
{
lean_del_object(v___x_1921_);
lean_dec(v_snd_1919_);
lean_dec(v_fst_1918_);
lean_dec_ref_known(v___x_1912_, 2);
goto v___jp_1897_;
}
else
{
if (v___y_1980_ == 0)
{
lean_del_object(v___x_1921_);
lean_dec(v_snd_1919_);
lean_dec(v_fst_1918_);
lean_dec_ref_known(v___x_1912_, 2);
goto v___jp_1897_;
}
else
{
lean_del_object(v___x_1876_);
goto v___jp_1952_;
}
}
}
else
{
lean_del_object(v___x_1876_);
goto v___jp_1952_;
}
}
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v_scopes_1988_; lean_object* v___x_1989_; lean_object* v_opts_1990_; uint8_t v_hasTrace_1991_; 
lean_dec(v___x_1916_);
lean_dec_ref_known(v___x_1912_, 2);
lean_del_object(v___x_1876_);
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_1984_ = l_Lean_inheritedTraceOptions;
v___x_1985_ = lean_st_ref_get(v___x_1984_);
v___x_1986_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1987_ = lean_st_ref_get(v___y_1870_);
v_scopes_1988_ = lean_ctor_get(v___x_1987_, 2);
lean_inc(v_scopes_1988_);
lean_dec(v___x_1987_);
v___x_1989_ = l_List_head_x21___redArg(v___x_1986_, v_scopes_1988_);
lean_dec(v_scopes_1988_);
v_opts_1990_ = lean_ctor_get(v___x_1989_, 1);
lean_inc_ref(v_opts_1990_);
lean_dec(v___x_1989_);
v_hasTrace_1991_ = lean_ctor_get_uint8(v_opts_1990_, sizeof(void*)*1);
if (v_hasTrace_1991_ == 0)
{
lean_dec_ref(v_opts_1990_);
lean_dec(v___x_1985_);
lean_dec(v___x_1911_);
lean_dec(v___x_1910_);
lean_del_object(v___x_1908_);
goto v___jp_1901_;
}
else
{
lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_1993_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1985_, v_opts_1990_, v___x_1992_);
lean_dec_ref(v_opts_1990_);
lean_dec(v___x_1985_);
if (v___x_1993_ == 0)
{
lean_dec(v___x_1911_);
lean_dec(v___x_1910_);
lean_del_object(v___x_1908_);
goto v___jp_1901_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1994_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__7);
v___x_1995_ = l_Nat_reprFast(v___x_1910_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 3);
lean_ctor_set(v___x_1908_, 0, v___x_1995_);
v___x_1997_ = v___x_1908_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_2017_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_1998_ = l_Lean_MessageData_ofFormat(v___x_1997_);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1994_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__9);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = l_Nat_reprFast(v___x_1911_);
v___x_2003_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
v___x_2004_ = l_Lean_MessageData_ofFormat(v___x_2003_);
v___x_2005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2001_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__11);
v___x_2007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_1983_, v___x_2007_, v___y_1869_, v___y_1870_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_dec_ref_known(v___x_2008_, 1);
goto v___jp_1901_;
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_del_object(v___x_1881_);
lean_dec(v_snd_1879_);
lean_dec(v_fst_1878_);
lean_dec(v_cmd_1862_);
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
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
lean_object* v___x_2019_; 
lean_dec(v_endPos_1885_);
lean_del_object(v___x_1876_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v_fst_1878_);
lean_ctor_set(v___x_2019_, 1, v_snd_1879_);
v_a_1890_ = v___x_2019_;
goto v___jp_1889_;
}
}
}
else
{
lean_object* v___x_2020_; 
lean_dec(v_endPos_1885_);
lean_del_object(v___x_1876_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v_fst_1878_);
lean_ctor_set(v___x_2020_, 1, v_snd_1879_);
v_a_1890_ = v___x_2020_;
goto v___jp_1889_;
}
v___jp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 1, v_a_1890_);
lean_ctor_set(v___x_1881_, 0, v___x_1888_);
v___x_1892_ = v___x_1881_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_a_1890_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = ((size_t)1ULL);
v___x_1894_ = lean_usize_add(v_i_1867_, v___x_1893_);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11_spec__13(v___x_1860_, v_val_1861_, v_cmd_1862_, v_onUnsolved_1863_, v___y_1864_, v_as_1865_, v_sz_1866_, v___x_1894_, v___x_1892_, v___y_1869_, v___y_1870_);
return v___x_1895_;
}
}
v___jp_1897_:
{
lean_object* v___x_1899_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v_snd_1879_);
lean_ctor_set(v___x_1876_, 0, v_fst_1878_);
v___x_1899_ = v___x_1876_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_fst_1878_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_snd_1879_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
v_a_1890_ = v___x_1899_;
goto v___jp_1889_;
}
}
v___jp_1901_:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v_fst_1878_);
lean_ctor_set(v___x_1902_, 1, v_snd_1879_);
v_a_1890_ = v___x_1902_;
goto v___jp_1889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11___boxed(lean_object* v___x_2024_, lean_object* v_val_2025_, lean_object* v_cmd_2026_, lean_object* v_onUnsolved_2027_, lean_object* v___y_2028_, lean_object* v_as_2029_, lean_object* v_sz_2030_, lean_object* v_i_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v_onUnsolved_boxed_2036_; uint8_t v___y_12997__boxed_2037_; size_t v_sz_boxed_2038_; size_t v_i_boxed_2039_; lean_object* v_res_2040_; 
v_onUnsolved_boxed_2036_ = lean_unbox(v_onUnsolved_2027_);
v___y_12997__boxed_2037_ = lean_unbox(v___y_2028_);
v_sz_boxed_2038_ = lean_unbox_usize(v_sz_2030_);
lean_dec(v_sz_2030_);
v_i_boxed_2039_ = lean_unbox_usize(v_i_2031_);
lean_dec(v_i_2031_);
v_res_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2024_, v_val_2025_, v_cmd_2026_, v_onUnsolved_boxed_2036_, v___y_12997__boxed_2037_, v_as_2029_, v_sz_boxed_2038_, v_i_boxed_2039_, v_b_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_as_2029_);
lean_dec_ref(v_val_2025_);
lean_dec_ref(v___x_2024_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(lean_object* v_init_2041_, lean_object* v___x_2042_, lean_object* v_val_2043_, lean_object* v_cmd_2044_, uint8_t v_onUnsolved_2045_, uint8_t v___y_2046_, lean_object* v_n_2047_, lean_object* v_b_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
if (lean_obj_tag(v_n_2047_) == 0)
{
lean_object* v_cs_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; size_t v_sz_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v_cs_2052_ = lean_ctor_get(v_n_2047_, 0);
v___x_2053_ = lean_box(0);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v_b_2048_);
v_sz_2055_ = lean_array_size(v_cs_2052_);
v___x_2056_ = ((size_t)0ULL);
v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2041_, v___x_2042_, v_val_2043_, v_cmd_2044_, v_onUnsolved_2045_, v___y_2046_, v_cs_2052_, v_sz_2055_, v___x_2056_, v___x_2054_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2072_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2072_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2072_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_fst_2062_; 
v_fst_2062_ = lean_ctor_get(v_a_2058_, 0);
if (lean_obj_tag(v_fst_2062_) == 0)
{
lean_object* v_snd_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v_snd_2063_ = lean_ctor_get(v_a_2058_, 1);
lean_inc(v_snd_2063_);
lean_dec(v_a_2058_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_snd_2063_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2064_);
v___x_2066_ = v___x_2060_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
else
{
lean_object* v_val_2068_; lean_object* v___x_2070_; 
lean_inc_ref(v_fst_2062_);
lean_dec(v_a_2058_);
v_val_2068_ = lean_ctor_get(v_fst_2062_, 0);
lean_inc(v_val_2068_);
lean_dec_ref_known(v_fst_2062_, 1);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v_val_2068_);
v___x_2070_ = v___x_2060_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_val_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
v_a_2073_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2057_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2057_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
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
lean_object* v_vs_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; size_t v_sz_2084_; size_t v___x_2085_; lean_object* v___x_2086_; 
v_vs_2081_ = lean_ctor_get(v_n_2047_, 0);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v_b_2048_);
v_sz_2084_ = lean_array_size(v_vs_2081_);
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__11(v___x_2042_, v_val_2043_, v_cmd_2044_, v_onUnsolved_2045_, v___y_2046_, v_vs_2081_, v_sz_2084_, v___x_2085_, v___x_2083_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2101_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2101_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2101_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_fst_2091_; 
v_fst_2091_ = lean_ctor_get(v_a_2087_, 0);
if (lean_obj_tag(v_fst_2091_) == 0)
{
lean_object* v_snd_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v_snd_2092_ = lean_ctor_get(v_a_2087_, 1);
lean_inc(v_snd_2092_);
lean_dec(v_a_2087_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_snd_2092_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2093_);
v___x_2095_ = v___x_2089_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
else
{
lean_object* v_val_2097_; lean_object* v___x_2099_; 
lean_inc_ref(v_fst_2091_);
lean_dec(v_a_2087_);
v_val_2097_ = lean_ctor_get(v_fst_2091_, 0);
lean_inc(v_val_2097_);
lean_dec_ref_known(v_fst_2091_, 1);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v_val_2097_);
v___x_2099_ = v___x_2089_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_val_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
v_a_2102_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2086_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2086_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(lean_object* v_init_2110_, lean_object* v___x_2111_, lean_object* v_val_2112_, lean_object* v_cmd_2113_, uint8_t v_onUnsolved_2114_, uint8_t v___y_2115_, lean_object* v_as_2116_, size_t v_sz_2117_, size_t v_i_2118_, lean_object* v_b_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_usize_dec_lt(v_i_2118_, v_sz_2117_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; 
lean_dec(v_cmd_2113_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_b_2119_);
return v___x_2124_;
}
else
{
lean_object* v_snd_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2159_; 
v_snd_2125_ = lean_ctor_get(v_b_2119_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_b_2119_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v_b_2119_, 0);
lean_dec(v_unused_2160_);
v___x_2127_ = v_b_2119_;
v_isShared_2128_ = v_isSharedCheck_2159_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_snd_2125_);
lean_dec(v_b_2119_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2159_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v_a_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_box(0);
v_a_2130_ = lean_array_uget_borrowed(v_as_2116_, v_i_2118_);
lean_inc(v_snd_2125_);
lean_inc(v_cmd_2113_);
v___x_2131_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2110_, v___x_2111_, v_val_2112_, v_cmd_2113_, v_onUnsolved_2114_, v___y_2115_, v_a_2130_, v_snd_2125_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2150_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2150_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2150_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
if (lean_obj_tag(v_a_2132_) == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_dec(v_cmd_2113_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_a_2132_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2136_);
v___x_2138_ = v___x_2127_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_snd_2125_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2138_);
v___x_2140_ = v___x_2134_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; 
lean_del_object(v___x_2134_);
lean_dec(v_snd_2125_);
v_a_2143_ = lean_ctor_get(v_a_2132_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v_a_2132_, 1);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 1, v_a_2143_);
lean_ctor_set(v___x_2127_, 0, v___x_2129_);
v___x_2145_ = v___x_2127_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_a_2143_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
size_t v___x_2146_; size_t v___x_2147_; 
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_i_2118_, v___x_2146_);
v_i_2118_ = v___x_2147_;
v_b_2119_ = v___x_2145_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_del_object(v___x_2127_);
lean_dec(v_snd_2125_);
lean_dec(v_cmd_2113_);
v_a_2151_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2131_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2131_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10___boxed(lean_object* v_init_2161_, lean_object* v___x_2162_, lean_object* v_val_2163_, lean_object* v_cmd_2164_, lean_object* v_onUnsolved_2165_, lean_object* v___y_2166_, lean_object* v_as_2167_, lean_object* v_sz_2168_, lean_object* v_i_2169_, lean_object* v_b_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v_onUnsolved_boxed_2174_; uint8_t v___y_13298__boxed_2175_; size_t v_sz_boxed_2176_; size_t v_i_boxed_2177_; lean_object* v_res_2178_; 
v_onUnsolved_boxed_2174_ = lean_unbox(v_onUnsolved_2165_);
v___y_13298__boxed_2175_ = lean_unbox(v___y_2166_);
v_sz_boxed_2176_ = lean_unbox_usize(v_sz_2168_);
lean_dec(v_sz_2168_);
v_i_boxed_2177_ = lean_unbox_usize(v_i_2169_);
lean_dec(v_i_2169_);
v_res_2178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8_spec__10(v_init_2161_, v___x_2162_, v_val_2163_, v_cmd_2164_, v_onUnsolved_boxed_2174_, v___y_13298__boxed_2175_, v_as_2167_, v_sz_boxed_2176_, v_i_boxed_2177_, v_b_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec_ref(v_as_2167_);
lean_dec_ref(v_val_2163_);
lean_dec_ref(v___x_2162_);
lean_dec_ref(v_init_2161_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8___boxed(lean_object* v_init_2179_, lean_object* v___x_2180_, lean_object* v_val_2181_, lean_object* v_cmd_2182_, lean_object* v_onUnsolved_2183_, lean_object* v___y_2184_, lean_object* v_n_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v_onUnsolved_boxed_2190_; uint8_t v___y_13320__boxed_2191_; lean_object* v_res_2192_; 
v_onUnsolved_boxed_2190_ = lean_unbox(v_onUnsolved_2183_);
v___y_13320__boxed_2191_ = lean_unbox(v___y_2184_);
v_res_2192_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2179_, v___x_2180_, v_val_2181_, v_cmd_2182_, v_onUnsolved_boxed_2190_, v___y_13320__boxed_2191_, v_n_2185_, v_b_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec_ref(v_n_2185_);
lean_dec_ref(v_val_2181_);
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_init_2179_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(lean_object* v___x_2193_, lean_object* v_val_2194_, lean_object* v_cmd_2195_, uint8_t v_onUnsolved_2196_, uint8_t v___y_2197_, lean_object* v_t_2198_, lean_object* v_init_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_root_2203_; lean_object* v_tail_2204_; lean_object* v___x_2205_; 
v_root_2203_ = lean_ctor_get(v_t_2198_, 0);
v_tail_2204_ = lean_ctor_get(v_t_2198_, 1);
lean_inc(v_cmd_2195_);
lean_inc_ref(v_init_2199_);
v___x_2205_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__8(v_init_2199_, v___x_2193_, v_val_2194_, v_cmd_2195_, v_onUnsolved_2196_, v___y_2197_, v_root_2203_, v_init_2199_, v___y_2200_, v___y_2201_);
lean_dec_ref(v_init_2199_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2242_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2242_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2242_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
if (lean_obj_tag(v_a_2206_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; 
lean_dec(v_cmd_2195_);
v_a_2210_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v_a_2206_, 1);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v_a_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; size_t v_sz_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
lean_del_object(v___x_2208_);
v_a_2214_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v_a_2206_, 1);
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v_a_2214_);
v_sz_2217_ = lean_array_size(v_tail_2204_);
v___x_2218_ = ((size_t)0ULL);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9(v___x_2193_, v_val_2194_, v_cmd_2195_, v_onUnsolved_2196_, v___y_2197_, v_tail_2204_, v_sz_2217_, v___x_2218_, v___x_2216_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2233_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2233_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2233_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v_fst_2224_; 
v_fst_2224_ = lean_ctor_get(v_a_2220_, 0);
if (lean_obj_tag(v_fst_2224_) == 0)
{
lean_object* v_snd_2225_; lean_object* v___x_2227_; 
v_snd_2225_ = lean_ctor_get(v_a_2220_, 1);
lean_inc(v_snd_2225_);
lean_dec(v_a_2220_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v_snd_2225_);
v___x_2227_ = v___x_2222_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_snd_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2231_; 
lean_inc_ref(v_fst_2224_);
lean_dec(v_a_2220_);
v_val_2229_ = lean_ctor_get(v_fst_2224_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v_fst_2224_, 1);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v_val_2229_);
v___x_2231_ = v___x_2222_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_val_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_a_2234_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2219_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2219_);
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
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_cmd_2195_);
v_a_2243_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2205_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2205_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5___boxed(lean_object* v___x_2251_, lean_object* v_val_2252_, lean_object* v_cmd_2253_, lean_object* v_onUnsolved_2254_, lean_object* v___y_2255_, lean_object* v_t_2256_, lean_object* v_init_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_onUnsolved_boxed_2261_; uint8_t v___y_13511__boxed_2262_; lean_object* v_res_2263_; 
v_onUnsolved_boxed_2261_ = lean_unbox(v_onUnsolved_2254_);
v___y_13511__boxed_2262_ = lean_unbox(v___y_2255_);
v_res_2263_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v___x_2251_, v_val_2252_, v_cmd_2253_, v_onUnsolved_boxed_2261_, v___y_13511__boxed_2262_, v_t_2256_, v_init_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v_t_2256_);
lean_dec_ref(v_val_2252_);
lean_dec_ref(v___x_2251_);
return v_res_2263_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_box(0);
v___x_2265_ = lean_unsigned_to_nat(16u);
v___x_2266_ = lean_mk_array(v___x_2265_, v___x_2264_);
return v___x_2266_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__0);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___x_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(lean_object* v_cmd_2273_, lean_object* v_opts_2274_, lean_object* v_tree_2275_, lean_object* v_msgs_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___y_2281_; lean_object* v___y_2282_; uint8_t v___y_2283_; lean_object* v___y_2284_; uint8_t v___y_2285_; uint8_t v___y_2286_; uint8_t v___y_2312_; uint8_t v___y_2313_; lean_object* v_acc_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___f_2318_; uint8_t v___y_2320_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___f_2318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__2));
v___x_2327_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_2328_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2274_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_2330_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2274_, v___x_2329_);
v___y_2320_ = v___x_2330_;
goto v___jp_2319_;
}
else
{
v___y_2320_ = v___x_2328_;
goto v___jp_2319_;
}
v___jp_2280_:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_Syntax_getRange_x3f(v_cmd_2273_, v___y_2286_);
if (lean_obj_tag(v___x_2287_) == 1)
{
lean_object* v_val_2288_; lean_object* v_fileMap_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_val_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_val_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_fileMap_2289_ = lean_ctor_get(v___y_2281_, 1);
v___x_2290_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__1);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___y_2282_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5(v_fileMap_2289_, v_val_2288_, v_cmd_2273_, v___y_2283_, v___y_2285_, v_msgs_2276_, v___x_2291_, v___y_2281_, v___y_2284_);
lean_dec(v_val_2288_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2301_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2301_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2301_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_fst_2297_; lean_object* v___x_2299_; 
v_fst_2297_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_fst_2297_);
lean_dec(v_a_2293_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v_fst_2297_);
v___x_2299_ = v___x_2295_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_fst_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_a_2302_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2292_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2292_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v___x_2310_; 
lean_dec(v___x_2287_);
lean_dec(v_cmd_2273_);
v___x_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2310_, 0, v___y_2282_);
return v___x_2310_;
}
}
v___jp_2311_:
{
if (v___y_2312_ == 0)
{
if (v___y_2313_ == 0)
{
lean_object* v___x_2317_; 
lean_dec(v_cmd_2273_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_acc_2314_);
return v___x_2317_;
}
else
{
v___y_2281_ = v___y_2315_;
v___y_2282_ = v_acc_2314_;
v___y_2283_ = v___y_2312_;
v___y_2284_ = v___y_2316_;
v___y_2285_ = v___y_2313_;
v___y_2286_ = v___y_2313_;
goto v___jp_2280_;
}
}
else
{
v___y_2281_ = v___y_2315_;
v___y_2282_ = v_acc_2314_;
v___y_2283_ = v___y_2312_;
v___y_2284_ = v___y_2316_;
v___y_2285_ = v___y_2313_;
v___y_2286_ = v___y_2312_;
goto v___jp_2280_;
}
}
v___jp_2319_:
{
lean_object* v___x_2321_; uint8_t v_onUnsolved_2322_; lean_object* v___x_2323_; uint8_t v_onSorry_2324_; lean_object* v_acc_2325_; 
v___x_2321_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v_onUnsolved_2322_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2274_, v___x_2321_);
v___x_2323_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v_onSorry_2324_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_2274_, v___x_2323_);
v_acc_2325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___closed__3));
if (v_onSorry_2324_ == 0)
{
lean_dec_ref(v_tree_2275_);
v___y_2312_ = v_onUnsolved_2322_;
v___y_2313_ = v___y_2320_;
v_acc_2314_ = v_acc_2325_;
v___y_2315_ = v_a_2277_;
v___y_2316_ = v_a_2278_;
goto v___jp_2311_;
}
else
{
lean_object* v_acc_2326_; 
v_acc_2326_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_2318_, v_acc_2325_, v_tree_2275_);
v___y_2312_ = v_onUnsolved_2322_;
v___y_2313_ = v___y_2320_;
v_acc_2314_ = v_acc_2326_;
v___y_2315_ = v_a_2277_;
v___y_2316_ = v_a_2278_;
goto v___jp_2311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints___boxed(lean_object* v_cmd_2331_, lean_object* v_opts_2332_, lean_object* v_tree_2333_, lean_object* v_msgs_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_cmd_2331_, v_opts_2332_, v_tree_2333_, v_msgs_2334_, v_a_2335_, v_a_2336_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec_ref(v_msgs_2334_);
lean_dec_ref(v_opts_2332_);
return v_res_2338_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(lean_object* v_00_u03b2_2339_, lean_object* v_m_2340_, lean_object* v_a_2341_){
_start:
{
uint8_t v___x_2342_; 
v___x_2342_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___redArg(v_m_2340_, v_a_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1___boxed(lean_object* v_00_u03b2_2343_, lean_object* v_m_2344_, lean_object* v_a_2345_){
_start:
{
uint8_t v_res_2346_; lean_object* v_r_2347_; 
v_res_2346_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1(v_00_u03b2_2343_, v_m_2344_, v_a_2345_);
lean_dec_ref(v_a_2345_);
lean_dec_ref(v_m_2344_);
v_r_2347_ = lean_box(v_res_2346_);
return v_r_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2(lean_object* v_00_u03b2_2348_, lean_object* v_m_2349_, lean_object* v_a_2350_, lean_object* v_b_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2___redArg(v_m_2349_, v_a_2350_, v_b_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(lean_object* v___x_2353_, lean_object* v_fst_2354_, lean_object* v_snd_2355_, lean_object* v___x_2356_, lean_object* v_as_2357_, size_t v_sz_2358_, size_t v_i_2359_, lean_object* v_b_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___redArg(v___x_2353_, v_fst_2354_, v_snd_2355_, v___x_2356_, v_as_2357_, v_sz_2358_, v_i_2359_, v_b_2360_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3___boxed(lean_object* v___x_2365_, lean_object* v_fst_2366_, lean_object* v_snd_2367_, lean_object* v___x_2368_, lean_object* v_as_2369_, lean_object* v_sz_2370_, lean_object* v_i_2371_, lean_object* v_b_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
size_t v_sz_boxed_2376_; size_t v_i_boxed_2377_; lean_object* v_res_2378_; 
v_sz_boxed_2376_ = lean_unbox_usize(v_sz_2370_);
lean_dec(v_sz_2370_);
v_i_boxed_2377_ = lean_unbox_usize(v_i_2371_);
lean_dec(v_i_2371_);
v_res_2378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__3(v___x_2365_, v_fst_2366_, v_snd_2367_, v___x_2368_, v_as_2369_, v_sz_boxed_2376_, v_i_boxed_2377_, v_b_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v_as_2369_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(lean_object* v_msgData_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v_msgData_2379_, v___y_2381_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___boxed(lean_object* v_msgData_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6(v_msgData_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2388_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(lean_object* v_00_u03b2_2389_, lean_object* v_a_2390_, lean_object* v_x_2391_){
_start:
{
uint8_t v___x_2392_; 
v___x_2392_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___redArg(v_a_2390_, v_x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2393_, lean_object* v_a_2394_, lean_object* v_x_2395_){
_start:
{
uint8_t v_res_2396_; lean_object* v_r_2397_; 
v_res_2396_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__1_spec__1(v_00_u03b2_2393_, v_a_2394_, v_x_2395_);
lean_dec(v_x_2395_);
lean_dec_ref(v_a_2394_);
v_r_2397_ = lean_box(v_res_2396_);
return v_r_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3(lean_object* v_00_u03b2_2398_, lean_object* v_data_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3___redArg(v_data_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_2401_, lean_object* v_i_2402_, lean_object* v_source_2403_, lean_object* v_target_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4___redArg(v_i_2402_, v_source_2403_, v_target_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_2406_, lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__2_spec__3_spec__4_spec__9___redArg(v_x_2407_, v_x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
v___x_2418_ = lean_apply_7(v_x_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, lean_box(0));
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed(lean_object* v_x_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0(v_x_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(lean_object* v_mvarId_2428_, lean_object* v_x_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___f_2437_; lean_object* v___x_2438_; 
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2430_);
v___f_2437_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2437_, 0, v_x_2429_);
lean_closure_set(v___f_2437_, 1, v___y_2430_);
lean_closure_set(v___f_2437_, 2, v___y_2431_);
v___x_2438_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2428_, v___f_2437_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2438_) == 0)
{
return v___x_2438_;
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg___boxed(lean_object* v_mvarId_2447_, lean_object* v_x_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2447_, v_x_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(lean_object* v_00_u03b1_2457_, lean_object* v_mvarId_2458_, lean_object* v_x_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___redArg(v_mvarId_2458_, v_x_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2___boxed(lean_object* v_00_u03b1_2468_, lean_object* v_mvarId_2469_, lean_object* v_x_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__2(v_00_u03b1_2468_, v_mvarId_2469_, v_x_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(lean_object* v_____r_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___boxed(lean_object* v_____r_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0(v_____r_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(lean_object* v_____r_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__0___closed__1));
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1___boxed(lean_object* v_____r_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__1(v_____r_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
return v_res_2520_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(uint8_t v___x_2521_, lean_object* v_x_2522_){
_start:
{
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2___boxed(lean_object* v___x_2523_, lean_object* v_x_2524_){
_start:
{
uint8_t v___x_11058__boxed_2525_; uint8_t v_res_2526_; lean_object* v_r_2527_; 
v___x_11058__boxed_2525_ = lean_unbox(v___x_2523_);
v_res_2526_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__2(v___x_11058__boxed_2525_, v_x_2524_);
lean_dec(v_x_2524_);
v_r_2527_ = lean_box(v_res_2526_);
return v_r_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(lean_object* v_msgData_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v_env_2535_; lean_object* v___x_2536_; lean_object* v_toCold_2537_; lean_object* v_mctx_2538_; lean_object* v_lctx_2539_; lean_object* v_options_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2534_ = lean_st_ref_get(v___y_2532_);
v_env_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_ref(v_env_2535_);
lean_dec(v___x_2534_);
v___x_2536_ = lean_st_ref_get(v___y_2530_);
v_toCold_2537_ = lean_ctor_get(v___y_2531_, 0);
v_mctx_2538_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_mctx_2538_);
lean_dec(v___x_2536_);
v_lctx_2539_ = lean_ctor_get(v___y_2529_, 2);
v_options_2540_ = lean_ctor_get(v_toCold_2537_, 2);
lean_inc_ref(v_options_2540_);
lean_inc_ref(v_lctx_2539_);
v___x_2541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2541_, 0, v_env_2535_);
lean_ctor_set(v___x_2541_, 1, v_mctx_2538_);
lean_ctor_set(v___x_2541_, 2, v_lctx_2539_);
lean_ctor_set(v___x_2541_, 3, v_options_2540_);
v___x_2542_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v_msgData_2528_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2___boxed(lean_object* v_msgData_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msgData_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(lean_object* v_cls_2551_, lean_object* v_msg_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_ref_2558_; lean_object* v___x_2559_; lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2605_; 
v_ref_2558_ = lean_ctor_get(v___y_2555_, 2);
v___x_2559_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2605_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2605_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v_traceState_2565_; lean_object* v_env_2566_; lean_object* v_nextMacroScope_2567_; lean_object* v_ngen_2568_; lean_object* v_auxDeclNGen_2569_; lean_object* v_cache_2570_; lean_object* v_recordedDeps_2571_; lean_object* v_messages_2572_; lean_object* v_infoState_2573_; lean_object* v_snapshotTasks_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2604_; 
v___x_2564_ = lean_st_ref_take(v___y_2556_);
v_traceState_2565_ = lean_ctor_get(v___x_2564_, 4);
v_env_2566_ = lean_ctor_get(v___x_2564_, 0);
v_nextMacroScope_2567_ = lean_ctor_get(v___x_2564_, 1);
v_ngen_2568_ = lean_ctor_get(v___x_2564_, 2);
v_auxDeclNGen_2569_ = lean_ctor_get(v___x_2564_, 3);
v_cache_2570_ = lean_ctor_get(v___x_2564_, 5);
v_recordedDeps_2571_ = lean_ctor_get(v___x_2564_, 6);
v_messages_2572_ = lean_ctor_get(v___x_2564_, 7);
v_infoState_2573_ = lean_ctor_get(v___x_2564_, 8);
v_snapshotTasks_2574_ = lean_ctor_get(v___x_2564_, 9);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2576_ = v___x_2564_;
v_isShared_2577_ = v_isSharedCheck_2604_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_snapshotTasks_2574_);
lean_inc(v_infoState_2573_);
lean_inc(v_messages_2572_);
lean_inc(v_recordedDeps_2571_);
lean_inc(v_cache_2570_);
lean_inc(v_traceState_2565_);
lean_inc(v_auxDeclNGen_2569_);
lean_inc(v_ngen_2568_);
lean_inc(v_nextMacroScope_2567_);
lean_inc(v_env_2566_);
lean_dec(v___x_2564_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2604_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
uint64_t v_tid_2578_; lean_object* v_traces_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2603_; 
v_tid_2578_ = lean_ctor_get_uint64(v_traceState_2565_, sizeof(void*)*1);
v_traces_2579_ = lean_ctor_get(v_traceState_2565_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v_traceState_2565_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2581_ = v_traceState_2565_;
v_isShared_2582_ = v_isSharedCheck_2603_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_traces_2579_);
lean_dec(v_traceState_2565_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2603_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; double v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2586_ = 0;
v___x_2587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2588_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2588_, 0, v_cls_2551_);
lean_ctor_set(v___x_2588_, 1, v___x_2584_);
lean_ctor_set(v___x_2588_, 2, v___x_2587_);
lean_ctor_set_float(v___x_2588_, sizeof(void*)*3, v___x_2585_);
lean_ctor_set_float(v___x_2588_, sizeof(void*)*3 + 8, v___x_2585_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*3 + 16, v___x_2586_);
v___x_2589_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2590_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v_a_2560_);
lean_ctor_set(v___x_2590_, 2, v___x_2589_);
lean_inc(v_ref_2558_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_ref_2558_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = l_Lean_PersistentArray_push___redArg(v_traces_2579_, v___x_2591_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2592_);
v___x_2594_ = v___x_2581_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2592_);
lean_ctor_set_uint64(v_reuseFailAlloc_2602_, sizeof(void*)*1, v_tid_2578_);
v___x_2594_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2596_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v___x_2594_);
v___x_2596_ = v___x_2576_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_env_2566_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_nextMacroScope_2567_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_ngen_2568_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_auxDeclNGen_2569_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2601_, 5, v_cache_2570_);
lean_ctor_set(v_reuseFailAlloc_2601_, 6, v_recordedDeps_2571_);
lean_ctor_set(v_reuseFailAlloc_2601_, 7, v_messages_2572_);
lean_ctor_set(v_reuseFailAlloc_2601_, 8, v_infoState_2573_);
lean_ctor_set(v_reuseFailAlloc_2601_, 9, v_snapshotTasks_2574_);
v___x_2596_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = lean_st_ref_put(v___y_2556_, v___x_2596_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2583_);
v___x_2599_ = v___x_2562_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2583_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg___boxed(lean_object* v_cls_2606_, lean_object* v_msg_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v_cls_2606_, v_msg_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
return v_res_2613_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__0));
v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(lean_object* v___x_2617_, lean_object* v___f_2618_, lean_object* v___x_2619_, lean_object* v___x_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___x_2628_; lean_object* v_a_2630_; lean_object* v___y_2634_; lean_object* v___x_2648_; 
v___x_2628_ = lean_st_mk_ref(v___x_2617_);
v___x_2648_ = l_Lean_Elab_Tactic_saveState___redArg(v___x_2628_, v___y_2622_, v___y_2624_, v___y_2626_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2650_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v___x_2650_ = l_Lean_Elab_Tactic_Try_collectTryCoreSuggestions(v___x_2620_, v___x_2619_, v___x_2628_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; 
lean_dec(v_a_2649_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v___f_2618_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_a_2630_ = v_a_2651_;
goto v___jp_2629_;
}
else
{
lean_object* v_a_2652_; uint8_t v___y_2654_; uint8_t v___x_2698_; 
v_a_2652_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2652_);
v___x_2698_ = l_Lean_Exception_isInterrupt(v_a_2652_);
if (v___x_2698_ == 0)
{
uint8_t v___x_2699_; 
lean_inc(v_a_2652_);
v___x_2699_ = l_Lean_Exception_isRuntime(v_a_2652_);
v___y_2654_ = v___x_2699_;
goto v___jp_2653_;
}
else
{
v___y_2654_ = v___x_2698_;
goto v___jp_2653_;
}
v___jp_2653_:
{
if (v___y_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref_known(v___x_2650_, 1);
v___x_2655_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2649_, v___y_2654_, v___x_2628_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2688_; 
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v___x_2655_, 0);
lean_dec(v_unused_2689_);
v___x_2657_ = v___x_2655_;
v_isShared_2658_ = v_isSharedCheck_2688_;
goto v_resetjp_2656_;
}
else
{
lean_dec(v___x_2655_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2688_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
uint8_t v___x_2659_; 
v___x_2659_ = l_Lean_Exception_isInterrupt(v_a_2652_);
if (v___x_2659_ == 0)
{
uint8_t v___x_2660_; 
lean_inc(v_a_2652_);
v___x_2660_ = l_Lean_Exception_isMaxRecDepth(v_a_2652_);
if (v___x_2660_ == 0)
{
lean_object* v_toCold_2661_; lean_object* v_options_2662_; uint8_t v_hasTrace_2663_; 
lean_del_object(v___x_2657_);
v_toCold_2661_ = lean_ctor_get(v___y_2625_, 0);
v_options_2662_ = lean_ctor_get(v_toCold_2661_, 2);
v_hasTrace_2663_ = lean_ctor_get_uint8(v_options_2662_, sizeof(void*)*1);
if (v_hasTrace_2663_ == 0)
{
lean_dec(v_a_2652_);
goto v___jp_2645_;
}
else
{
lean_object* v_inheritedTraceOptions_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v_inheritedTraceOptions_2664_ = lean_ctor_get(v_toCold_2661_, 11);
v___x_2665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2666_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2664_, v_options_2662_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_dec(v_a_2652_);
goto v___jp_2645_;
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2668_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_2669_ = l_Lean_Exception_toMessageData(v_a_2652_);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1___redArg(v___x_2665_, v___x_2670_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
lean_inc(v___x_2628_);
v___x_2673_ = lean_apply_10(v___f_2618_, v_a_2672_, v___x_2619_, v___x_2628_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
v___y_2634_ = v___x_2673_;
goto v___jp_2633_;
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec(v___x_2628_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v___f_2618_);
v_a_2674_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2671_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2671_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
}
else
{
lean_object* v___x_2683_; 
lean_dec(v___x_2628_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v___f_2618_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set_tag(v___x_2657_, 1);
lean_ctor_set(v___x_2657_, 0, v_a_2652_);
v___x_2683_ = v___x_2657_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2652_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
lean_object* v___x_2686_; 
lean_dec(v___x_2628_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v___f_2618_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set_tag(v___x_2657_, 1);
lean_ctor_set(v___x_2657_, 0, v_a_2652_);
v___x_2686_ = v___x_2657_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2652_);
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
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_a_2652_);
lean_dec(v___x_2628_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v___f_2618_);
v_a_2690_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2655_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2655_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_dec(v_a_2652_);
lean_dec(v_a_2649_);
lean_dec(v___x_2628_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v___f_2618_);
return v___x_2650_;
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v___x_2628_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___x_2620_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v___f_2618_);
v_a_2700_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2648_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2648_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
v___jp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_st_ref_get(v___x_2628_);
lean_dec(v___x_2628_);
lean_dec(v___x_2631_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_a_2630_);
return v___x_2632_;
}
v___jp_2633_:
{
if (lean_obj_tag(v___y_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v_a_2636_; 
v_a_2635_ = lean_ctor_get(v___y_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___y_2634_, 1);
v_a_2636_ = lean_ctor_get(v_a_2635_, 0);
lean_inc(v_a_2636_);
lean_dec(v_a_2635_);
v_a_2630_ = v_a_2636_;
goto v___jp_2629_;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v___x_2628_);
v_a_2637_ = lean_ctor_get(v___y_2634_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___y_2634_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___y_2634_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___y_2634_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
v___jp_2645_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_box(0);
lean_inc(v___x_2628_);
v___x_2647_ = lean_apply_10(v___f_2618_, v___x_2646_, v___x_2619_, v___x_2628_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, lean_box(0));
v___y_2634_ = v___x_2647_;
goto v___jp_2633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___boxed(lean_object* v___x_2708_, lean_object* v___f_2709_, lean_object* v___x_2710_, lean_object* v___x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3(v___x_2708_, v___f_2709_, v___x_2710_, v___x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(lean_object* v___x_2720_, uint8_t v___x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2720_, v___x_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4___boxed(lean_object* v___x_2730_, lean_object* v___x_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v___x_11387__boxed_2739_; lean_object* v_res_2740_; 
v___x_11387__boxed_2739_ = lean_unbox(v___x_2731_);
v_res_2740_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__4(v___x_2730_, v___x_11387__boxed_2739_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(lean_object* v_cls_2741_, lean_object* v_msg_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_ref_2748_; lean_object* v___x_2749_; lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2795_; 
v_ref_2748_ = lean_ctor_get(v___y_2745_, 2);
v___x_2749_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__1_spec__2(v_msg_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2795_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2795_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v_traceState_2755_; lean_object* v_env_2756_; lean_object* v_nextMacroScope_2757_; lean_object* v_ngen_2758_; lean_object* v_auxDeclNGen_2759_; lean_object* v_cache_2760_; lean_object* v_recordedDeps_2761_; lean_object* v_messages_2762_; lean_object* v_infoState_2763_; lean_object* v_snapshotTasks_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2794_; 
v___x_2754_ = lean_st_ref_take(v___y_2746_);
v_traceState_2755_ = lean_ctor_get(v___x_2754_, 4);
v_env_2756_ = lean_ctor_get(v___x_2754_, 0);
v_nextMacroScope_2757_ = lean_ctor_get(v___x_2754_, 1);
v_ngen_2758_ = lean_ctor_get(v___x_2754_, 2);
v_auxDeclNGen_2759_ = lean_ctor_get(v___x_2754_, 3);
v_cache_2760_ = lean_ctor_get(v___x_2754_, 5);
v_recordedDeps_2761_ = lean_ctor_get(v___x_2754_, 6);
v_messages_2762_ = lean_ctor_get(v___x_2754_, 7);
v_infoState_2763_ = lean_ctor_get(v___x_2754_, 8);
v_snapshotTasks_2764_ = lean_ctor_get(v___x_2754_, 9);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2766_ = v___x_2754_;
v_isShared_2767_ = v_isSharedCheck_2794_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_snapshotTasks_2764_);
lean_inc(v_infoState_2763_);
lean_inc(v_messages_2762_);
lean_inc(v_recordedDeps_2761_);
lean_inc(v_cache_2760_);
lean_inc(v_traceState_2755_);
lean_inc(v_auxDeclNGen_2759_);
lean_inc(v_ngen_2758_);
lean_inc(v_nextMacroScope_2757_);
lean_inc(v_env_2756_);
lean_dec(v___x_2754_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2794_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint64_t v_tid_2768_; lean_object* v_traces_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2793_; 
v_tid_2768_ = lean_ctor_get_uint64(v_traceState_2755_, sizeof(void*)*1);
v_traces_2769_ = lean_ctor_get(v_traceState_2755_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_traceState_2755_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2771_ = v_traceState_2755_;
v_isShared_2772_ = v_isSharedCheck_2793_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_traces_2769_);
lean_dec(v_traceState_2755_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2793_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; double v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_box(0);
v___x_2775_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__0);
v___x_2776_ = 0;
v___x_2777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
v___x_2778_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2778_, 0, v_cls_2741_);
lean_ctor_set(v___x_2778_, 1, v___x_2774_);
lean_ctor_set(v___x_2778_, 2, v___x_2777_);
lean_ctor_set_float(v___x_2778_, sizeof(void*)*3, v___x_2775_);
lean_ctor_set_float(v___x_2778_, sizeof(void*)*3 + 8, v___x_2775_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*3 + 16, v___x_2776_);
v___x_2779_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4___closed__1));
v___x_2780_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v_a_2750_);
lean_ctor_set(v___x_2780_, 2, v___x_2779_);
lean_inc(v_ref_2748_);
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v_ref_2748_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = l_Lean_PersistentArray_push___redArg(v_traces_2769_, v___x_2781_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2782_);
v___x_2784_ = v___x_2771_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2782_);
lean_ctor_set_uint64(v_reuseFailAlloc_2792_, sizeof(void*)*1, v_tid_2768_);
v___x_2784_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2786_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v___x_2784_);
v___x_2786_ = v___x_2766_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_env_2756_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_nextMacroScope_2757_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_ngen_2758_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_auxDeclNGen_2759_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2791_, 5, v_cache_2760_);
lean_ctor_set(v_reuseFailAlloc_2791_, 6, v_recordedDeps_2761_);
lean_ctor_set(v_reuseFailAlloc_2791_, 7, v_messages_2762_);
lean_ctor_set(v_reuseFailAlloc_2791_, 8, v_infoState_2763_);
lean_ctor_set(v_reuseFailAlloc_2791_, 9, v_snapshotTasks_2764_);
v___x_2786_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = lean_st_ref_put(v___y_2746_, v___x_2786_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2773_);
v___x_2789_ = v___x_2752_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2773_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3___boxed(lean_object* v_cls_2796_, lean_object* v_msg_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v_cls_2796_, v_msg_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
return v_res_2803_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__0));
v___x_2806_ = l_Lean_stringToMessageData(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5(lean_object* v___f_2807_, lean_object* v_term_2808_, lean_object* v___x_2809_, lean_object* v___x_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___y_2817_; lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_term_2808_, v___x_2809_, v___x_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v___f_2807_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2847_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2847_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_fst_2843_; lean_object* v___x_2845_; 
v_fst_2843_ = lean_ctor_get(v_a_2839_, 0);
lean_inc(v_fst_2843_);
lean_dec(v_a_2839_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v_fst_2843_);
v___x_2845_ = v___x_2841_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_fst_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2888_; 
v_a_2848_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2850_ = v___x_2838_;
v_isShared_2851_ = v_isSharedCheck_2888_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2838_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2888_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
uint8_t v___y_2853_; uint8_t v___x_2886_; 
v___x_2886_ = l_Lean_Exception_isInterrupt(v_a_2848_);
if (v___x_2886_ == 0)
{
uint8_t v___x_2887_; 
lean_inc(v_a_2848_);
v___x_2887_ = l_Lean_Exception_isRuntime(v_a_2848_);
v___y_2853_ = v___x_2887_;
goto v___jp_2852_;
}
else
{
v___y_2853_ = v___x_2886_;
goto v___jp_2852_;
}
v___jp_2852_:
{
if (v___y_2853_ == 0)
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_Exception_isInterrupt(v_a_2848_);
if (v___x_2854_ == 0)
{
uint8_t v___x_2855_; 
lean_inc(v_a_2848_);
v___x_2855_ = l_Lean_Exception_isMaxRecDepth(v_a_2848_);
if (v___x_2855_ == 0)
{
lean_object* v_toCold_2856_; lean_object* v_options_2857_; uint8_t v_hasTrace_2858_; 
lean_del_object(v___x_2850_);
v_toCold_2856_ = lean_ctor_get(v___y_2813_, 0);
v_options_2857_ = lean_ctor_get(v_toCold_2856_, 2);
v_hasTrace_2858_ = lean_ctor_get_uint8(v_options_2857_, sizeof(void*)*1);
if (v_hasTrace_2858_ == 0)
{
lean_dec(v_a_2848_);
goto v___jp_2835_;
}
else
{
lean_object* v_inheritedTraceOptions_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_inheritedTraceOptions_2859_ = lean_ctor_get(v_toCold_2856_, 11);
v___x_2860_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_2861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_2862_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2859_, v_options_2857_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_dec(v_a_2848_);
goto v___jp_2835_;
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2863_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__5___closed__1);
v___x_2864_ = l_Lean_Exception_toMessageData(v_a_2848_);
v___x_2865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_2860_, v___x_2865_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2868_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v___x_2868_ = lean_apply_6(v___f_2807_, v_a_2867_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, lean_box(0));
v___y_2817_ = v___x_2868_;
goto v___jp_2816_;
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v___f_2807_);
v_a_2869_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2866_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2866_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
else
{
lean_object* v___x_2878_; 
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v___f_2807_);
if (v_isShared_2851_ == 0)
{
v___x_2878_ = v___x_2850_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2848_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
else
{
lean_object* v___x_2881_; 
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v___f_2807_);
if (v_isShared_2851_ == 0)
{
v___x_2881_ = v___x_2850_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2848_);
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
lean_object* v___x_2884_; 
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v___f_2807_);
if (v_isShared_2851_ == 0)
{
v___x_2884_ = v___x_2850_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2848_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
v___jp_2816_:
{
if (lean_obj_tag(v___y_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2826_; 
v_a_2818_ = lean_ctor_get(v___y_2817_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___y_2817_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2820_ = v___y_2817_;
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___y_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_a_2822_; lean_object* v___x_2824_; 
v_a_2822_ = lean_ctor_get(v_a_2818_, 0);
lean_inc(v_a_2822_);
lean_dec(v_a_2818_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_a_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2822_);
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
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
v_a_2827_ = lean_ctor_get(v___y_2817_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___y_2817_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___y_2817_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___y_2817_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
v___jp_2835_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_apply_6(v___f_2807_, v___x_2836_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, lean_box(0));
v___y_2817_ = v___x_2837_;
goto v___jp_2816_;
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
size_t v_x_11706__boxed_2944_; lean_object* v_res_2945_; 
v_x_11706__boxed_2944_ = lean_unbox_usize(v_x_2942_);
lean_dec(v_x_2942_);
v_res_2945_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0___redArg(v_x_2941_, v_x_11706__boxed_2944_, v_x_2943_);
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
size_t v_x_11963__boxed_3055_; lean_object* v_res_3056_; 
v_x_11963__boxed_3055_ = lean_unbox_usize(v_x_3053_);
lean_dec(v_x_3053_);
v_res_3056_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0_spec__0(v_00_u03b2_3051_, v_x_3052_, v_x_11963__boxed_3055_, v_x_3054_);
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
uint8_t v___x_3494__boxed_3104_; lean_object* v_res_3105_; 
v___x_3494__boxed_3104_ = lean_unbox(v___x_3095_);
v_res_3105_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0(v___x_3494__boxed_3104_, v___x_3096_, v_ref_3097_, v_a_3098_, v___x_3099_, v___x_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___x_3100_);
lean_dec_ref(v___x_3099_);
return v_res_3105_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_3106_, uint8_t v___y_3107_, lean_object* v_x_3108_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 1)
{
lean_object* v_pre_3109_; 
v_pre_3109_ = lean_ctor_get(v_x_3108_, 0);
if (lean_obj_tag(v_pre_3109_) == 0)
{
lean_object* v_str_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v_str_3110_ = lean_ctor_get(v_x_3108_, 1);
v___x_3111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__1));
v___x_3112_ = lean_string_dec_eq(v_str_3110_, v___x_3111_);
if (v___x_3112_ == 0)
{
return v___x_3112_;
}
else
{
return v_suppressElabErrors_3106_;
}
}
else
{
return v___y_3107_;
}
}
else
{
return v___y_3107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_3113_, lean_object* v___y_3114_, lean_object* v_x_3115_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3116_; uint8_t v___y_3547__boxed_3117_; uint8_t v_res_3118_; lean_object* v_r_3119_; 
v_suppressElabErrors_boxed_3116_ = lean_unbox(v_suppressElabErrors_3113_);
v___y_3547__boxed_3117_ = lean_unbox(v___y_3114_);
v_res_3118_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_3116_, v___y_3547__boxed_3117_, v_x_3115_);
lean_dec(v_x_3115_);
v_r_3119_ = lean_box(v_res_3118_);
return v_r_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(lean_object* v_ref_3120_, lean_object* v_msgData_3121_, uint8_t v_severity_3122_, uint8_t v_isSilent_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___y_3128_; uint8_t v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; uint8_t v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; uint8_t v___y_3193_; uint8_t v___y_3194_; lean_object* v___y_3195_; uint8_t v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3221_; uint8_t v___y_3222_; lean_object* v___y_3223_; uint8_t v___y_3224_; lean_object* v___y_3225_; uint8_t v___y_3229_; uint8_t v___y_3230_; uint8_t v___y_3231_; uint8_t v___x_3246_; uint8_t v___y_3248_; uint8_t v___y_3249_; uint8_t v___y_3250_; uint8_t v___y_3252_; uint8_t v___x_3264_; 
v___x_3246_ = 2;
v___x_3264_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3122_, v___x_3246_);
if (v___x_3264_ == 0)
{
v___y_3252_ = v___x_3264_;
goto v___jp_3251_;
}
else
{
uint8_t v___x_3265_; 
lean_inc_ref(v_msgData_3121_);
v___x_3265_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3121_);
v___y_3252_ = v___x_3265_;
goto v___jp_3251_;
}
v___jp_3127_:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_Elab_Command_getScope___redArg(v___y_3135_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v_currNamespace_3138_; lean_object* v___x_3139_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3136_, 1);
v_currNamespace_3138_ = lean_ctor_get(v_a_3137_, 2);
lean_inc(v_currNamespace_3138_);
lean_dec(v_a_3137_);
v___x_3139_ = l_Lean_Elab_Command_getScope___redArg(v___y_3135_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3175_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3175_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3175_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v_openDecls_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v_env_3149_; lean_object* v_messages_3150_; lean_object* v_scopes_3151_; lean_object* v_usedQuotCtxts_3152_; lean_object* v_nextMacroScope_3153_; lean_object* v_maxRecDepth_3154_; lean_object* v_ngen_3155_; lean_object* v_auxDeclNGen_3156_; lean_object* v_infoState_3157_; lean_object* v_traceState_3158_; lean_object* v_snapshotTasks_3159_; lean_object* v_prevLinterStates_3160_; lean_object* v_codeQualityEntryTasks_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3174_; 
v_openDecls_3144_ = lean_ctor_get(v_a_3140_, 3);
lean_inc(v_openDecls_3144_);
lean_dec(v_a_3140_);
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_currNamespace_3138_);
lean_ctor_set(v___x_3145_, 1, v_openDecls_3144_);
v___x_3146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v___y_3134_);
lean_inc_ref(v___y_3128_);
lean_inc_ref(v___y_3132_);
v___x_3147_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3147_, 0, v___y_3132_);
lean_ctor_set(v___x_3147_, 1, v___y_3131_);
lean_ctor_set(v___x_3147_, 2, v___y_3130_);
lean_ctor_set(v___x_3147_, 3, v___y_3128_);
lean_ctor_set(v___x_3147_, 4, v___x_3146_);
lean_ctor_set_uint8(v___x_3147_, sizeof(void*)*5, v___y_3129_);
lean_ctor_set_uint8(v___x_3147_, sizeof(void*)*5 + 1, v___y_3133_);
lean_ctor_set_uint8(v___x_3147_, sizeof(void*)*5 + 2, v_isSilent_3123_);
v___x_3148_ = lean_st_ref_take(v___y_3135_);
v_env_3149_ = lean_ctor_get(v___x_3148_, 0);
v_messages_3150_ = lean_ctor_get(v___x_3148_, 1);
v_scopes_3151_ = lean_ctor_get(v___x_3148_, 2);
v_usedQuotCtxts_3152_ = lean_ctor_get(v___x_3148_, 3);
v_nextMacroScope_3153_ = lean_ctor_get(v___x_3148_, 4);
v_maxRecDepth_3154_ = lean_ctor_get(v___x_3148_, 5);
v_ngen_3155_ = lean_ctor_get(v___x_3148_, 6);
v_auxDeclNGen_3156_ = lean_ctor_get(v___x_3148_, 7);
v_infoState_3157_ = lean_ctor_get(v___x_3148_, 8);
v_traceState_3158_ = lean_ctor_get(v___x_3148_, 9);
v_snapshotTasks_3159_ = lean_ctor_get(v___x_3148_, 10);
v_prevLinterStates_3160_ = lean_ctor_get(v___x_3148_, 11);
v_codeQualityEntryTasks_3161_ = lean_ctor_get(v___x_3148_, 12);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3163_ = v___x_3148_;
v_isShared_3164_ = v_isSharedCheck_3174_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3161_);
lean_inc(v_prevLinterStates_3160_);
lean_inc(v_snapshotTasks_3159_);
lean_inc(v_traceState_3158_);
lean_inc(v_infoState_3157_);
lean_inc(v_auxDeclNGen_3156_);
lean_inc(v_ngen_3155_);
lean_inc(v_maxRecDepth_3154_);
lean_inc(v_nextMacroScope_3153_);
lean_inc(v_usedQuotCtxts_3152_);
lean_inc(v_scopes_3151_);
lean_inc(v_messages_3150_);
lean_inc(v_env_3149_);
lean_dec(v___x_3148_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3174_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3165_ = lean_box(0);
v___x_3166_ = l_Lean_MessageLog_add(v___x_3147_, v_messages_3150_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3166_);
v___x_3168_ = v___x_3163_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_env_3149_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_scopes_3151_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_usedQuotCtxts_3152_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_nextMacroScope_3153_);
lean_ctor_set(v_reuseFailAlloc_3173_, 5, v_maxRecDepth_3154_);
lean_ctor_set(v_reuseFailAlloc_3173_, 6, v_ngen_3155_);
lean_ctor_set(v_reuseFailAlloc_3173_, 7, v_auxDeclNGen_3156_);
lean_ctor_set(v_reuseFailAlloc_3173_, 8, v_infoState_3157_);
lean_ctor_set(v_reuseFailAlloc_3173_, 9, v_traceState_3158_);
lean_ctor_set(v_reuseFailAlloc_3173_, 10, v_snapshotTasks_3159_);
lean_ctor_set(v_reuseFailAlloc_3173_, 11, v_prevLinterStates_3160_);
lean_ctor_set(v_reuseFailAlloc_3173_, 12, v_codeQualityEntryTasks_3161_);
v___x_3168_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_st_ref_put(v___y_3135_, v___x_3168_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3165_);
v___x_3171_ = v___x_3142_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3165_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v_currNamespace_3138_);
lean_dec_ref(v___y_3134_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
v_a_3176_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3139_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3139_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v___y_3134_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
v_a_3184_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3136_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3136_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
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
v___jp_3192_:
{
lean_object* v_fileName_3198_; lean_object* v_fileMap_3199_; uint8_t v_suppressElabErrors_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___f_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3219_; 
v_fileName_3198_ = lean_ctor_get(v___y_3124_, 0);
v_fileMap_3199_ = lean_ctor_get(v___y_3124_, 1);
v_suppressElabErrors_3200_ = lean_ctor_get_uint8(v___y_3124_, sizeof(void*)*10);
v___x_3201_ = lean_box(v_suppressElabErrors_3200_);
v___x_3202_ = lean_box(v___y_3193_);
v___f_3203_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3203_, 0, v___x_3201_);
lean_closure_set(v___f_3203_, 1, v___x_3202_);
v___x_3204_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3121_);
v___x_3205_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4_spec__6___redArg(v___x_3204_, v___y_3125_);
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
lean_inc_ref_n(v_fileMap_3199_, 2);
v___x_3210_ = l_Lean_FileMap_toPosition(v_fileMap_3199_, v___y_3195_);
lean_dec(v___y_3195_);
v___x_3211_ = l_Lean_FileMap_toPosition(v_fileMap_3199_, v___y_3197_);
lean_dec(v___y_3197_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___x_3213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx___closed__0));
if (v_suppressElabErrors_3200_ == 0)
{
lean_del_object(v___x_3208_);
lean_dec_ref(v___f_3203_);
v___y_3128_ = v___x_3213_;
v___y_3129_ = v___y_3194_;
v___y_3130_ = v___x_3212_;
v___y_3131_ = v___x_3210_;
v___y_3132_ = v_fileName_3198_;
v___y_3133_ = v___y_3196_;
v___y_3134_ = v_a_3206_;
v___y_3135_ = v___y_3125_;
goto v___jp_3127_;
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
v___y_3128_ = v___x_3213_;
v___y_3129_ = v___y_3194_;
v___y_3130_ = v___x_3212_;
v___y_3131_ = v___x_3210_;
v___y_3132_ = v_fileName_3198_;
v___y_3133_ = v___y_3196_;
v___y_3134_ = v_a_3206_;
v___y_3135_ = v___y_3125_;
goto v___jp_3127_;
}
}
}
}
v___jp_3220_:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Syntax_getTailPos_x3f(v___y_3223_, v___y_3222_);
lean_dec(v___y_3223_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_inc(v___y_3225_);
v___y_3193_ = v___y_3221_;
v___y_3194_ = v___y_3222_;
v___y_3195_ = v___y_3225_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3225_;
goto v___jp_3192_;
}
else
{
lean_object* v_val_3227_; 
v_val_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_val_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___y_3193_ = v___y_3221_;
v___y_3194_ = v___y_3222_;
v___y_3195_ = v___y_3225_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v_val_3227_;
goto v___jp_3192_;
}
}
v___jp_3228_:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Elab_Command_getRef___redArg(v___y_3124_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v_ref_3234_; lean_object* v___x_3235_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v_ref_3234_ = l_Lean_replaceRef(v_ref_3120_, v_a_3233_);
lean_dec(v_a_3233_);
v___x_3235_ = l_Lean_Syntax_getPos_x3f(v_ref_3234_, v___y_3230_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_unsigned_to_nat(0u);
v___y_3221_ = v___y_3229_;
v___y_3222_ = v___y_3230_;
v___y_3223_ = v_ref_3234_;
v___y_3224_ = v___y_3231_;
v___y_3225_ = v___x_3236_;
goto v___jp_3220_;
}
else
{
lean_object* v_val_3237_; 
v_val_3237_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_val_3237_);
lean_dec_ref_known(v___x_3235_, 1);
v___y_3221_ = v___y_3229_;
v___y_3222_ = v___y_3230_;
v___y_3223_ = v_ref_3234_;
v___y_3224_ = v___y_3231_;
v___y_3225_ = v_val_3237_;
goto v___jp_3220_;
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v_msgData_3121_);
v_a_3238_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3232_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3232_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
v___jp_3247_:
{
if (v___y_3250_ == 0)
{
v___y_3229_ = v___y_3248_;
v___y_3230_ = v___y_3249_;
v___y_3231_ = v_severity_3122_;
goto v___jp_3228_;
}
else
{
v___y_3229_ = v___y_3248_;
v___y_3230_ = v___y_3249_;
v___y_3231_ = v___x_3246_;
goto v___jp_3228_;
}
}
v___jp_3251_:
{
if (v___y_3252_ == 0)
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v_scopes_3255_; lean_object* v___x_3256_; lean_object* v_opts_3257_; uint8_t v___x_3258_; uint8_t v___x_3259_; 
v___x_3253_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3254_ = lean_st_ref_get(v___y_3125_);
v_scopes_3255_ = lean_ctor_get(v___x_3254_, 2);
lean_inc(v_scopes_3255_);
lean_dec(v___x_3254_);
v___x_3256_ = l_List_head_x21___redArg(v___x_3253_, v_scopes_3255_);
lean_dec(v_scopes_3255_);
v_opts_3257_ = lean_ctor_get(v___x_3256_, 1);
lean_inc_ref(v_opts_3257_);
lean_dec(v___x_3256_);
v___x_3258_ = 1;
v___x_3259_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3122_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_dec_ref(v_opts_3257_);
v___y_3248_ = v___y_3252_;
v___y_3249_ = v___y_3252_;
v___y_3250_ = v___x_3259_;
goto v___jp_3247_;
}
else
{
lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = l_Lean_warningAsError;
v___x_3261_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3257_, v___x_3260_);
lean_dec_ref(v_opts_3257_);
v___y_3248_ = v___y_3252_;
v___y_3249_ = v___y_3252_;
v___y_3250_ = v___x_3261_;
goto v___jp_3247_;
}
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
lean_dec_ref(v_msgData_3121_);
v___x_3262_ = lean_box(0);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
return v___x_3263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0___boxed(lean_object* v_ref_3266_, lean_object* v_msgData_3267_, lean_object* v_severity_3268_, lean_object* v_isSilent_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v_severity_boxed_3273_; uint8_t v_isSilent_boxed_3274_; lean_object* v_res_3275_; 
v_severity_boxed_3273_ = lean_unbox(v_severity_3268_);
v_isSilent_boxed_3274_ = lean_unbox(v_isSilent_3269_);
v_res_3275_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3266_, v_msgData_3267_, v_severity_boxed_3273_, v_isSilent_boxed_3274_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v_ref_3266_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(lean_object* v_ref_3276_, lean_object* v_msgData_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v___x_3281_; uint8_t v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = 0;
v___x_3282_ = 0;
v___x_3283_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0_spec__0(v_ref_3276_, v_msgData_3277_, v___x_3281_, v___x_3282_, v___y_3278_, v___y_3279_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0___boxed(lean_object* v_ref_3284_, lean_object* v_msgData_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3284_, v_msgData_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v_ref_3284_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(lean_object* v___x_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___closed__0));
v___x_3294_ = lean_string_append(v___x_3293_, v___x_3291_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed(lean_object* v___x_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0(v___x_3295_, v_x_3296_);
lean_dec_ref(v_x_3296_);
lean_dec_ref(v___x_3295_);
return v_res_3297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__0));
v___x_3300_ = l_Lean_stringToMessageData(v___x_3299_);
return v___x_3300_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__2));
v___x_3303_ = l_Lean_stringToMessageData(v___x_3302_);
return v___x_3303_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__4));
v___x_3306_ = l_Lean_stringToMessageData(v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(lean_object* v___x_3307_, uint8_t v___x_3308_, lean_object* v___x_3309_, lean_object* v_insertPos_3310_, lean_object* v_cmdLine_3311_, lean_object* v_ref_3312_, size_t v_sz_3313_, size_t v_i_3314_, lean_object* v_bs_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
uint8_t v___x_3319_; 
v___x_3319_ = lean_usize_dec_lt(v_i_3314_, v_sz_3313_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; 
lean_dec_ref(v___x_3309_);
lean_dec_ref(v___x_3307_);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_bs_3315_);
return v___x_3320_;
}
else
{
lean_object* v_v_3321_; lean_object* v___x_3322_; lean_object* v_bs_x27_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_v_3321_ = lean_array_uget(v_bs_3315_, v_i_3314_);
v___x_3322_ = lean_unsigned_to_nat(0u);
v_bs_x27_3323_ = lean_array_uset(v_bs_3315_, v_i_3314_, v___x_3322_);
lean_inc(v_v_3321_);
v___x_3324_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTactic___boxed), 4, 1);
lean_closure_set(v___x_3324_, 0, v_v_3321_);
v___x_3325_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_3324_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___f_3329_; lean_object* v___x_3330_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = l_Std_Format_defWidth;
v___x_3328_ = l_Std_Format_pretty(v_a_3326_, v___x_3327_, v___x_3322_, v___x_3322_);
lean_inc_ref(v___x_3328_);
v___f_3329_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3329_, 0, v___x_3328_);
lean_inc_ref(v___x_3307_);
v___x_3330_ = lean_string_append(v___x_3307_, v___x_3328_);
lean_dec_ref(v___x_3328_);
if (v___x_3308_ == 0)
{
goto v___jp_3331_;
}
else
{
lean_object* v___x_3342_; lean_object* v_line_3343_; lean_object* v_column_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3379_; 
lean_inc_ref(v___x_3309_);
v___x_3342_ = l_Lean_FileMap_toPosition(v___x_3309_, v_insertPos_3310_);
v_line_3343_ = lean_ctor_get(v___x_3342_, 0);
v_column_3344_ = lean_ctor_get(v___x_3342_, 1);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3346_ = v___x_3342_;
v_isShared_3347_ = v_isSharedCheck_3379_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_column_3344_);
lean_inc(v_line_3343_);
lean_dec(v___x_3342_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3379_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3348_ = lean_nat_sub(v_line_3343_, v_cmdLine_3311_);
lean_dec(v_line_3343_);
v___x_3349_ = lean_unsigned_to_nat(1u);
v___x_3350_ = lean_nat_add(v___x_3348_, v___x_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__1);
lean_inc_ref(v___x_3330_);
v___x_3352_ = l_String_quote(v___x_3330_);
v___x_3353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
v___x_3354_ = l_Lean_MessageData_ofFormat(v___x_3353_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set_tag(v___x_3346_, 7);
lean_ctor_set(v___x_3346_, 1, v___x_3354_);
lean_ctor_set(v___x_3346_, 0, v___x_3351_);
v___x_3356_ = v___x_3346_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3357_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__3);
v___x_3358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = l_Nat_reprFast(v___x_3350_);
v___x_3360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
v___x_3361_ = l_Lean_MessageData_ofFormat(v___x_3360_);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3358_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___closed__5);
v___x_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = l_Nat_reprFast(v_column_3344_);
v___x_3366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
v___x_3367_ = l_Lean_MessageData_ofFormat(v___x_3366_);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3364_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__0(v_ref_3312_, v___x_3368_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_dec_ref_known(v___x_3369_, 1);
goto v___jp_3331_;
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec_ref(v___x_3330_);
lean_dec_ref(v___f_3329_);
lean_dec_ref(v_bs_x27_3323_);
lean_dec(v_v_3321_);
lean_dec_ref(v___x_3309_);
lean_dec_ref(v___x_3307_);
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3369_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3369_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
v___jp_3331_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3330_);
v___x_3333_ = lean_box(0);
v___x_3334_ = l_Lean_MessageData_ofSyntax(v_v_3321_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___f_3329_);
v___x_3337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3332_);
lean_ctor_set(v___x_3337_, 1, v___x_3333_);
lean_ctor_set(v___x_3337_, 2, v___x_3333_);
lean_ctor_set(v___x_3337_, 3, v___x_3333_);
lean_ctor_set(v___x_3337_, 4, v___x_3335_);
lean_ctor_set(v___x_3337_, 5, v___x_3336_);
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3314_, v___x_3338_);
v___x_3340_ = lean_array_uset(v_bs_x27_3323_, v_i_3314_, v___x_3337_);
v_i_3314_ = v___x_3339_;
v_bs_3315_ = v___x_3340_;
goto _start;
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref(v_bs_x27_3323_);
lean_dec(v_v_3321_);
lean_dec_ref(v___x_3309_);
lean_dec_ref(v___x_3307_);
v_a_3380_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3325_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3325_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1___boxed(lean_object* v___x_3388_, lean_object* v___x_3389_, lean_object* v___x_3390_, lean_object* v_insertPos_3391_, lean_object* v_cmdLine_3392_, lean_object* v_ref_3393_, lean_object* v_sz_3394_, lean_object* v_i_3395_, lean_object* v_bs_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
uint8_t v___x_3859__boxed_3400_; size_t v_sz_boxed_3401_; size_t v_i_boxed_3402_; lean_object* v_res_3403_; 
v___x_3859__boxed_3400_ = lean_unbox(v___x_3389_);
v_sz_boxed_3401_ = lean_unbox_usize(v_sz_3394_);
lean_dec(v_sz_3394_);
v_i_boxed_3402_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_res_3403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3388_, v___x_3859__boxed_3400_, v___x_3390_, v_insertPos_3391_, v_cmdLine_3392_, v_ref_3393_, v_sz_boxed_3401_, v_i_boxed_3402_, v_bs_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v_ref_3393_);
lean_dec(v_cmdLine_3392_);
lean_dec(v_insertPos_3391_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(lean_object* v_tacticSeq_3404_, lean_object* v_ref_3405_, lean_object* v_insertPos_3406_, lean_object* v_suggs_3407_, lean_object* v_cmdLine_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = lean_array_get_size(v_suggs_3407_);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = lean_nat_dec_eq(v___x_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v_fileMap_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v_scopes_3421_; lean_object* v___x_3422_; lean_object* v_opts_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; size_t v_sz_3426_; size_t v___x_3427_; lean_object* v___x_3428_; 
v_fileMap_3415_ = lean_ctor_get(v_a_3409_, 1);
v___x_3416_ = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default;
lean_inc_ref_n(v_fileMap_3415_, 2);
v___x_3417_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_computeAppendSep(v_tacticSeq_3404_, v_fileMap_3415_);
lean_inc(v_insertPos_3406_);
v___x_3418_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_mkEmptyRangeStx(v_insertPos_3406_);
v___x_3419_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3420_ = lean_st_ref_get(v_a_3410_);
v_scopes_3421_ = lean_ctor_get(v___x_3420_, 2);
lean_inc(v_scopes_3421_);
lean_dec(v___x_3420_);
v___x_3422_ = l_List_head_x21___redArg(v___x_3419_, v_scopes_3421_);
lean_dec(v_scopes_3421_);
v_opts_3423_ = lean_ctor_get(v___x_3422_, 1);
lean_inc_ref(v_opts_3423_);
lean_dec(v___x_3422_);
v___x_3424_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_debug_autoTry_showEdits;
v___x_3425_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_3423_, v___x_3424_);
lean_dec_ref(v_opts_3423_);
v_sz_3426_ = lean_array_size(v_suggs_3407_);
v___x_3427_ = ((size_t)0ULL);
v___x_3428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions_spec__1(v___x_3417_, v___x_3425_, v_fileMap_3415_, v_insertPos_3406_, v_cmdLine_3408_, v_ref_3405_, v_sz_3426_, v___x_3427_, v_suggs_3407_, v_a_3409_, v_a_3410_);
lean_dec(v_insertPos_3406_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___y_3434_; lean_object* v___x_3435_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
v___x_3430_ = lean_array_get_size(v_a_3429_);
v___x_3431_ = lean_unsigned_to_nat(1u);
v___x_3432_ = lean_nat_dec_eq(v___x_3430_, v___x_3431_);
v___x_3433_ = lean_box(v___x_3432_);
v___y_3434_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___lam__0___boxed), 9, 6);
lean_closure_set(v___y_3434_, 0, v___x_3433_);
lean_closure_set(v___y_3434_, 1, v___x_3418_);
lean_closure_set(v___y_3434_, 2, v_ref_3405_);
lean_closure_set(v___y_3434_, 3, v_a_3429_);
lean_closure_set(v___y_3434_, 4, v___x_3416_);
lean_closure_set(v___y_3434_, 5, v___x_3413_);
v___x_3435_ = l_Lean_Elab_Command_liftCoreM___redArg(v___y_3434_, v_a_3409_, v_a_3410_);
return v___x_3435_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v___x_3418_);
lean_dec(v_ref_3405_);
v_a_3436_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3428_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3428_);
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
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec_ref(v_suggs_3407_);
lean_dec(v_insertPos_3406_);
lean_dec(v_ref_3405_);
v___x_3444_ = lean_box(0);
v___x_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions___boxed(lean_object* v_tacticSeq_3446_, lean_object* v_ref_3447_, lean_object* v_insertPos_3448_, lean_object* v_suggs_3449_, lean_object* v_cmdLine_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3446_, v_ref_3447_, v_insertPos_3448_, v_suggs_3449_, v_cmdLine_3450_, v_a_3451_, v_a_3452_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_cmdLine_3450_);
lean_dec(v_tacticSeq_3446_);
return v_res_3454_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(lean_object* v_x_3455_){
_start:
{
uint8_t v___x_3456_; 
v___x_3456_ = 0;
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0___boxed(lean_object* v_x_3457_){
_start:
{
uint8_t v_res_3458_; lean_object* v_r_3459_; 
v_res_3458_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__0(v_x_3457_);
lean_dec(v_x_3457_);
v_r_3459_ = lean_box(v_res_3458_);
return v_r_3459_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Array_mkArray0___redArg();
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(lean_object* v___f_3480_, lean_object* v_ref_3481_, lean_object* v_goal_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_toCold_3491_; lean_object* v_currRecDepth_3492_; lean_object* v_ref_3493_; uint16_t v_optionFlags_3494_; uint8_t v_suppressElabErrors_3495_; uint8_t v_isRecordingDeps_3496_; uint8_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v_ref_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_toCold_3491_ = lean_ctor_get(v___y_3485_, 0);
v_currRecDepth_3492_ = lean_ctor_get(v___y_3485_, 1);
v_ref_3493_ = lean_ctor_get(v___y_3485_, 2);
v_optionFlags_3494_ = lean_ctor_get_uint16(v___y_3485_, sizeof(void*)*3);
v_suppressElabErrors_3495_ = lean_ctor_get_uint8(v___y_3485_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3496_ = lean_ctor_get_uint8(v___y_3485_, sizeof(void*)*3 + 3);
v___x_3497_ = 0;
v___x_3498_ = l_Lean_SourceInfo_fromRef(v_ref_3493_, v___x_3497_);
v___x_3499_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__1));
v___x_3500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__2));
lean_inc_n(v___x_3498_, 3);
v___x_3501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3498_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__4));
v___x_3503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__6));
v___x_3504_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__7);
v___x_3505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3498_);
lean_ctor_set(v___x_3505_, 1, v___x_3503_);
lean_ctor_set(v___x_3505_, 2, v___x_3504_);
v___x_3506_ = l_Lean_Syntax_node1(v___x_3498_, v___x_3502_, v___x_3505_);
v___x_3507_ = l_Lean_Syntax_node2(v___x_3498_, v___x_3499_, v___x_3501_, v___x_3506_);
v___x_3508_ = lean_box(0);
v___x_3509_ = lean_box(0);
v___x_3510_ = 1;
v___x_3511_ = lean_box(1);
v___x_3512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___closed__5));
v___x_3513_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3513_, 0, v___x_3508_);
lean_ctor_set(v___x_3513_, 1, v___x_3509_);
lean_ctor_set(v___x_3513_, 2, v___x_3508_);
lean_ctor_set(v___x_3513_, 3, v___f_3480_);
lean_ctor_set(v___x_3513_, 4, v___x_3511_);
lean_ctor_set(v___x_3513_, 5, v___x_3511_);
lean_ctor_set(v___x_3513_, 6, v___x_3508_);
lean_ctor_set(v___x_3513_, 7, v___x_3512_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8, v___x_3510_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 1, v___x_3510_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 2, v___x_3510_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 3, v___x_3510_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 4, v___x_3497_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 5, v___x_3497_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 6, v___x_3497_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 7, v___x_3497_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 8, v___x_3510_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 9, v___x_3497_);
lean_ctor_set_uint8(v___x_3513_, sizeof(void*)*8 + 10, v___x_3510_);
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___closed__8));
v___x_3515_ = lean_box(0);
v_ref_3516_ = l_Lean_replaceRef(v_ref_3481_, v_ref_3493_);
lean_inc(v_currRecDepth_3492_);
lean_inc_ref(v_toCold_3491_);
v___x_3517_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3517_, 0, v_toCold_3491_);
lean_ctor_set(v___x_3517_, 1, v_currRecDepth_3492_);
lean_ctor_set(v___x_3517_, 2, v_ref_3516_);
lean_ctor_set_uint16(v___x_3517_, sizeof(void*)*3, v_optionFlags_3494_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*3 + 2, v_suppressElabErrors_3495_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*3 + 3, v_isRecordingDeps_3496_);
v___x_3518_ = l_Lean_Elab_runTactic(v_goal_3482_, v___x_3507_, v___x_3513_, v___x_3514_, v___y_3483_, v___y_3484_, v___x_3517_, v___y_3486_);
lean_dec_ref_known(v___x_3517_, 3);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; 
v_unused_3526_ = lean_ctor_get(v___x_3518_, 0);
lean_dec(v_unused_3526_);
v___x_3520_ = v___x_3518_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_dec(v___x_3518_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3515_);
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3515_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3552_; 
v_a_3527_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3529_ = v___x_3518_;
v_isShared_3530_ = v_isSharedCheck_3552_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3518_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3552_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
lean_inc(v_a_3527_);
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
uint8_t v___y_3534_; uint8_t v___y_3546_; uint8_t v___x_3549_; 
v___x_3549_ = l_Lean_Exception_isInterrupt(v_a_3527_);
if (v___x_3549_ == 0)
{
uint8_t v___x_3550_; 
lean_inc(v_a_3527_);
v___x_3550_ = l_Lean_Exception_isRuntime(v_a_3527_);
v___y_3546_ = v___x_3550_;
goto v___jp_3545_;
}
else
{
v___y_3546_ = v___x_3549_;
goto v___jp_3545_;
}
v___jp_3533_:
{
if (v___y_3534_ == 0)
{
lean_object* v_options_3535_; uint8_t v_hasTrace_3536_; 
lean_dec_ref(v___x_3532_);
v_options_3535_ = lean_ctor_get(v_toCold_3491_, 2);
v_hasTrace_3536_ = lean_ctor_get_uint8(v_options_3535_, sizeof(void*)*1);
if (v_hasTrace_3536_ == 0)
{
lean_dec(v_a_3527_);
goto v___jp_3488_;
}
else
{
lean_object* v_inheritedTraceOptions_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v_inheritedTraceOptions_3537_ = lean_ctor_get(v_toCold_3491_, 11);
v___x_3538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3539_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3540_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3537_, v_options_3535_, v___x_3539_);
if (v___x_3540_ == 0)
{
lean_dec(v_a_3527_);
goto v___jp_3488_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal___lam__3___closed__1);
v___x_3542_ = l_Lean_Exception_toMessageData(v_a_3527_);
v___x_3543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3541_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__3(v___x_3538_, v___x_3543_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
return v___x_3544_;
}
}
}
else
{
lean_dec(v_a_3527_);
return v___x_3532_;
}
}
v___jp_3545_:
{
if (v___y_3546_ == 0)
{
uint8_t v___x_3547_; 
v___x_3547_ = l_Lean_Exception_isInterrupt(v_a_3527_);
if (v___x_3547_ == 0)
{
uint8_t v___x_3548_; 
lean_inc(v_a_3527_);
v___x_3548_ = l_Lean_Exception_isMaxRecDepth(v_a_3527_);
v___y_3534_ = v___x_3548_;
goto v___jp_3533_;
}
else
{
v___y_3534_ = v___x_3547_;
goto v___jp_3533_;
}
}
else
{
lean_dec(v_a_3527_);
return v___x_3532_;
}
}
}
}
}
v___jp_3488_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
return v___x_3490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed(lean_object* v___f_3553_, lean_object* v_ref_3554_, lean_object* v_goal_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1(v___f_3553_, v_ref_3554_, v_goal_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v_ref_3554_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(lean_object* v_c_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_mctx_3567_; lean_object* v_ref_3568_; lean_object* v_env_3569_; lean_object* v_opts_3570_; lean_object* v_namingCtx_3571_; lean_object* v_goal_3572_; lean_object* v_decls_3573_; lean_object* v___x_3574_; 
v_mctx_3567_ = lean_ctor_get(v_c_3563_, 3);
lean_inc_ref(v_mctx_3567_);
v_ref_3568_ = lean_ctor_get(v_c_3563_, 1);
lean_inc(v_ref_3568_);
v_env_3569_ = lean_ctor_get(v_c_3563_, 2);
lean_inc_ref(v_env_3569_);
v_opts_3570_ = lean_ctor_get(v_c_3563_, 4);
lean_inc_ref(v_opts_3570_);
v_namingCtx_3571_ = lean_ctor_get(v_c_3563_, 5);
lean_inc_ref(v_namingCtx_3571_);
v_goal_3572_ = lean_ctor_get(v_c_3563_, 6);
lean_inc(v_goal_3572_);
lean_dec_ref(v_c_3563_);
v_decls_3573_ = lean_ctor_get(v_mctx_3567_, 5);
v___x_3574_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal_spec__0___redArg(v_decls_3573_, v_goal_3572_);
if (lean_obj_tag(v___x_3574_) == 1)
{
lean_object* v_val_3575_; lean_object* v_lctx_3576_; lean_object* v___f_3577_; lean_object* v___f_3578_; lean_object* v___x_3579_; 
v_val_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_val_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v_lctx_3576_ = lean_ctor_get(v_val_3575_, 1);
lean_inc_ref(v_lctx_3576_);
lean_dec(v_val_3575_);
v___f_3577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___closed__0));
v___f_3578_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3578_, 0, v___f_3577_);
lean_closure_set(v___f_3578_, 1, v_ref_3568_);
lean_closure_set(v___f_3578_, 2, v_goal_3572_);
v___x_3579_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runMetaMInScope___redArg(v_env_3569_, v_mctx_3567_, v_lctx_3576_, v_opts_3570_, v_namingCtx_3571_, v___f_3578_, v_a_3564_, v_a_3565_);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec(v___x_3574_);
lean_dec(v_goal_3572_);
lean_dec_ref(v_namingCtx_3571_);
lean_dec_ref(v_opts_3570_);
lean_dec_ref(v_env_3569_);
lean_dec(v_ref_3568_);
lean_dec_ref(v_mctx_3567_);
v___x_3580_ = lean_box(0);
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal___boxed(lean_object* v_c_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_c_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
return v_res_3586_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(lean_object* v___x_3587_, lean_object* v_val_3588_, lean_object* v_as_3589_, size_t v_i_3590_, size_t v_stop_3591_){
_start:
{
uint8_t v___x_3596_; uint8_t v___x_3597_; 
v___x_3596_ = 0;
v___x_3597_ = lean_usize_dec_eq(v_i_3590_, v_stop_3591_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v_pos_3599_; uint8_t v_severity_3600_; lean_object* v_data_3601_; lean_object* v___f_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; uint8_t v___y_3607_; 
v___x_3598_ = lean_array_uget_borrowed(v_as_3589_, v_i_3590_);
v_pos_3599_ = lean_ctor_get(v___x_3598_, 1);
v_severity_3600_ = lean_ctor_get_uint8(v___x_3598_, sizeof(void*)*5 + 1);
v_data_3601_ = lean_ctor_get(v___x_3598_, 4);
v___f_3602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__0));
v___x_3603_ = 1;
lean_inc_ref(v_pos_3599_);
v___x_3604_ = l_Lean_FileMap_ofPosition(v___x_3587_, v_pos_3599_);
v___x_3605_ = l_Lean_Syntax_Range_contains(v_val_3588_, v___x_3604_, v___x_3603_);
lean_dec(v___x_3604_);
if (v_severity_3600_ == 2)
{
v___y_3607_ = v___x_3603_;
goto v___jp_3606_;
}
else
{
v___y_3607_ = v___x_3596_;
goto v___jp_3606_;
}
v___jp_3606_:
{
if (v___x_3605_ == 0)
{
goto v___jp_3592_;
}
else
{
if (v___y_3607_ == 0)
{
goto v___jp_3592_;
}
else
{
uint8_t v___x_3608_; 
lean_inc(v_data_3601_);
v___x_3608_ = l_Lean_MessageData_hasTag(v___f_3602_, v_data_3601_);
if (v___x_3608_ == 0)
{
return v___x_3603_;
}
else
{
goto v___jp_3592_;
}
}
}
}
}
else
{
return v___x_3596_;
}
v___jp_3592_:
{
size_t v___x_3593_; size_t v___x_3594_; 
v___x_3593_ = ((size_t)1ULL);
v___x_3594_ = lean_usize_add(v_i_3590_, v___x_3593_);
v_i_3590_ = v___x_3594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1___boxed(lean_object* v___x_3609_, lean_object* v_val_3610_, lean_object* v_as_3611_, lean_object* v_i_3612_, lean_object* v_stop_3613_){
_start:
{
size_t v_i_boxed_3614_; size_t v_stop_boxed_3615_; uint8_t v_res_3616_; lean_object* v_r_3617_; 
v_i_boxed_3614_ = lean_unbox_usize(v_i_3612_);
lean_dec(v_i_3612_);
v_stop_boxed_3615_ = lean_unbox_usize(v_stop_3613_);
lean_dec(v_stop_3613_);
v_res_3616_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3609_, v_val_3610_, v_as_3611_, v_i_boxed_3614_, v_stop_boxed_3615_);
lean_dec_ref(v_as_3611_);
lean_dec_ref(v_val_3610_);
lean_dec_ref(v___x_3609_);
v_r_3617_ = lean_box(v_res_3616_);
return v_r_3617_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(lean_object* v___x_3618_, lean_object* v_val_3619_, lean_object* v_x_3620_){
_start:
{
if (lean_obj_tag(v_x_3620_) == 0)
{
lean_object* v_cs_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v_cs_3621_ = lean_ctor_get(v_x_3620_, 0);
v___x_3622_ = lean_unsigned_to_nat(0u);
v___x_3623_ = lean_array_get_size(v_cs_3621_);
v___x_3624_ = lean_nat_dec_lt(v___x_3622_, v___x_3623_);
if (v___x_3624_ == 0)
{
return v___x_3624_;
}
else
{
if (v___x_3624_ == 0)
{
return v___x_3624_;
}
else
{
size_t v___x_3625_; size_t v___x_3626_; uint8_t v___x_3627_; 
v___x_3625_ = ((size_t)0ULL);
v___x_3626_ = lean_usize_of_nat(v___x_3623_);
v___x_3627_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3618_, v_val_3619_, v_cs_3621_, v___x_3625_, v___x_3626_);
return v___x_3627_;
}
}
}
else
{
lean_object* v_vs_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; uint8_t v___x_3631_; 
v_vs_3628_ = lean_ctor_get(v_x_3620_, 0);
v___x_3629_ = lean_unsigned_to_nat(0u);
v___x_3630_ = lean_array_get_size(v_vs_3628_);
v___x_3631_ = lean_nat_dec_lt(v___x_3629_, v___x_3630_);
if (v___x_3631_ == 0)
{
return v___x_3631_;
}
else
{
if (v___x_3631_ == 0)
{
return v___x_3631_;
}
else
{
size_t v___x_3632_; size_t v___x_3633_; uint8_t v___x_3634_; 
v___x_3632_ = ((size_t)0ULL);
v___x_3633_ = lean_usize_of_nat(v___x_3630_);
v___x_3634_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3618_, v_val_3619_, v_vs_3628_, v___x_3632_, v___x_3633_);
return v___x_3634_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(lean_object* v___x_3635_, lean_object* v_val_3636_, lean_object* v_as_3637_, size_t v_i_3638_, size_t v_stop_3639_){
_start:
{
uint8_t v___x_3640_; 
v___x_3640_ = lean_usize_dec_eq(v_i_3638_, v_stop_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3641_ = lean_array_uget_borrowed(v_as_3637_, v_i_3638_);
v___x_3642_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3635_, v_val_3636_, v___x_3641_);
if (v___x_3642_ == 0)
{
size_t v___x_3643_; size_t v___x_3644_; 
v___x_3643_ = ((size_t)1ULL);
v___x_3644_ = lean_usize_add(v_i_3638_, v___x_3643_);
v_i_3638_ = v___x_3644_;
goto _start;
}
else
{
return v___x_3642_;
}
}
else
{
uint8_t v___x_3646_; 
v___x_3646_ = 0;
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3647_, lean_object* v_val_3648_, lean_object* v_as_3649_, lean_object* v_i_3650_, lean_object* v_stop_3651_){
_start:
{
size_t v_i_boxed_3652_; size_t v_stop_boxed_3653_; uint8_t v_res_3654_; lean_object* v_r_3655_; 
v_i_boxed_3652_ = lean_unbox_usize(v_i_3650_);
lean_dec(v_i_3650_);
v_stop_boxed_3653_ = lean_unbox_usize(v_stop_3651_);
lean_dec(v_stop_3651_);
v_res_3654_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0_spec__1(v___x_3647_, v_val_3648_, v_as_3649_, v_i_boxed_3652_, v_stop_boxed_3653_);
lean_dec_ref(v_as_3649_);
lean_dec_ref(v_val_3648_);
lean_dec_ref(v___x_3647_);
v_r_3655_ = lean_box(v_res_3654_);
return v_r_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0___boxed(lean_object* v___x_3656_, lean_object* v_val_3657_, lean_object* v_x_3658_){
_start:
{
uint8_t v_res_3659_; lean_object* v_r_3660_; 
v_res_3659_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3656_, v_val_3657_, v_x_3658_);
lean_dec_ref(v_x_3658_);
lean_dec_ref(v_val_3657_);
lean_dec_ref(v___x_3656_);
v_r_3660_ = lean_box(v_res_3659_);
return v_r_3660_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(lean_object* v___x_3661_, lean_object* v_val_3662_, lean_object* v_t_3663_){
_start:
{
lean_object* v_root_3664_; lean_object* v_tail_3665_; uint8_t v___x_3666_; 
v_root_3664_ = lean_ctor_get(v_t_3663_, 0);
v_tail_3665_ = lean_ctor_get(v_t_3663_, 1);
v___x_3666_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__0(v___x_3661_, v_val_3662_, v_root_3664_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3667_ = lean_unsigned_to_nat(0u);
v___x_3668_ = lean_array_get_size(v_tail_3665_);
v___x_3669_ = lean_nat_dec_lt(v___x_3667_, v___x_3668_);
if (v___x_3669_ == 0)
{
return v___x_3669_;
}
else
{
if (v___x_3669_ == 0)
{
return v___x_3669_;
}
else
{
size_t v___x_3670_; size_t v___x_3671_; uint8_t v___x_3672_; 
v___x_3670_ = ((size_t)0ULL);
v___x_3671_ = lean_usize_of_nat(v___x_3668_);
v___x_3672_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0_spec__1(v___x_3661_, v_val_3662_, v_tail_3665_, v___x_3670_, v___x_3671_);
return v___x_3672_;
}
}
}
else
{
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0___boxed(lean_object* v___x_3673_, lean_object* v_val_3674_, lean_object* v_t_3675_){
_start:
{
uint8_t v_res_3676_; lean_object* v_r_3677_; 
v_res_3676_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v___x_3673_, v_val_3674_, v_t_3675_);
lean_dec_ref(v_t_3675_);
lean_dec_ref(v_val_3674_);
lean_dec_ref(v___x_3673_);
v_r_3677_ = lean_box(v_res_3676_);
return v_r_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(lean_object* v_stx_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_){
_start:
{
uint8_t v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = 0;
v___x_3683_ = l_Lean_Syntax_getRange_x3f(v_stx_3678_, v___x_3682_);
if (lean_obj_tag(v___x_3683_) == 1)
{
lean_object* v_val_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3697_; 
v_val_3684_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3686_ = v___x_3683_;
v_isShared_3687_ = v_isSharedCheck_3697_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_val_3684_);
lean_dec(v___x_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3697_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v_fileMap_3688_; lean_object* v___x_3689_; lean_object* v_messages_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3695_; 
v_fileMap_3688_ = lean_ctor_get(v_a_3679_, 1);
v___x_3689_ = lean_st_ref_get(v_a_3680_);
v_messages_3690_ = lean_ctor_get(v___x_3689_, 1);
lean_inc_ref(v_messages_3690_);
lean_dec(v___x_3689_);
v___x_3691_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_3690_);
v___x_3692_ = l_Lean_PersistentArray_anyM___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError_spec__0(v_fileMap_3688_, v_val_3684_, v___x_3691_);
lean_dec_ref(v___x_3691_);
lean_dec(v_val_3684_);
v___x_3693_ = lean_box(v___x_3692_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set_tag(v___x_3686_, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3693_);
v___x_3695_ = v___x_3686_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec(v___x_3683_);
v___x_3698_ = lean_box(v___x_3682_);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError___boxed(lean_object* v_stx_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_3700_, v_a_3701_, v_a_3702_);
lean_dec(v_a_3702_);
lean_dec_ref(v_a_3701_);
lean_dec(v_stx_3700_);
return v_res_3704_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(lean_object* v_tree_3705_, lean_object* v_fileMap_3706_, lean_object* v_c_3707_){
_start:
{
lean_object* v___y_3709_; lean_object* v_kind_3713_; lean_object* v_ref_3714_; lean_object* v___y_3716_; 
v_kind_3713_ = lean_ctor_get(v_c_3707_, 0);
lean_inc(v_kind_3713_);
v_ref_3714_ = lean_ctor_get(v_c_3707_, 1);
lean_inc(v_ref_3714_);
lean_dec_ref(v_c_3707_);
if (lean_obj_tag(v_kind_3713_) == 0)
{
lean_object* v_insertPos_3732_; 
lean_dec(v_ref_3714_);
v_insertPos_3732_ = lean_ctor_get(v_kind_3713_, 1);
lean_inc(v_insertPos_3732_);
v___y_3716_ = v_insertPos_3732_;
goto v___jp_3715_;
}
else
{
uint8_t v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = 0;
v___x_3734_ = l_Lean_Syntax_getPos_x3f(v_ref_3714_, v___x_3733_);
lean_dec(v_ref_3714_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_unsigned_to_nat(0u);
v___y_3716_ = v___x_3735_;
goto v___jp_3715_;
}
else
{
lean_object* v_val_3736_; 
v_val_3736_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_val_3736_);
lean_dec_ref_known(v___x_3734_, 1);
v___y_3716_ = v_val_3736_;
goto v___jp_3715_;
}
}
v___jp_3708_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3710_ = l_List_lengthTR___redArg(v___y_3709_);
lean_dec(v___y_3709_);
v___x_3711_ = lean_unsigned_to_nat(1u);
v___x_3712_ = lean_nat_dec_eq(v___x_3710_, v___x_3711_);
lean_dec(v___x_3710_);
return v___x_3712_;
}
v___jp_3715_:
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_Elab_InfoTree_goalsAt_x3f(v_fileMap_3706_, v_tree_3705_, v___y_3716_);
if (lean_obj_tag(v___x_3717_) == 1)
{
lean_object* v_tail_3718_; 
v_tail_3718_ = lean_ctor_get(v___x_3717_, 1);
lean_inc(v_tail_3718_);
if (lean_obj_tag(v_tail_3718_) == 0)
{
if (lean_obj_tag(v_kind_3713_) == 0)
{
lean_object* v_head_3719_; lean_object* v_tacticSeq_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; 
v_head_3719_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_head_3719_);
lean_dec_ref_known(v___x_3717_, 2);
v_tacticSeq_3720_ = lean_ctor_get(v_kind_3713_, 0);
lean_inc(v_tacticSeq_3720_);
lean_dec_ref_known(v_kind_3713_, 2);
v___x_3721_ = 0;
v___x_3722_ = l_Lean_Syntax_getPos_x3f(v_tacticSeq_3720_, v___x_3721_);
lean_dec(v_tacticSeq_3720_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_tacticInfo_3723_; lean_object* v_goalsBefore_3724_; 
v_tacticInfo_3723_ = lean_ctor_get(v_head_3719_, 1);
lean_inc_ref(v_tacticInfo_3723_);
lean_dec(v_head_3719_);
v_goalsBefore_3724_ = lean_ctor_get(v_tacticInfo_3723_, 2);
lean_inc(v_goalsBefore_3724_);
lean_dec_ref(v_tacticInfo_3723_);
v___y_3709_ = v_goalsBefore_3724_;
goto v___jp_3708_;
}
else
{
lean_object* v_tacticInfo_3725_; lean_object* v_goalsAfter_3726_; 
lean_dec_ref_known(v___x_3722_, 1);
v_tacticInfo_3725_ = lean_ctor_get(v_head_3719_, 1);
lean_inc_ref(v_tacticInfo_3725_);
lean_dec(v_head_3719_);
v_goalsAfter_3726_ = lean_ctor_get(v_tacticInfo_3725_, 4);
lean_inc(v_goalsAfter_3726_);
lean_dec_ref(v_tacticInfo_3725_);
v___y_3709_ = v_goalsAfter_3726_;
goto v___jp_3708_;
}
}
else
{
lean_object* v_head_3727_; lean_object* v_tacticInfo_3728_; lean_object* v_goalsBefore_3729_; 
v_head_3727_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_head_3727_);
lean_dec_ref_known(v___x_3717_, 2);
v_tacticInfo_3728_ = lean_ctor_get(v_head_3727_, 1);
lean_inc_ref(v_tacticInfo_3728_);
lean_dec(v_head_3727_);
v_goalsBefore_3729_ = lean_ctor_get(v_tacticInfo_3728_, 2);
lean_inc(v_goalsBefore_3729_);
lean_dec_ref(v_tacticInfo_3728_);
v___y_3709_ = v_goalsBefore_3729_;
goto v___jp_3708_;
}
}
else
{
uint8_t v___x_3730_; 
lean_dec_ref_known(v___x_3717_, 2);
lean_dec(v_tail_3718_);
lean_dec(v_kind_3713_);
v___x_3730_ = 0;
return v___x_3730_;
}
}
else
{
uint8_t v___x_3731_; 
lean_dec(v___x_3717_);
lean_dec(v_kind_3713_);
v___x_3731_ = 0;
return v___x_3731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos___boxed(lean_object* v_tree_3737_, lean_object* v_fileMap_3738_, lean_object* v_c_3739_){
_start:
{
uint8_t v_res_3740_; lean_object* v_r_3741_; 
v_res_3740_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3737_, v_fileMap_3738_, v_c_3739_);
v_r_3741_ = lean_box(v_res_3740_);
return v_r_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3744_; lean_object* v_infoState_3745_; lean_object* v_trees_3746_; lean_object* v___x_3747_; 
v___x_3744_ = lean_st_ref_get(v___y_3742_);
v_infoState_3745_ = lean_ctor_get(v___x_3744_, 8);
lean_inc_ref(v_infoState_3745_);
lean_dec(v___x_3744_);
v_trees_3746_ = lean_ctor_get(v_infoState_3745_, 2);
lean_inc_ref(v_trees_3746_);
lean_dec_ref(v_infoState_3745_);
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v_trees_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg___boxed(lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3748_);
lean_dec(v___y_3748_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___boxed(lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0(v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3758_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__0));
v___x_3761_ = l_Lean_stringToMessageData(v___x_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(lean_object* v_tree_3762_, lean_object* v___x_3763_, lean_object* v___x_3764_, lean_object* v_as_3765_, size_t v_sz_3766_, size_t v_i_3767_, lean_object* v_b_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_a_3773_; uint8_t v___x_3777_; 
v___x_3777_ = lean_usize_dec_lt(v_i_3767_, v_sz_3766_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; 
lean_dec_ref(v___x_3763_);
lean_dec_ref(v_tree_3762_);
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v_b_3768_);
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; lean_object* v_a_3780_; uint8_t v___x_3781_; 
v___x_3779_ = lean_box(0);
v_a_3780_ = lean_array_uget_borrowed(v_as_3765_, v_i_3767_);
lean_inc(v_a_3780_);
lean_inc_ref(v___x_3763_);
lean_inc_ref(v_tree_3762_);
v___x_3781_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_singleGoalAtInsertPos(v_tree_3762_, v___x_3763_, v_a_3780_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v_scopes_3787_; lean_object* v___x_3788_; lean_object* v_opts_3789_; uint8_t v_hasTrace_3790_; 
v___x_3782_ = l_Lean_inheritedTraceOptions;
v___x_3783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_3784_ = lean_st_ref_get(v___x_3782_);
v___x_3785_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3786_ = lean_st_ref_get(v___y_3770_);
v_scopes_3787_ = lean_ctor_get(v___x_3786_, 2);
lean_inc(v_scopes_3787_);
lean_dec(v___x_3786_);
v___x_3788_ = l_List_head_x21___redArg(v___x_3785_, v_scopes_3787_);
lean_dec(v_scopes_3787_);
v_opts_3789_ = lean_ctor_get(v___x_3788_, 1);
lean_inc_ref(v_opts_3789_);
lean_dec(v___x_3788_);
v_hasTrace_3790_ = lean_ctor_get_uint8(v_opts_3789_, sizeof(void*)*1);
if (v_hasTrace_3790_ == 0)
{
lean_dec_ref(v_opts_3789_);
lean_dec(v___x_3784_);
v_a_3773_ = v___x_3779_;
goto v___jp_3772_;
}
else
{
lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3791_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3792_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3784_, v_opts_3789_, v___x_3791_);
lean_dec_ref(v_opts_3789_);
lean_dec(v___x_3784_);
if (v___x_3792_ == 0)
{
v_a_3773_ = v___x_3779_;
goto v___jp_3772_;
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___closed__1);
v___x_3794_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3783_, v___x_3793_, v___y_3769_, v___y_3770_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_dec_ref_known(v___x_3794_, 1);
v_a_3773_ = v___x_3779_;
goto v___jp_3772_;
}
else
{
lean_dec_ref(v___x_3763_);
lean_dec_ref(v_tree_3762_);
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_kind_3795_; 
v_kind_3795_ = lean_ctor_get(v_a_3780_, 0);
if (lean_obj_tag(v_kind_3795_) == 0)
{
lean_object* v_ref_3796_; lean_object* v_tacticSeq_3797_; lean_object* v_insertPos_3798_; lean_object* v___x_3799_; 
v_ref_3796_ = lean_ctor_get(v_a_3780_, 1);
v_tacticSeq_3797_ = lean_ctor_get(v_kind_3795_, 0);
v_insertPos_3798_ = lean_ctor_get(v_kind_3795_, 1);
lean_inc(v_a_3780_);
v___x_3799_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectSuggestionsForGoal(v_a_3780_, v___y_3769_, v___y_3770_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3801_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3799_, 1);
lean_inc(v_insertPos_3798_);
lean_inc(v_ref_3796_);
v___x_3801_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_emitAppendSuggestions(v_tacticSeq_3797_, v_ref_3796_, v_insertPos_3798_, v_a_3800_, v___x_3764_, v___y_3769_, v___y_3770_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_dec_ref_known(v___x_3801_, 1);
v_a_3773_ = v___x_3779_;
goto v___jp_3772_;
}
else
{
lean_dec_ref(v___x_3763_);
lean_dec_ref(v_tree_3762_);
return v___x_3801_;
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v___x_3763_);
lean_dec_ref(v_tree_3762_);
v_a_3802_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3799_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3799_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v___x_3810_; 
lean_inc(v_a_3780_);
v___x_3810_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_runReplaceTryOnGoal(v_a_3780_, v___y_3769_, v___y_3770_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_dec_ref_known(v___x_3810_, 1);
v_a_3773_ = v___x_3779_;
goto v___jp_3772_;
}
else
{
lean_dec_ref(v___x_3763_);
lean_dec_ref(v_tree_3762_);
return v___x_3810_;
}
}
}
}
v___jp_3772_:
{
size_t v___x_3774_; size_t v___x_3775_; 
v___x_3774_ = ((size_t)1ULL);
v___x_3775_ = lean_usize_add(v_i_3767_, v___x_3774_);
v_i_3767_ = v___x_3775_;
v_b_3768_ = v_a_3773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1___boxed(lean_object* v_tree_3811_, lean_object* v___x_3812_, lean_object* v___x_3813_, lean_object* v_as_3814_, lean_object* v_sz_3815_, lean_object* v_i_3816_, lean_object* v_b_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
size_t v_sz_boxed_3821_; size_t v_i_boxed_3822_; lean_object* v_res_3823_; 
v_sz_boxed_3821_ = lean_unbox_usize(v_sz_3815_);
lean_dec(v_sz_3815_);
v_i_boxed_3822_ = lean_unbox_usize(v_i_3816_);
lean_dec(v_i_3816_);
v_res_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_tree_3811_, v___x_3812_, v___x_3813_, v_as_3814_, v_sz_boxed_3821_, v_i_boxed_3822_, v_b_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec_ref(v_as_3814_);
lean_dec(v___x_3813_);
return v_res_3823_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__1));
v___x_3829_ = l_Lean_stringToMessageData(v___x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(lean_object* v_stx_3830_, lean_object* v___x_3831_, lean_object* v___x_3832_, lean_object* v___x_3833_, lean_object* v___x_3834_, lean_object* v_as_3835_, size_t v_sz_3836_, size_t v_i_3837_, lean_object* v_b_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
uint8_t v___x_3842_; 
v___x_3842_ = lean_usize_dec_lt(v_i_3837_, v_sz_3836_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; 
lean_dec_ref(v___x_3833_);
lean_dec(v_stx_3830_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_b_3838_);
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_a_3847_; lean_object* v___x_3848_; 
lean_dec_ref(v_b_3838_);
v___x_3844_ = lean_box(0);
v___x_3845_ = l_Lean_inheritedTraceOptions;
v___x_3846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3847_ = lean_array_uget_borrowed(v_as_3835_, v_i_3837_);
lean_inc(v_a_3847_);
lean_inc(v_stx_3830_);
v___x_3848_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3830_, v___x_3831_, v_a_3847_, v___x_3832_, v___y_3839_, v___y_3840_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v_scopes_3871_; lean_object* v___x_3872_; lean_object* v_opts_3873_; uint8_t v_hasTrace_3874_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
v___x_3868_ = lean_st_ref_get(v___x_3845_);
v___x_3869_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3870_ = lean_st_ref_get(v___y_3840_);
v_scopes_3871_ = lean_ctor_get(v___x_3870_, 2);
lean_inc(v_scopes_3871_);
lean_dec(v___x_3870_);
v___x_3872_ = l_List_head_x21___redArg(v___x_3869_, v_scopes_3871_);
lean_dec(v_scopes_3871_);
v_opts_3873_ = lean_ctor_get(v___x_3872_, 1);
lean_inc_ref(v_opts_3873_);
lean_dec(v___x_3872_);
v_hasTrace_3874_ = lean_ctor_get_uint8(v_opts_3873_, sizeof(void*)*1);
if (v_hasTrace_3874_ == 0)
{
lean_dec_ref(v_opts_3873_);
lean_dec(v___x_3868_);
v___y_3851_ = v___y_3839_;
v___y_3852_ = v___y_3840_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3875_; uint8_t v___x_3876_; 
v___x_3875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3876_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3868_, v_opts_3873_, v___x_3875_);
lean_dec_ref(v_opts_3873_);
lean_dec(v___x_3868_);
if (v___x_3876_ == 0)
{
v___y_3851_ = v___y_3839_;
v___y_3852_ = v___y_3840_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3878_ = lean_array_get_size(v_a_3849_);
v___x_3879_ = l_Nat_reprFast(v___x_3878_);
v___x_3880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
v___x_3881_ = l_Lean_MessageData_ofFormat(v___x_3880_);
v___x_3882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3877_);
lean_ctor_set(v___x_3882_, 1, v___x_3881_);
v___x_3883_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3846_, v___x_3882_, v___y_3839_, v___y_3840_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_dec_ref_known(v___x_3883_, 1);
v___y_3851_ = v___y_3839_;
v___y_3852_ = v___y_3840_;
goto v___jp_3850_;
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_a_3849_);
lean_dec_ref(v___x_3833_);
lean_dec(v_stx_3830_);
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3883_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3883_);
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
}
v___jp_3850_:
{
size_t v_sz_3853_; size_t v___x_3854_; lean_object* v___x_3855_; 
v_sz_3853_ = lean_array_size(v_a_3849_);
v___x_3854_ = ((size_t)0ULL);
lean_inc_ref(v___x_3833_);
lean_inc(v_a_3847_);
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3847_, v___x_3833_, v___x_3834_, v_a_3849_, v_sz_3853_, v___x_3854_, v___x_3844_, v___y_3851_, v___y_3852_);
lean_dec(v_a_3849_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; size_t v___x_3857_; size_t v___x_3858_; 
lean_dec_ref_known(v___x_3855_, 1);
v___x_3856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3857_ = ((size_t)1ULL);
v___x_3858_ = lean_usize_add(v_i_3837_, v___x_3857_);
v_i_3837_ = v___x_3858_;
v_b_3838_ = v___x_3856_;
goto _start;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v___x_3833_);
lean_dec(v_stx_3830_);
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
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref(v___x_3833_);
lean_dec(v_stx_3830_);
v_a_3892_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3848_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3848_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___boxed(lean_object* v_stx_3900_, lean_object* v___x_3901_, lean_object* v___x_3902_, lean_object* v___x_3903_, lean_object* v___x_3904_, lean_object* v_as_3905_, lean_object* v_sz_3906_, lean_object* v_i_3907_, lean_object* v_b_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
size_t v_sz_boxed_3912_; size_t v_i_boxed_3913_; lean_object* v_res_3914_; 
v_sz_boxed_3912_ = lean_unbox_usize(v_sz_3906_);
lean_dec(v_sz_3906_);
v_i_boxed_3913_ = lean_unbox_usize(v_i_3907_);
lean_dec(v_i_3907_);
v_res_3914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3900_, v___x_3901_, v___x_3902_, v___x_3903_, v___x_3904_, v_as_3905_, v_sz_boxed_3912_, v_i_boxed_3913_, v_b_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec_ref(v_as_3905_);
lean_dec(v___x_3904_);
lean_dec_ref(v___x_3902_);
lean_dec_ref(v___x_3901_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(lean_object* v_stx_3915_, lean_object* v___x_3916_, lean_object* v___x_3917_, lean_object* v___x_3918_, lean_object* v___x_3919_, lean_object* v_as_3920_, size_t v_sz_3921_, size_t v_i_3922_, lean_object* v_b_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
uint8_t v___x_3927_; 
v___x_3927_ = lean_usize_dec_lt(v_i_3922_, v_sz_3921_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3928_; 
lean_dec_ref(v___x_3918_);
lean_dec(v_stx_3915_);
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v_b_3923_);
return v___x_3928_;
}
else
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v_a_3932_; lean_object* v___x_3933_; 
lean_dec_ref(v_b_3923_);
v___x_3929_ = lean_box(0);
v___x_3930_ = l_Lean_inheritedTraceOptions;
v___x_3931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_3932_ = lean_array_uget_borrowed(v_as_3920_, v_i_3922_);
lean_inc(v_a_3932_);
lean_inc(v_stx_3915_);
v___x_3933_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_3915_, v___x_3916_, v_a_3932_, v___x_3917_, v___y_3924_, v___y_3925_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v_scopes_3956_; lean_object* v___x_3957_; lean_object* v_opts_3958_; uint8_t v_hasTrace_3959_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3933_, 1);
v___x_3953_ = lean_st_ref_get(v___x_3930_);
v___x_3954_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3955_ = lean_st_ref_get(v___y_3925_);
v_scopes_3956_ = lean_ctor_get(v___x_3955_, 2);
lean_inc(v_scopes_3956_);
lean_dec(v___x_3955_);
v___x_3957_ = l_List_head_x21___redArg(v___x_3954_, v_scopes_3956_);
lean_dec(v_scopes_3956_);
v_opts_3958_ = lean_ctor_get(v___x_3957_, 1);
lean_inc_ref(v_opts_3958_);
lean_dec(v___x_3957_);
v_hasTrace_3959_ = lean_ctor_get_uint8(v_opts_3958_, sizeof(void*)*1);
if (v_hasTrace_3959_ == 0)
{
lean_dec_ref(v_opts_3958_);
lean_dec(v___x_3953_);
v___y_3936_ = v___y_3924_;
v___y_3937_ = v___y_3925_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3960_; uint8_t v___x_3961_; 
v___x_3960_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_3961_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3953_, v_opts_3958_, v___x_3960_);
lean_dec_ref(v_opts_3958_);
lean_dec(v___x_3953_);
if (v___x_3961_ == 0)
{
v___y_3936_ = v___y_3924_;
v___y_3937_ = v___y_3925_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3962_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_3963_ = lean_array_get_size(v_a_3934_);
v___x_3964_ = l_Nat_reprFast(v___x_3963_);
v___x_3965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
v___x_3966_ = l_Lean_MessageData_ofFormat(v___x_3965_);
v___x_3967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3962_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_3931_, v___x_3967_, v___y_3924_, v___y_3925_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_dec_ref_known(v___x_3968_, 1);
v___y_3936_ = v___y_3924_;
v___y_3937_ = v___y_3925_;
goto v___jp_3935_;
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec(v_a_3934_);
lean_dec_ref(v___x_3918_);
lean_dec(v_stx_3915_);
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3968_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
}
v___jp_3935_:
{
size_t v_sz_3938_; size_t v___x_3939_; lean_object* v___x_3940_; 
v_sz_3938_ = lean_array_size(v_a_3934_);
v___x_3939_ = ((size_t)0ULL);
lean_inc_ref(v___x_3918_);
lean_inc(v_a_3932_);
v___x_3940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_3932_, v___x_3918_, v___x_3919_, v_a_3934_, v_sz_3938_, v___x_3939_, v___x_3929_, v___y_3936_, v___y_3937_);
lean_dec(v_a_3934_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; lean_object* v___x_3944_; 
lean_dec_ref_known(v___x_3940_, 1);
v___x_3941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__0));
v___x_3942_ = ((size_t)1ULL);
v___x_3943_ = lean_usize_add(v_i_3922_, v___x_3942_);
v___x_3944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6(v_stx_3915_, v___x_3916_, v___x_3917_, v___x_3918_, v___x_3919_, v_as_3920_, v_sz_3921_, v___x_3943_, v___x_3941_, v___y_3924_, v___y_3925_);
return v___x_3944_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec_ref(v___x_3918_);
lean_dec(v_stx_3915_);
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
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v___x_3918_);
lean_dec(v_stx_3915_);
v_a_3977_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3933_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3933_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3___boxed(lean_object* v_stx_3985_, lean_object* v___x_3986_, lean_object* v___x_3987_, lean_object* v___x_3988_, lean_object* v___x_3989_, lean_object* v_as_3990_, lean_object* v_sz_3991_, lean_object* v_i_3992_, lean_object* v_b_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
size_t v_sz_boxed_3997_; size_t v_i_boxed_3998_; lean_object* v_res_3999_; 
v_sz_boxed_3997_ = lean_unbox_usize(v_sz_3991_);
lean_dec(v_sz_3991_);
v_i_boxed_3998_ = lean_unbox_usize(v_i_3992_);
lean_dec(v_i_3992_);
v_res_3999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_3985_, v___x_3986_, v___x_3987_, v___x_3988_, v___x_3989_, v_as_3990_, v_sz_boxed_3997_, v_i_boxed_3998_, v_b_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec_ref(v_as_3990_);
lean_dec(v___x_3989_);
lean_dec_ref(v___x_3987_);
lean_dec_ref(v___x_3986_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(lean_object* v_stx_4003_, lean_object* v___x_4004_, lean_object* v___x_4005_, lean_object* v___x_4006_, lean_object* v___x_4007_, lean_object* v_as_4008_, size_t v_sz_4009_, size_t v_i_4010_, lean_object* v_b_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
uint8_t v___x_4015_; 
v___x_4015_ = lean_usize_dec_lt(v_i_4010_, v_sz_4009_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; 
lean_dec_ref(v___x_4006_);
lean_dec(v_stx_4003_);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v_b_4011_);
return v___x_4016_;
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v_a_4020_; lean_object* v___x_4021_; 
lean_dec_ref(v_b_4011_);
v___x_4017_ = lean_box(0);
v___x_4018_ = l_Lean_inheritedTraceOptions;
v___x_4019_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v_a_4020_ = lean_array_uget_borrowed(v_as_4008_, v_i_4010_);
lean_inc(v_a_4020_);
lean_inc(v_stx_4003_);
v___x_4021_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints(v_stx_4003_, v___x_4004_, v_a_4020_, v___x_4005_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v_scopes_4044_; lean_object* v___x_4045_; lean_object* v_opts_4046_; uint8_t v_hasTrace_4047_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v___x_4041_ = lean_st_ref_get(v___x_4018_);
v___x_4042_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4043_ = lean_st_ref_get(v___y_4013_);
v_scopes_4044_ = lean_ctor_get(v___x_4043_, 2);
lean_inc(v_scopes_4044_);
lean_dec(v___x_4043_);
v___x_4045_ = l_List_head_x21___redArg(v___x_4042_, v_scopes_4044_);
lean_dec(v_scopes_4044_);
v_opts_4046_ = lean_ctor_get(v___x_4045_, 1);
lean_inc_ref(v_opts_4046_);
lean_dec(v___x_4045_);
v_hasTrace_4047_ = lean_ctor_get_uint8(v_opts_4046_, sizeof(void*)*1);
if (v_hasTrace_4047_ == 0)
{
lean_dec_ref(v_opts_4046_);
lean_dec(v___x_4041_);
v___y_4024_ = v___y_4012_;
v___y_4025_ = v___y_4013_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4048_; uint8_t v___x_4049_; 
v___x_4048_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4049_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4041_, v_opts_4046_, v___x_4048_);
lean_dec_ref(v_opts_4046_);
lean_dec(v___x_4041_);
if (v___x_4049_ == 0)
{
v___y_4024_ = v___y_4012_;
v___y_4025_ = v___y_4013_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4050_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3_spec__6___closed__2);
v___x_4051_ = lean_array_get_size(v_a_4022_);
v___x_4052_ = l_Nat_reprFast(v___x_4051_);
v___x_4053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
v___x_4054_ = l_Lean_MessageData_ofFormat(v___x_4053_);
v___x_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4050_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4019_, v___x_4055_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_dec_ref_known(v___x_4056_, 1);
v___y_4024_ = v___y_4012_;
v___y_4025_ = v___y_4013_;
goto v___jp_4023_;
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_a_4022_);
lean_dec_ref(v___x_4006_);
lean_dec(v_stx_4003_);
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4056_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4056_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
v___jp_4023_:
{
size_t v_sz_4026_; size_t v___x_4027_; lean_object* v___x_4028_; 
v_sz_4026_ = lean_array_size(v_a_4022_);
v___x_4027_ = ((size_t)0ULL);
lean_inc_ref(v___x_4006_);
lean_inc(v_a_4020_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__1(v_a_4020_, v___x_4006_, v___x_4007_, v_a_4022_, v_sz_4026_, v___x_4027_, v___x_4017_, v___y_4024_, v___y_4025_);
lean_dec(v_a_4022_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v___x_4029_; size_t v___x_4030_; size_t v___x_4031_; 
lean_dec_ref_known(v___x_4028_, 1);
v___x_4029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4030_ = ((size_t)1ULL);
v___x_4031_ = lean_usize_add(v_i_4010_, v___x_4030_);
v_i_4010_ = v___x_4031_;
v_b_4011_ = v___x_4029_;
goto _start;
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v___x_4006_);
lean_dec(v_stx_4003_);
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
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v___x_4006_);
lean_dec(v_stx_4003_);
v_a_4065_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4021_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4021_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___boxed(lean_object* v_stx_4073_, lean_object* v___x_4074_, lean_object* v___x_4075_, lean_object* v___x_4076_, lean_object* v___x_4077_, lean_object* v_as_4078_, lean_object* v_sz_4079_, lean_object* v_i_4080_, lean_object* v_b_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
size_t v_sz_boxed_4085_; size_t v_i_boxed_4086_; lean_object* v_res_4087_; 
v_sz_boxed_4085_ = lean_unbox_usize(v_sz_4079_);
lean_dec(v_sz_4079_);
v_i_boxed_4086_ = lean_unbox_usize(v_i_4080_);
lean_dec(v_i_4080_);
v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4073_, v___x_4074_, v___x_4075_, v___x_4076_, v___x_4077_, v_as_4078_, v_sz_boxed_4085_, v_i_boxed_4086_, v_b_4081_, v___y_4082_, v___y_4083_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec_ref(v_as_4078_);
lean_dec(v___x_4077_);
lean_dec_ref(v___x_4075_);
lean_dec_ref(v___x_4074_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(lean_object* v_stx_4088_, lean_object* v___x_4089_, lean_object* v___x_4090_, lean_object* v___x_4091_, lean_object* v___x_4092_, lean_object* v_as_4093_, size_t v_sz_4094_, size_t v_i_4095_, lean_object* v_b_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
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
lean_object* v___x_4114_; size_t v___x_4115_; size_t v___x_4116_; lean_object* v___x_4117_; 
lean_dec_ref_known(v___x_4113_, 1);
v___x_4114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5___closed__0));
v___x_4115_ = ((size_t)1ULL);
v___x_4116_ = lean_usize_add(v_i_4095_, v___x_4115_);
v___x_4117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4_spec__5(v_stx_4088_, v___x_4089_, v___x_4090_, v___x_4091_, v___x_4092_, v_as_4093_, v_sz_4094_, v___x_4116_, v___x_4114_, v___y_4097_, v___y_4098_);
return v___x_4117_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4___boxed(lean_object* v_stx_4158_, lean_object* v___x_4159_, lean_object* v___x_4160_, lean_object* v___x_4161_, lean_object* v___x_4162_, lean_object* v_as_4163_, lean_object* v_sz_4164_, lean_object* v_i_4165_, lean_object* v_b_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
size_t v_sz_boxed_4170_; size_t v_i_boxed_4171_; lean_object* v_res_4172_; 
v_sz_boxed_4170_ = lean_unbox_usize(v_sz_4164_);
lean_dec(v_sz_4164_);
v_i_boxed_4171_ = lean_unbox_usize(v_i_4165_);
lean_dec(v_i_4165_);
v_res_4172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4158_, v___x_4159_, v___x_4160_, v___x_4161_, v___x_4162_, v_as_4163_, v_sz_boxed_4170_, v_i_boxed_4171_, v_b_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec_ref(v_as_4163_);
lean_dec(v___x_4162_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v___x_4159_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(lean_object* v_init_4173_, lean_object* v_stx_4174_, lean_object* v___x_4175_, lean_object* v___x_4176_, lean_object* v___x_4177_, lean_object* v___x_4178_, lean_object* v_n_4179_, lean_object* v_b_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
if (lean_obj_tag(v_n_4179_) == 0)
{
lean_object* v_cs_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; size_t v_sz_4187_; size_t v___x_4188_; lean_object* v___x_4189_; 
v_cs_4184_ = lean_ctor_get(v_n_4179_, 0);
v___x_4185_ = lean_box(0);
v___x_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
lean_ctor_set(v___x_4186_, 1, v_b_4180_);
v_sz_4187_ = lean_array_size(v_cs_4184_);
v___x_4188_ = ((size_t)0ULL);
v___x_4189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4173_, v_stx_4174_, v___x_4175_, v___x_4176_, v___x_4177_, v___x_4178_, v_cs_4184_, v_sz_4187_, v___x_4188_, v___x_4186_, v___y_4181_, v___y_4182_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4204_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4192_ = v___x_4189_;
v_isShared_4193_ = v_isSharedCheck_4204_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4189_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4204_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v_fst_4194_; 
v_fst_4194_ = lean_ctor_get(v_a_4190_, 0);
if (lean_obj_tag(v_fst_4194_) == 0)
{
lean_object* v_snd_4195_; lean_object* v___x_4196_; lean_object* v___x_4198_; 
v_snd_4195_ = lean_ctor_get(v_a_4190_, 1);
lean_inc(v_snd_4195_);
lean_dec(v_a_4190_);
v___x_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4196_, 0, v_snd_4195_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 0, v___x_4196_);
v___x_4198_ = v___x_4192_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
else
{
lean_object* v_val_4200_; lean_object* v___x_4202_; 
lean_inc_ref(v_fst_4194_);
lean_dec(v_a_4190_);
v_val_4200_ = lean_ctor_get(v_fst_4194_, 0);
lean_inc(v_val_4200_);
lean_dec_ref_known(v_fst_4194_, 1);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 0, v_val_4200_);
v___x_4202_ = v___x_4192_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_val_4200_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
v_a_4205_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4189_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4189_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
else
{
lean_object* v_vs_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; size_t v_sz_4216_; size_t v___x_4217_; lean_object* v___x_4218_; 
v_vs_4213_ = lean_ctor_get(v_n_4179_, 0);
v___x_4214_ = lean_box(0);
v___x_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
lean_ctor_set(v___x_4215_, 1, v_b_4180_);
v_sz_4216_ = lean_array_size(v_vs_4213_);
v___x_4217_ = ((size_t)0ULL);
v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__4(v_stx_4174_, v___x_4175_, v___x_4176_, v___x_4177_, v___x_4178_, v_vs_4213_, v_sz_4216_, v___x_4217_, v___x_4215_, v___y_4181_, v___y_4182_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4233_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4233_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4233_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v_fst_4223_; 
v_fst_4223_ = lean_ctor_get(v_a_4219_, 0);
if (lean_obj_tag(v_fst_4223_) == 0)
{
lean_object* v_snd_4224_; lean_object* v___x_4225_; lean_object* v___x_4227_; 
v_snd_4224_ = lean_ctor_get(v_a_4219_, 1);
lean_inc(v_snd_4224_);
lean_dec(v_a_4219_);
v___x_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4225_, 0, v_snd_4224_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4225_);
v___x_4227_ = v___x_4221_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
else
{
lean_object* v_val_4229_; lean_object* v___x_4231_; 
lean_inc_ref(v_fst_4223_);
lean_dec(v_a_4219_);
v_val_4229_ = lean_ctor_get(v_fst_4223_, 0);
lean_inc(v_val_4229_);
lean_dec_ref_known(v_fst_4223_, 1);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v_val_4229_);
v___x_4231_ = v___x_4221_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_val_4229_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
v_a_4234_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4218_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4218_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(lean_object* v_init_4242_, lean_object* v_stx_4243_, lean_object* v___x_4244_, lean_object* v___x_4245_, lean_object* v___x_4246_, lean_object* v___x_4247_, lean_object* v_as_4248_, size_t v_sz_4249_, size_t v_i_4250_, lean_object* v_b_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
uint8_t v___x_4255_; 
v___x_4255_ = lean_usize_dec_lt(v_i_4250_, v_sz_4249_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; 
lean_dec_ref(v___x_4246_);
lean_dec(v_stx_4243_);
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v_b_4251_);
return v___x_4256_;
}
else
{
lean_object* v_snd_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4291_; 
v_snd_4257_ = lean_ctor_get(v_b_4251_, 1);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_b_4251_);
if (v_isSharedCheck_4291_ == 0)
{
lean_object* v_unused_4292_; 
v_unused_4292_ = lean_ctor_get(v_b_4251_, 0);
lean_dec(v_unused_4292_);
v___x_4259_ = v_b_4251_;
v_isShared_4260_ = v_isSharedCheck_4291_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_snd_4257_);
lean_dec(v_b_4251_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4291_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4261_; lean_object* v_a_4262_; lean_object* v___x_4263_; 
v___x_4261_ = lean_box(0);
v_a_4262_ = lean_array_uget_borrowed(v_as_4248_, v_i_4250_);
lean_inc(v_snd_4257_);
lean_inc_ref(v___x_4246_);
lean_inc(v_stx_4243_);
v___x_4263_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4242_, v_stx_4243_, v___x_4244_, v___x_4245_, v___x_4246_, v___x_4247_, v_a_4262_, v_snd_4257_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4282_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4266_ = v___x_4263_;
v_isShared_4267_ = v_isSharedCheck_4282_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4263_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4282_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
if (lean_obj_tag(v_a_4264_) == 0)
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
lean_dec_ref(v___x_4246_);
lean_dec(v_stx_4243_);
v___x_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4268_, 0, v_a_4264_);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 0, v___x_4268_);
v___x_4270_ = v___x_4259_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4268_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v_snd_4257_);
v___x_4270_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4272_; 
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 0, v___x_4270_);
v___x_4272_ = v___x_4266_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; 
lean_del_object(v___x_4266_);
lean_dec(v_snd_4257_);
v_a_4275_ = lean_ctor_get(v_a_4264_, 0);
lean_inc(v_a_4275_);
lean_dec_ref_known(v_a_4264_, 1);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 1, v_a_4275_);
lean_ctor_set(v___x_4259_, 0, v___x_4261_);
v___x_4277_ = v___x_4259_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4261_);
lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_a_4275_);
v___x_4277_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
size_t v___x_4278_; size_t v___x_4279_; 
v___x_4278_ = ((size_t)1ULL);
v___x_4279_ = lean_usize_add(v_i_4250_, v___x_4278_);
v_i_4250_ = v___x_4279_;
v_b_4251_ = v___x_4277_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_del_object(v___x_4259_);
lean_dec(v_snd_4257_);
lean_dec_ref(v___x_4246_);
lean_dec(v_stx_4243_);
v_a_4283_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4263_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4263_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3___boxed(lean_object* v_init_4293_, lean_object* v_stx_4294_, lean_object* v___x_4295_, lean_object* v___x_4296_, lean_object* v___x_4297_, lean_object* v___x_4298_, lean_object* v_as_4299_, lean_object* v_sz_4300_, lean_object* v_i_4301_, lean_object* v_b_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
size_t v_sz_boxed_4306_; size_t v_i_boxed_4307_; lean_object* v_res_4308_; 
v_sz_boxed_4306_ = lean_unbox_usize(v_sz_4300_);
lean_dec(v_sz_4300_);
v_i_boxed_4307_ = lean_unbox_usize(v_i_4301_);
lean_dec(v_i_4301_);
v_res_4308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2_spec__3(v_init_4293_, v_stx_4294_, v___x_4295_, v___x_4296_, v___x_4297_, v___x_4298_, v_as_4299_, v_sz_boxed_4306_, v_i_boxed_4307_, v_b_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v_as_4299_);
lean_dec(v___x_4298_);
lean_dec_ref(v___x_4296_);
lean_dec_ref(v___x_4295_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2___boxed(lean_object* v_init_4309_, lean_object* v_stx_4310_, lean_object* v___x_4311_, lean_object* v___x_4312_, lean_object* v___x_4313_, lean_object* v___x_4314_, lean_object* v_n_4315_, lean_object* v_b_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4309_, v_stx_4310_, v___x_4311_, v___x_4312_, v___x_4313_, v___x_4314_, v_n_4315_, v_b_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec_ref(v_n_4315_);
lean_dec(v___x_4314_);
lean_dec_ref(v___x_4312_);
lean_dec_ref(v___x_4311_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(lean_object* v___x_4321_, lean_object* v___x_4322_, lean_object* v_stx_4323_, lean_object* v___x_4324_, lean_object* v___x_4325_, lean_object* v_t_4326_, lean_object* v_init_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_root_4331_; lean_object* v_tail_4332_; lean_object* v___x_4333_; 
v_root_4331_ = lean_ctor_get(v_t_4326_, 0);
v_tail_4332_ = lean_ctor_get(v_t_4326_, 1);
lean_inc_ref(v___x_4321_);
lean_inc(v_stx_4323_);
v___x_4333_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__2(v_init_4327_, v_stx_4323_, v___x_4324_, v___x_4325_, v___x_4321_, v___x_4322_, v_root_4331_, v_init_4327_, v___y_4328_, v___y_4329_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4370_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4370_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4370_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
if (lean_obj_tag(v_a_4334_) == 0)
{
lean_object* v_a_4338_; lean_object* v___x_4340_; 
lean_dec(v_stx_4323_);
lean_dec_ref(v___x_4321_);
v_a_4338_ = lean_ctor_get(v_a_4334_, 0);
lean_inc(v_a_4338_);
lean_dec_ref_known(v_a_4334_, 1);
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 0, v_a_4338_);
v___x_4340_ = v___x_4336_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4338_);
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
lean_object* v_a_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; size_t v_sz_4345_; size_t v___x_4346_; lean_object* v___x_4347_; 
lean_del_object(v___x_4336_);
v_a_4342_ = lean_ctor_get(v_a_4334_, 0);
lean_inc(v_a_4342_);
lean_dec_ref_known(v_a_4334_, 1);
v___x_4343_ = lean_box(0);
v___x_4344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
lean_ctor_set(v___x_4344_, 1, v_a_4342_);
v_sz_4345_ = lean_array_size(v_tail_4332_);
v___x_4346_ = ((size_t)0ULL);
v___x_4347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2_spec__3(v_stx_4323_, v___x_4324_, v___x_4325_, v___x_4321_, v___x_4322_, v_tail_4332_, v_sz_4345_, v___x_4346_, v___x_4344_, v___y_4328_, v___y_4329_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4361_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4350_ = v___x_4347_;
v_isShared_4351_ = v_isSharedCheck_4361_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4347_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4361_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v_fst_4352_; 
v_fst_4352_ = lean_ctor_get(v_a_4348_, 0);
if (lean_obj_tag(v_fst_4352_) == 0)
{
lean_object* v_snd_4353_; lean_object* v___x_4355_; 
v_snd_4353_ = lean_ctor_get(v_a_4348_, 1);
lean_inc(v_snd_4353_);
lean_dec(v_a_4348_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v_snd_4353_);
v___x_4355_ = v___x_4350_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_snd_4353_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
else
{
lean_object* v_val_4357_; lean_object* v___x_4359_; 
lean_inc_ref(v_fst_4352_);
lean_dec(v_a_4348_);
v_val_4357_ = lean_ctor_get(v_fst_4352_, 0);
lean_inc(v_val_4357_);
lean_dec_ref_known(v_fst_4352_, 1);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v_val_4357_);
v___x_4359_ = v___x_4350_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_val_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
v_a_4362_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4347_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4347_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec(v_stx_4323_);
lean_dec_ref(v___x_4321_);
v_a_4371_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4333_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4333_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2___boxed(lean_object* v___x_4379_, lean_object* v___x_4380_, lean_object* v_stx_4381_, lean_object* v___x_4382_, lean_object* v___x_4383_, lean_object* v_t_4384_, lean_object* v_init_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___x_4379_, v___x_4380_, v_stx_4381_, v___x_4382_, v___x_4383_, v_t_4384_, v_init_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec_ref(v_t_4384_);
lean_dec_ref(v___x_4383_);
lean_dec_ref(v___x_4382_);
lean_dec(v___x_4380_);
return v_res_4389_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__0));
v___x_4392_ = l_Lean_stringToMessageData(v___x_4391_);
return v___x_4392_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__4));
v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
return v___x_4397_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__6));
v___x_4400_ = l_Lean_stringToMessageData(v___x_4399_);
return v___x_4400_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__8));
v___x_4403_ = l_Lean_stringToMessageData(v___x_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(lean_object* v_stx_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v_scopes_4413_; lean_object* v___x_4414_; lean_object* v_opts_4415_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; uint8_t v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4447_; uint8_t v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; uint8_t v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; uint8_t v___y_4459_; lean_object* v___y_4460_; uint8_t v___y_4469_; lean_object* v___y_4470_; uint8_t v___y_4471_; uint8_t v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; uint8_t v___y_4483_; uint8_t v___y_4484_; uint8_t v___y_4485_; uint8_t v___y_4519_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v___x_4411_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4412_ = lean_st_ref_get(v___y_4406_);
v_scopes_4413_ = lean_ctor_get(v___x_4412_, 2);
lean_inc(v_scopes_4413_);
lean_dec(v___x_4412_);
v___x_4414_ = l_List_head_x21___redArg(v___x_4411_, v_scopes_4413_);
lean_dec(v_scopes_4413_);
v_opts_4415_ = lean_ctor_get(v___x_4414_, 1);
lean_inc_ref(v_opts_4415_);
lean_dec(v___x_4414_);
v___x_4526_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onEmptyProof;
v___x_4527_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4415_, v___x_4526_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_tactic_tryOnEmptyBy;
v___x_4529_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4415_, v___x_4528_);
v___y_4519_ = v___x_4529_;
goto v___jp_4518_;
}
else
{
v___y_4519_ = v___x_4527_;
goto v___jp_4518_;
}
v___jp_4408_:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = lean_box(0);
v___x_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4409_);
return v___x_4410_;
}
v___jp_4416_:
{
lean_object* v___x_4421_; lean_object* v_line_4422_; lean_object* v___x_4423_; lean_object* v_messages_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v_a_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
lean_inc_ref_n(v___y_4417_, 2);
v___x_4421_ = l_Lean_FileMap_toPosition(v___y_4417_, v___y_4420_);
lean_dec(v___y_4420_);
v_line_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_line_4422_);
lean_dec_ref(v___x_4421_);
v___x_4423_ = lean_st_ref_get(v___y_4419_);
v_messages_4424_ = lean_ctor_get(v___x_4423_, 1);
lean_inc_ref(v_messages_4424_);
lean_dec(v___x_4423_);
v___x_4425_ = l_Lean_MessageLog_reportedPlusUnreported(v_messages_4424_);
v___x_4426_ = l_Lean_Elab_getInfoTrees___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__0___redArg(v___y_4419_);
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref(v___x_4426_);
v___x_4428_ = lean_box(0);
v___x_4429_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook_spec__2(v___y_4417_, v_line_4422_, v_stx_4404_, v_opts_4415_, v___x_4425_, v_a_4427_, v___x_4428_, v___y_4418_, v___y_4419_);
lean_dec(v_a_4427_);
lean_dec_ref(v___x_4425_);
lean_dec_ref(v_opts_4415_);
lean_dec(v_line_4422_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4436_ == 0)
{
lean_object* v_unused_4437_; 
v_unused_4437_ = lean_ctor_get(v___x_4429_, 0);
lean_dec(v_unused_4437_);
v___x_4431_ = v___x_4429_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_dec(v___x_4429_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4428_);
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4428_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
else
{
return v___x_4429_;
}
}
v___jp_4438_:
{
lean_object* v_fileMap_4442_; lean_object* v___x_4443_; 
v_fileMap_4442_ = lean_ctor_get(v___y_4440_, 1);
v___x_4443_ = l_Lean_Syntax_getPos_x3f(v_stx_4404_, v___y_4439_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v___x_4444_; 
v___x_4444_ = lean_unsigned_to_nat(0u);
v___y_4417_ = v_fileMap_4442_;
v___y_4418_ = v___y_4440_;
v___y_4419_ = v___y_4441_;
v___y_4420_ = v___x_4444_;
goto v___jp_4416_;
}
else
{
lean_object* v_val_4445_; 
v_val_4445_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_val_4445_);
lean_dec_ref_known(v___x_4443_, 1);
v___y_4417_ = v_fileMap_4442_;
v___y_4418_ = v___y_4440_;
v___y_4419_ = v___y_4441_;
v___y_4420_ = v_val_4445_;
goto v___jp_4416_;
}
}
v___jp_4446_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
lean_inc_ref(v___y_4450_);
v___x_4451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___y_4450_);
v___x_4452_ = l_Lean_MessageData_ofFormat(v___x_4451_);
v___x_4453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___y_4447_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
lean_inc(v___y_4449_);
v___x_4454_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___y_4449_, v___x_4453_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_dec_ref_known(v___x_4454_, 1);
v___y_4439_ = v___y_4448_;
v___y_4440_ = v___y_4405_;
v___y_4441_ = v___y_4406_;
goto v___jp_4438_;
}
else
{
lean_dec_ref(v_opts_4415_);
lean_dec(v_stx_4404_);
return v___x_4454_;
}
}
v___jp_4455_:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
lean_inc_ref(v___y_4460_);
v___x_4461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___y_4460_);
v___x_4462_ = l_Lean_MessageData_ofFormat(v___x_4461_);
v___x_4463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___y_4457_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
v___x_4464_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__1);
v___x_4465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4463_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
if (v___y_4456_ == 0)
{
lean_object* v___x_4466_; 
v___x_4466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4447_ = v___x_4465_;
v___y_4448_ = v___y_4459_;
v___y_4449_ = v___y_4458_;
v___y_4450_ = v___x_4466_;
goto v___jp_4446_;
}
else
{
lean_object* v___x_4467_; 
v___x_4467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4447_ = v___x_4465_;
v___y_4448_ = v___y_4459_;
v___y_4449_ = v___y_4458_;
v___y_4450_ = v___x_4467_;
goto v___jp_4446_;
}
}
v___jp_4468_:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
lean_inc_ref(v___y_4474_);
v___x_4475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___y_4474_);
v___x_4476_ = l_Lean_MessageData_ofFormat(v___x_4475_);
lean_inc_ref(v___y_4470_);
v___x_4477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___y_4470_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
v___x_4478_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__5);
v___x_4479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4477_);
lean_ctor_set(v___x_4479_, 1, v___x_4478_);
if (v___y_4471_ == 0)
{
lean_object* v___x_4480_; 
v___x_4480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___y_4456_ = v___y_4469_;
v___y_4457_ = v___x_4479_;
v___y_4458_ = v___y_4473_;
v___y_4459_ = v___y_4472_;
v___y_4460_ = v___x_4480_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4481_; 
v___x_4481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___y_4456_ = v___y_4469_;
v___y_4457_ = v___x_4479_;
v___y_4458_ = v___y_4473_;
v___y_4459_ = v___y_4472_;
v___y_4460_ = v___x_4481_;
goto v___jp_4455_;
}
}
v___jp_4482_:
{
lean_object* v___x_4486_; lean_object* v_a_4487_; uint8_t v___x_4488_; 
v___x_4486_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_hasNonUnsolvedGoalError(v_stx_4404_, v___y_4405_, v___y_4406_);
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref(v___x_4486_);
v___x_4488_ = lean_unbox(v_a_4487_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v_scopes_4493_; lean_object* v___x_4494_; lean_object* v_opts_4495_; uint8_t v_hasTrace_4496_; 
v___x_4489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4490_ = l_Lean_inheritedTraceOptions;
v___x_4491_ = lean_st_ref_get(v___x_4490_);
v___x_4492_ = lean_st_ref_get(v___y_4406_);
v_scopes_4493_ = lean_ctor_get(v___x_4492_, 2);
lean_inc(v_scopes_4493_);
lean_dec(v___x_4492_);
v___x_4494_ = l_List_head_x21___redArg(v___x_4411_, v_scopes_4493_);
lean_dec(v_scopes_4493_);
v_opts_4495_ = lean_ctor_get(v___x_4494_, 1);
lean_inc_ref(v_opts_4495_);
lean_dec(v___x_4494_);
v_hasTrace_4496_ = lean_ctor_get_uint8(v_opts_4495_, sizeof(void*)*1);
if (v_hasTrace_4496_ == 0)
{
uint8_t v___x_4497_; 
lean_dec_ref(v_opts_4495_);
lean_dec(v___x_4491_);
v___x_4497_ = lean_unbox(v_a_4487_);
lean_dec(v_a_4487_);
v___y_4439_ = v___x_4497_;
v___y_4440_ = v___y_4405_;
v___y_4441_ = v___y_4406_;
goto v___jp_4438_;
}
else
{
lean_object* v___x_4498_; uint8_t v___x_4499_; 
v___x_4498_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4499_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4491_, v_opts_4495_, v___x_4498_);
lean_dec_ref(v_opts_4495_);
lean_dec(v___x_4491_);
if (v___x_4499_ == 0)
{
uint8_t v___x_4500_; 
v___x_4500_ = lean_unbox(v_a_4487_);
lean_dec(v_a_4487_);
v___y_4439_ = v___x_4500_;
v___y_4440_ = v___y_4405_;
v___y_4441_ = v___y_4406_;
goto v___jp_4438_;
}
else
{
lean_object* v___x_4501_; 
v___x_4501_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__7);
if (v___y_4484_ == 0)
{
lean_object* v___x_4502_; uint8_t v___x_4503_; 
v___x_4502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__2));
v___x_4503_ = lean_unbox(v_a_4487_);
lean_dec(v_a_4487_);
v___y_4469_ = v___y_4483_;
v___y_4470_ = v___x_4501_;
v___y_4471_ = v___y_4485_;
v___y_4472_ = v___x_4503_;
v___y_4473_ = v___x_4489_;
v___y_4474_ = v___x_4502_;
goto v___jp_4468_;
}
else
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__3));
v___x_4505_ = lean_unbox(v_a_4487_);
lean_dec(v_a_4487_);
v___y_4469_ = v___y_4483_;
v___y_4470_ = v___x_4501_;
v___y_4471_ = v___y_4485_;
v___y_4472_ = v___x_4505_;
v___y_4473_ = v___x_4489_;
v___y_4474_ = v___x_4504_;
goto v___jp_4468_;
}
}
}
}
else
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v_scopes_4510_; lean_object* v___x_4511_; lean_object* v_opts_4512_; uint8_t v_hasTrace_4513_; 
lean_dec(v_a_4487_);
lean_dec_ref(v_opts_4415_);
lean_dec(v_stx_4404_);
v___x_4506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn___closed__0_00___x40_Lean_Elab_Tactic_AutoTry_938150806____hygCtx___hyg_2_));
v___x_4507_ = l_Lean_inheritedTraceOptions;
v___x_4508_ = lean_st_ref_get(v___x_4507_);
v___x_4509_ = lean_st_ref_get(v___y_4406_);
v_scopes_4510_ = lean_ctor_get(v___x_4509_, 2);
lean_inc(v_scopes_4510_);
lean_dec(v___x_4509_);
v___x_4511_ = l_List_head_x21___redArg(v___x_4411_, v_scopes_4510_);
lean_dec(v_scopes_4510_);
v_opts_4512_ = lean_ctor_get(v___x_4511_, 1);
lean_inc_ref(v_opts_4512_);
lean_dec(v___x_4511_);
v_hasTrace_4513_ = lean_ctor_get_uint8(v_opts_4512_, sizeof(void*)*1);
if (v_hasTrace_4513_ == 0)
{
lean_dec_ref(v_opts_4512_);
lean_dec(v___x_4508_);
goto v___jp_4408_;
}
else
{
lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__5_spec__9_spec__13___closed__3);
v___x_4515_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4508_, v_opts_4512_, v___x_4514_);
lean_dec_ref(v_opts_4512_);
lean_dec(v___x_4508_);
if (v___x_4515_ == 0)
{
goto v___jp_4408_;
}
else
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = lean_obj_once(&l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9, &l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___closed__9);
v___x_4517_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__4(v___x_4506_, v___x_4516_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_dec_ref_known(v___x_4517_, 1);
goto v___jp_4408_;
}
else
{
return v___x_4517_;
}
}
}
}
}
v___jp_4518_:
{
lean_object* v___x_4520_; uint8_t v___x_4521_; lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4520_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onUnsolvedGoal;
v___x_4521_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4415_, v___x_4520_);
v___x_4522_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTry_onSorry;
v___x_4523_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_collectTriggerPoints_spec__0(v_opts_4415_, v___x_4522_);
if (v___y_4519_ == 0)
{
if (v___x_4521_ == 0)
{
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
lean_dec_ref(v_opts_4415_);
lean_dec(v_stx_4404_);
v___x_4524_ = lean_box(0);
v___x_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
return v___x_4525_;
}
else
{
v___y_4483_ = v___x_4523_;
v___y_4484_ = v___y_4519_;
v___y_4485_ = v___x_4521_;
goto v___jp_4482_;
}
}
else
{
v___y_4483_ = v___x_4523_;
v___y_4484_ = v___y_4519_;
v___y_4485_ = v___x_4521_;
goto v___jp_4482_;
}
}
else
{
v___y_4483_ = v___x_4523_;
v___y_4484_ = v___y_4519_;
v___y_4485_ = v___x_4521_;
goto v___jp_4482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0___boxed(lean_object* v_stx_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook___lam__0(v_stx_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_autoTryHook));
v___x_4548_ = l_Lean_Elab_Command_addLinter(v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2____boxed(lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Elab_Tactic_AutoTry_0__Lean_Elab_Tactic_AutoTry_initFn_00___x40_Lean_Elab_Tactic_AutoTry_2389746878____hygCtx___hyg_2_();
return v_res_4550_;
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
