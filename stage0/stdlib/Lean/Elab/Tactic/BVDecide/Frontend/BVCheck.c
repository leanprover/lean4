// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVCheck
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide public import Lean.Meta.Tactic.TryThis
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "cannot compute parent directory of `"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Preparing LRAT reflection term"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 160, 246, 114, 147, 242, 134, 91)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(184, 210, 190, 202, 6, 52, 139, 149)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(215, 212, 31, 122, 239, 8, 183, 192)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(lean_object* v_opts_23_, lean_object* v_opt_24_){
_start:
{
lean_object* v_name_25_; lean_object* v_defValue_26_; lean_object* v_map_27_; lean_object* v___x_28_; 
v_name_25_ = lean_ctor_get(v_opt_24_, 0);
v_defValue_26_ = lean_ctor_get(v_opt_24_, 1);
v_map_27_ = lean_ctor_get(v_opts_23_, 0);
v___x_28_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_27_, v_name_25_);
if (lean_obj_tag(v___x_28_) == 0)
{
uint8_t v___x_29_; 
v___x_29_ = lean_unbox(v_defValue_26_);
return v___x_29_;
}
else
{
lean_object* v_val_30_; 
v_val_30_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_val_30_);
lean_dec_ref(v___x_28_);
if (lean_obj_tag(v_val_30_) == 1)
{
uint8_t v_v_31_; 
v_v_31_ = lean_ctor_get_uint8(v_val_30_, 0);
lean_dec_ref(v_val_30_);
return v_v_31_;
}
else
{
uint8_t v___x_32_; 
lean_dec(v_val_30_);
v___x_32_ = lean_unbox(v_defValue_26_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_33_, lean_object* v_opt_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_33_, v_opt_34_);
lean_dec_ref(v_opt_34_);
lean_dec_ref(v_opts_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_box(1);
v___x_38_ = l_Lean_MessageData_ofFormat(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2));
v___x_43_ = l_Lean_MessageData_ofFormat(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3(lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
return v_x_44_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_69_; 
v_head_46_ = lean_ctor_get(v_x_45_, 0);
v_tail_47_ = lean_ctor_get(v_x_45_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_69_ == 0)
{
v___x_49_ = v_x_45_;
v_isShared_50_ = v_isSharedCheck_69_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_tail_47_);
lean_inc(v_head_46_);
lean_dec(v_x_45_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_69_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v_before_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_67_; 
v_before_51_ = lean_ctor_get(v_head_46_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_head_46_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v_head_46_, 1);
lean_dec(v_unused_68_);
v___x_53_ = v_head_46_;
v_isShared_54_ = v_isSharedCheck_67_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_before_51_);
lean_dec(v_head_46_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_67_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_54_ == 0)
{
lean_ctor_set_tag(v___x_53_, 7);
lean_ctor_set(v___x_53_, 1, v___x_55_);
lean_ctor_set(v___x_53_, 0, v_x_44_);
v___x_57_ = v___x_53_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_x_44_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_55_);
v___x_57_ = v_reuseFailAlloc_66_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_50_ == 0)
{
lean_ctor_set_tag(v___x_49_, 7);
lean_ctor_set(v___x_49_, 1, v___x_58_);
lean_ctor_set(v___x_49_, 0, v___x_57_);
v___x_60_ = v___x_49_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_58_);
v___x_60_ = v_reuseFailAlloc_65_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = l_Lean_MessageData_ofSyntax(v_before_51_);
v___x_62_ = l_Lean_indentD(v___x_61_);
v___x_63_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_60_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v_x_44_ = v___x_63_;
v_x_45_ = v_tail_47_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1));
v___x_74_ = l_Lean_MessageData_ofFormat(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg(lean_object* v_msgData_75_, lean_object* v_macroStack_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_options_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_options_79_ = lean_ctor_get(v___y_77_, 2);
v___x_80_ = l_Lean_Elab_pp_macroStack;
v___x_81_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
lean_dec(v_macroStack_76_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_msgData_75_);
return v___x_82_;
}
else
{
if (lean_obj_tag(v_macroStack_76_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_msgData_75_);
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_after_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_100_; 
v_head_84_ = lean_ctor_get(v_macroStack_76_, 0);
lean_inc(v_head_84_);
v_after_85_ = lean_ctor_get(v_head_84_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_head_84_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v_head_84_, 0);
lean_dec(v_unused_101_);
v___x_87_ = v_head_84_;
v_isShared_88_ = v_isSharedCheck_100_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_after_85_);
lean_dec(v_head_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_100_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 7);
lean_ctor_set(v___x_87_, 1, v___x_89_);
lean_ctor_set(v___x_87_, 0, v_msgData_75_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_msgData_75_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_99_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_msgData_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_92_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_MessageData_ofSyntax(v_after_85_);
v___x_95_ = l_Lean_indentD(v___x_94_);
v_msgData_96_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_96_, 0, v___x_93_);
lean_ctor_set(v_msgData_96_, 1, v___x_95_);
v___x_97_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__3(v_msgData_96_, v_macroStack_76_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_102_, lean_object* v_macroStack_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_102_, v_macroStack_103_, v___y_104_);
lean_dec_ref(v___y_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___redArg(lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v_a_117_; lean_object* v_macroStack_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_115_ = lean_ctor_get(v___y_112_, 5);
v___x_116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v_msg_107_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v___x_116_);
v_macroStack_118_ = lean_ctor_get(v___y_108_, 1);
lean_inc_n(v_macroStack_118_, 2);
v___x_119_ = l_Lean_Elab_getBetterRef(v_ref_115_, v_macroStack_118_);
v___x_120_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_117_, v_macroStack_118_, v___y_112_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___redArg___boxed(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___redArg(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_138_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__0));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2));
v___x_144_ = l_Lean_stringToMessageData(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_fileName_152_; lean_object* v___x_153_; 
v_fileName_152_ = lean_ctor_get(v_a_149_, 0);
lean_inc_ref(v_fileName_152_);
v___x_153_ = l_System_FilePath_parent(v_fileName_152_);
if (lean_obj_tag(v___x_153_) == 1)
{
lean_object* v_val_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_val_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_val_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 0);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_val_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v___x_153_);
v___x_162_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1);
lean_inc_ref(v_fileName_152_);
v___x_163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_163_, 0, v_fileName_152_);
v___x_164_ = l_Lean_MessageData_ofFormat(v___x_163_);
v___x_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___redArg(v___x_167_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___boxed(lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0(lean_object* v_00_u03b1_177_, lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___redArg(v_msg_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___boxed(lean_object* v_00_u03b1_187_, lean_object* v_msg_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0(v_00_u03b1_187_, v_msg_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1(lean_object* v_msgData_197_, lean_object* v_macroStack_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_197_, v_macroStack_198_, v___y_203_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1___boxed(lean_object* v_msgData_207_, lean_object* v_macroStack_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_207_, v_macroStack_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object* v_lratPath_217_, lean_object* v_cfg_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v___x_228_ = l_System_FilePath_join(v_a_227_, v_lratPath_217_);
v___x_229_ = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(v___x_228_, v_cfg_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
return v___x_229_;
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v_cfg_218_);
lean_dec_ref(v_lratPath_217_);
v_a_230_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_226_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_226_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext___boxed(lean_object* v_lratPath_238_, lean_object* v_cfg_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(v_lratPath_238_, v_cfg_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(lean_object* v_ctx_248_, lean_object* v_reflectionResult_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_config_255_; lean_object* v_lratPath_256_; uint8_t v_trimProofs_257_; lean_object* v___x_258_; 
v_config_255_ = lean_ctor_get(v_ctx_248_, 5);
v_lratPath_256_ = lean_ctor_get(v_ctx_248_, 4);
v_trimProofs_257_ = lean_ctor_get_uint8(v_config_255_, sizeof(void*)*2);
v___x_258_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(v_lratPath_256_, v_trimProofs_257_, v_a_252_, v_a_253_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_260_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref(v___x_258_);
v___x_260_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof(v_a_259_, v_ctx_248_, v_reflectionResult_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
return v___x_260_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v_reflectionResult_249_);
lean_dec_ref(v_ctx_248_);
v_a_261_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_258_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_258_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___boxed(lean_object* v_ctx_269_, lean_object* v_reflectionResult_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_269_, v_reflectionResult_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
return v_res_276_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(32u);
v___x_278_ = lean_mk_empty_array_with_capacity(v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_280_ = ((size_t)5ULL);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_unsigned_to_nat(32u);
v___x_283_ = lean_mk_empty_array_with_capacity(v___x_282_);
v___x_284_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0);
v___x_285_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___x_281_);
lean_ctor_set(v___x_285_, 3, v___x_281_);
lean_ctor_set_usize(v___x_285_, 4, v___x_280_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_traceState_289_; lean_object* v_traces_290_; lean_object* v___x_291_; lean_object* v_traceState_292_; lean_object* v_env_293_; lean_object* v_nextMacroScope_294_; lean_object* v_ngen_295_; lean_object* v_auxDeclNGen_296_; lean_object* v_cache_297_; lean_object* v_messages_298_; lean_object* v_infoState_299_; lean_object* v_snapshotTasks_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_319_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_traceState_289_ = lean_ctor_get(v___x_288_, 4);
lean_inc_ref(v_traceState_289_);
lean_dec(v___x_288_);
v_traces_290_ = lean_ctor_get(v_traceState_289_, 0);
lean_inc_ref(v_traces_290_);
lean_dec_ref(v_traceState_289_);
v___x_291_ = lean_st_ref_take(v___y_286_);
v_traceState_292_ = lean_ctor_get(v___x_291_, 4);
v_env_293_ = lean_ctor_get(v___x_291_, 0);
v_nextMacroScope_294_ = lean_ctor_get(v___x_291_, 1);
v_ngen_295_ = lean_ctor_get(v___x_291_, 2);
v_auxDeclNGen_296_ = lean_ctor_get(v___x_291_, 3);
v_cache_297_ = lean_ctor_get(v___x_291_, 5);
v_messages_298_ = lean_ctor_get(v___x_291_, 6);
v_infoState_299_ = lean_ctor_get(v___x_291_, 7);
v_snapshotTasks_300_ = lean_ctor_get(v___x_291_, 8);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_319_ == 0)
{
v___x_302_ = v___x_291_;
v_isShared_303_ = v_isSharedCheck_319_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_snapshotTasks_300_);
lean_inc(v_infoState_299_);
lean_inc(v_messages_298_);
lean_inc(v_cache_297_);
lean_inc(v_traceState_292_);
lean_inc(v_auxDeclNGen_296_);
lean_inc(v_ngen_295_);
lean_inc(v_nextMacroScope_294_);
lean_inc(v_env_293_);
lean_dec(v___x_291_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_319_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint64_t v_tid_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_317_; 
v_tid_304_ = lean_ctor_get_uint64(v_traceState_292_, sizeof(void*)*1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_traceState_292_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_traceState_292_, 0);
lean_dec(v_unused_318_);
v___x_306_ = v_traceState_292_;
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_traceState_292_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_308_);
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_308_);
lean_ctor_set_uint64(v_reuseFailAlloc_316_, sizeof(void*)*1, v_tid_304_);
v___x_310_ = v_reuseFailAlloc_316_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_312_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v___x_310_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_env_293_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_nextMacroScope_294_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_ngen_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_auxDeclNGen_296_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_315_, 5, v_cache_297_);
lean_ctor_set(v_reuseFailAlloc_315_, 6, v_messages_298_);
lean_ctor_set(v_reuseFailAlloc_315_, 7, v_infoState_299_);
lean_ctor_set(v_reuseFailAlloc_315_, 8, v_snapshotTasks_300_);
v___x_312_ = v_reuseFailAlloc_315_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_st_ref_set(v___y_286_, v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v_traces_290_);
return v___x_314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___boxed(lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v___y_320_);
lean_dec(v___y_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0(lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v___y_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___boxed(lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0(v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1));
v___x_339_ = l_Lean_MessageData_ofFormat(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0(lean_object* v_x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___boxed(lean_object* v_x_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0(v_x_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec_ref(v_x_348_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
v_a_357_ = lean_ctor_get(v_x_355_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_355_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v_x_355_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v_x_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
v_a_365_ = lean_ctor_get(v_x_355_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_355_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v_x_355_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v_x_355_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 0);
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg___boxed(lean_object* v_x_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(v_x_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(lean_object* v_opts_376_, lean_object* v_opt_377_){
_start:
{
lean_object* v_name_378_; lean_object* v_defValue_379_; lean_object* v_map_380_; lean_object* v___x_381_; 
v_name_378_ = lean_ctor_get(v_opt_377_, 0);
v_defValue_379_ = lean_ctor_get(v_opt_377_, 1);
v_map_380_ = lean_ctor_get(v_opts_376_, 0);
v___x_381_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_380_, v_name_378_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_inc(v_defValue_379_);
return v_defValue_379_;
}
else
{
lean_object* v_val_382_; 
v_val_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_382_);
lean_dec_ref(v___x_381_);
if (lean_obj_tag(v_val_382_) == 3)
{
lean_object* v_v_383_; 
v_v_383_ = lean_ctor_get(v_val_382_, 0);
lean_inc(v_v_383_);
lean_dec_ref(v_val_382_);
return v_v_383_;
}
else
{
lean_dec(v_val_382_);
lean_inc(v_defValue_379_);
return v_defValue_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4___boxed(lean_object* v_opts_384_, lean_object* v_opt_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(v_opts_384_, v_opt_385_);
lean_dec_ref(v_opt_385_);
lean_dec_ref(v_opts_384_);
return v_res_386_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1(lean_object* v_e_387_){
_start:
{
if (lean_obj_tag(v_e_387_) == 0)
{
uint8_t v___x_388_; 
v___x_388_ = 2;
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = 0;
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1___boxed(lean_object* v_e_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1(v_e_390_);
lean_dec_ref(v_e_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3(size_t v_sz_393_, size_t v_i_394_, lean_object* v_bs_395_){
_start:
{
uint8_t v___x_396_; 
v___x_396_ = lean_usize_dec_lt(v_i_394_, v_sz_393_);
if (v___x_396_ == 0)
{
return v_bs_395_;
}
else
{
lean_object* v_v_397_; lean_object* v_msg_398_; lean_object* v___x_399_; lean_object* v_bs_x27_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; 
v_v_397_ = lean_array_uget_borrowed(v_bs_395_, v_i_394_);
v_msg_398_ = lean_ctor_get(v_v_397_, 1);
lean_inc_ref(v_msg_398_);
v___x_399_ = lean_unsigned_to_nat(0u);
v_bs_x27_400_ = lean_array_uset(v_bs_395_, v_i_394_, v___x_399_);
v___x_401_ = ((size_t)1ULL);
v___x_402_ = lean_usize_add(v_i_394_, v___x_401_);
v___x_403_ = lean_array_uset(v_bs_x27_400_, v_i_394_, v_msg_398_);
v_i_394_ = v___x_402_;
v_bs_395_ = v___x_403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3___boxed(lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_bs_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_409_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3(v_sz_boxed_408_, v_i_boxed_409_, v_bs_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2(lean_object* v_oldTraces_411_, lean_object* v_data_412_, lean_object* v_ref_413_, lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_fileName_420_; lean_object* v_fileMap_421_; lean_object* v_options_422_; lean_object* v_currRecDepth_423_; lean_object* v_maxRecDepth_424_; lean_object* v_ref_425_; lean_object* v_currNamespace_426_; lean_object* v_openDecls_427_; lean_object* v_initHeartbeats_428_; lean_object* v_maxHeartbeats_429_; lean_object* v_quotContext_430_; lean_object* v_currMacroScope_431_; uint8_t v_diag_432_; lean_object* v_cancelTk_x3f_433_; uint8_t v_suppressElabErrors_434_; lean_object* v_inheritedTraceOptions_435_; lean_object* v___x_436_; lean_object* v_traceState_437_; lean_object* v_traces_438_; lean_object* v_ref_439_; lean_object* v___x_440_; lean_object* v___x_441_; size_t v_sz_442_; size_t v___x_443_; lean_object* v___x_444_; lean_object* v_msg_445_; lean_object* v___x_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_484_; 
v_fileName_420_ = lean_ctor_get(v___y_417_, 0);
v_fileMap_421_ = lean_ctor_get(v___y_417_, 1);
v_options_422_ = lean_ctor_get(v___y_417_, 2);
v_currRecDepth_423_ = lean_ctor_get(v___y_417_, 3);
v_maxRecDepth_424_ = lean_ctor_get(v___y_417_, 4);
v_ref_425_ = lean_ctor_get(v___y_417_, 5);
v_currNamespace_426_ = lean_ctor_get(v___y_417_, 6);
v_openDecls_427_ = lean_ctor_get(v___y_417_, 7);
v_initHeartbeats_428_ = lean_ctor_get(v___y_417_, 8);
v_maxHeartbeats_429_ = lean_ctor_get(v___y_417_, 9);
v_quotContext_430_ = lean_ctor_get(v___y_417_, 10);
v_currMacroScope_431_ = lean_ctor_get(v___y_417_, 11);
v_diag_432_ = lean_ctor_get_uint8(v___y_417_, sizeof(void*)*14);
v_cancelTk_x3f_433_ = lean_ctor_get(v___y_417_, 12);
v_suppressElabErrors_434_ = lean_ctor_get_uint8(v___y_417_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_435_ = lean_ctor_get(v___y_417_, 13);
v___x_436_ = lean_st_ref_get(v___y_418_);
v_traceState_437_ = lean_ctor_get(v___x_436_, 4);
lean_inc_ref(v_traceState_437_);
lean_dec(v___x_436_);
v_traces_438_ = lean_ctor_get(v_traceState_437_, 0);
lean_inc_ref(v_traces_438_);
lean_dec_ref(v_traceState_437_);
v_ref_439_ = l_Lean_replaceRef(v_ref_413_, v_ref_425_);
lean_inc_ref(v_inheritedTraceOptions_435_);
lean_inc(v_cancelTk_x3f_433_);
lean_inc(v_currMacroScope_431_);
lean_inc(v_quotContext_430_);
lean_inc(v_maxHeartbeats_429_);
lean_inc(v_initHeartbeats_428_);
lean_inc(v_openDecls_427_);
lean_inc(v_currNamespace_426_);
lean_inc(v_maxRecDepth_424_);
lean_inc(v_currRecDepth_423_);
lean_inc_ref(v_options_422_);
lean_inc_ref(v_fileMap_421_);
lean_inc_ref(v_fileName_420_);
v___x_440_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_440_, 0, v_fileName_420_);
lean_ctor_set(v___x_440_, 1, v_fileMap_421_);
lean_ctor_set(v___x_440_, 2, v_options_422_);
lean_ctor_set(v___x_440_, 3, v_currRecDepth_423_);
lean_ctor_set(v___x_440_, 4, v_maxRecDepth_424_);
lean_ctor_set(v___x_440_, 5, v_ref_439_);
lean_ctor_set(v___x_440_, 6, v_currNamespace_426_);
lean_ctor_set(v___x_440_, 7, v_openDecls_427_);
lean_ctor_set(v___x_440_, 8, v_initHeartbeats_428_);
lean_ctor_set(v___x_440_, 9, v_maxHeartbeats_429_);
lean_ctor_set(v___x_440_, 10, v_quotContext_430_);
lean_ctor_set(v___x_440_, 11, v_currMacroScope_431_);
lean_ctor_set(v___x_440_, 12, v_cancelTk_x3f_433_);
lean_ctor_set(v___x_440_, 13, v_inheritedTraceOptions_435_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*14, v_diag_432_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*14 + 1, v_suppressElabErrors_434_);
v___x_441_ = l_Lean_PersistentArray_toArray___redArg(v_traces_438_);
lean_dec_ref(v_traces_438_);
v_sz_442_ = lean_array_size(v___x_441_);
v___x_443_ = ((size_t)0ULL);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3(v_sz_442_, v___x_443_, v___x_441_);
v_msg_445_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_445_, 0, v_data_412_);
lean_ctor_set(v_msg_445_, 1, v_msg_414_);
lean_ctor_set(v_msg_445_, 2, v___x_444_);
v___x_446_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v_msg_445_, v___y_415_, v___y_416_, v___x_440_, v___y_418_);
lean_dec_ref(v___x_440_);
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_484_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_484_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_484_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v_traceState_452_; lean_object* v_env_453_; lean_object* v_nextMacroScope_454_; lean_object* v_ngen_455_; lean_object* v_auxDeclNGen_456_; lean_object* v_cache_457_; lean_object* v_messages_458_; lean_object* v_infoState_459_; lean_object* v_snapshotTasks_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_483_; 
v___x_451_ = lean_st_ref_take(v___y_418_);
v_traceState_452_ = lean_ctor_get(v___x_451_, 4);
v_env_453_ = lean_ctor_get(v___x_451_, 0);
v_nextMacroScope_454_ = lean_ctor_get(v___x_451_, 1);
v_ngen_455_ = lean_ctor_get(v___x_451_, 2);
v_auxDeclNGen_456_ = lean_ctor_get(v___x_451_, 3);
v_cache_457_ = lean_ctor_get(v___x_451_, 5);
v_messages_458_ = lean_ctor_get(v___x_451_, 6);
v_infoState_459_ = lean_ctor_get(v___x_451_, 7);
v_snapshotTasks_460_ = lean_ctor_get(v___x_451_, 8);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_483_ == 0)
{
v___x_462_ = v___x_451_;
v_isShared_463_ = v_isSharedCheck_483_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_snapshotTasks_460_);
lean_inc(v_infoState_459_);
lean_inc(v_messages_458_);
lean_inc(v_cache_457_);
lean_inc(v_traceState_452_);
lean_inc(v_auxDeclNGen_456_);
lean_inc(v_ngen_455_);
lean_inc(v_nextMacroScope_454_);
lean_inc(v_env_453_);
lean_dec(v___x_451_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_483_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
uint64_t v_tid_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_481_; 
v_tid_464_ = lean_ctor_get_uint64(v_traceState_452_, sizeof(void*)*1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_traceState_452_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v_traceState_452_, 0);
lean_dec(v_unused_482_);
v___x_466_ = v_traceState_452_;
v_isShared_467_ = v_isSharedCheck_481_;
goto v_resetjp_465_;
}
else
{
lean_dec(v_traceState_452_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_481_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_ref_413_);
lean_ctor_set(v___x_468_, 1, v_a_447_);
v___x_469_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_411_, v___x_468_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_469_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_469_);
lean_ctor_set_uint64(v_reuseFailAlloc_480_, sizeof(void*)*1, v_tid_464_);
v___x_471_ = v_reuseFailAlloc_480_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 4, v___x_471_);
v___x_473_ = v___x_462_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_env_453_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_nextMacroScope_454_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_ngen_455_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_auxDeclNGen_456_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_479_, 5, v_cache_457_);
lean_ctor_set(v_reuseFailAlloc_479_, 6, v_messages_458_);
lean_ctor_set(v_reuseFailAlloc_479_, 7, v_infoState_459_);
lean_ctor_set(v_reuseFailAlloc_479_, 8, v_snapshotTasks_460_);
v___x_473_ = v_reuseFailAlloc_479_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_st_ref_set(v___y_418_, v___x_473_);
v___x_475_ = lean_box(0);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_475_);
v___x_477_ = v___x_449_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2___boxed(lean_object* v_oldTraces_485_, lean_object* v_data_486_, lean_object* v_ref_487_, lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2(v_oldTraces_485_, v_data_486_, v_ref_487_, v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_494_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__0));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2(void){
_start:
{
lean_object* v___x_498_; double v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_float_of_nat(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__3));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5(void){
_start:
{
lean_object* v___x_503_; double v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(1000u);
v___x_504_ = lean_float_of_nat(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(lean_object* v_cls_505_, uint8_t v_collapsed_506_, lean_object* v_tag_507_, lean_object* v_opts_508_, uint8_t v_clsEnabled_509_, lean_object* v_oldTraces_510_, lean_object* v_msg_511_, lean_object* v_resStartStop_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_fst_518_; lean_object* v_snd_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_617_; 
v_fst_518_ = lean_ctor_get(v_resStartStop_512_, 0);
v_snd_519_ = lean_ctor_get(v_resStartStop_512_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_resStartStop_512_);
if (v_isSharedCheck_617_ == 0)
{
v___x_521_ = v_resStartStop_512_;
v_isShared_522_ = v_isSharedCheck_617_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snd_519_);
lean_inc(v_fst_518_);
lean_dec(v_resStartStop_512_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_617_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v_data_526_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_616_; 
v_fst_537_ = lean_ctor_get(v_snd_519_, 0);
v_snd_538_ = lean_ctor_get(v_snd_519_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_snd_519_);
if (v_isSharedCheck_616_ == 0)
{
v___x_540_ = v_snd_519_;
v_isShared_541_ = v_isSharedCheck_616_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snd_538_);
lean_inc(v_fst_537_);
lean_dec(v_snd_519_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_616_;
goto v_resetjp_539_;
}
v___jp_523_:
{
lean_object* v___x_527_; 
lean_inc(v___y_525_);
v___x_527_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2(v_oldTraces_510_, v_data_526_, v___y_525_, v___y_524_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; 
lean_dec_ref(v___x_527_);
v___x_528_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(v_fst_518_);
return v___x_528_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_fst_518_);
v_a_529_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_527_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_527_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
v_resetjp_539_:
{
lean_object* v___x_542_; uint8_t v___x_543_; lean_object* v___y_545_; lean_object* v_a_546_; uint8_t v___y_570_; double v___y_601_; 
v___x_542_ = l_Lean_trace_profiler;
v___x_543_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_508_, v___x_542_);
if (v___x_543_ == 0)
{
v___y_570_ = v___x_543_;
goto v___jp_569_;
}
else
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = l_Lean_trace_profiler_useHeartbeats;
v___x_607_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_508_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; double v___x_610_; double v___x_611_; double v___x_612_; 
v___x_608_ = l_Lean_trace_profiler_threshold;
v___x_609_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(v_opts_508_, v___x_608_);
v___x_610_ = lean_float_of_nat(v___x_609_);
v___x_611_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5);
v___x_612_ = lean_float_div(v___x_610_, v___x_611_);
v___y_601_ = v___x_612_;
goto v___jp_600_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; double v___x_615_; 
v___x_613_ = l_Lean_trace_profiler_threshold;
v___x_614_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(v_opts_508_, v___x_613_);
v___x_615_ = lean_float_of_nat(v___x_614_);
v___y_601_ = v___x_615_;
goto v___jp_600_;
}
}
v___jp_544_:
{
uint8_t v_result_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v_result_547_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1(v_fst_518_);
v___x_548_ = l_Lean_TraceResult_toEmoji(v_result_547_);
v___x_549_ = l_Lean_stringToMessageData(v___x_548_);
v___x_550_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1);
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 7);
lean_ctor_set(v___x_540_, 1, v___x_550_);
lean_ctor_set(v___x_540_, 0, v___x_549_);
v___x_552_ = v___x_540_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_563_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v_m_554_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 7);
lean_ctor_set(v___x_521_, 1, v_a_546_);
lean_ctor_set(v___x_521_, 0, v___x_552_);
v_m_554_ = v___x_521_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_a_546_);
v_m_554_ = v_reuseFailAlloc_562_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; double v___x_557_; lean_object* v_data_558_; 
v___x_555_ = lean_box(v_result_547_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___x_557_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2);
lean_inc_ref(v_tag_507_);
lean_inc_ref(v___x_556_);
lean_inc(v_cls_505_);
v_data_558_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_558_, 0, v_cls_505_);
lean_ctor_set(v_data_558_, 1, v___x_556_);
lean_ctor_set(v_data_558_, 2, v_tag_507_);
lean_ctor_set_float(v_data_558_, sizeof(void*)*3, v___x_557_);
lean_ctor_set_float(v_data_558_, sizeof(void*)*3 + 8, v___x_557_);
lean_ctor_set_uint8(v_data_558_, sizeof(void*)*3 + 16, v_collapsed_506_);
if (v___x_543_ == 0)
{
lean_dec_ref(v___x_556_);
lean_dec(v_snd_538_);
lean_dec(v_fst_537_);
lean_dec_ref(v_tag_507_);
lean_dec(v_cls_505_);
v___y_524_ = v_m_554_;
v___y_525_ = v___y_545_;
v_data_526_ = v_data_558_;
goto v___jp_523_;
}
else
{
lean_object* v_data_559_; double v___x_560_; double v___x_561_; 
lean_dec_ref(v_data_558_);
v_data_559_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_559_, 0, v_cls_505_);
lean_ctor_set(v_data_559_, 1, v___x_556_);
lean_ctor_set(v_data_559_, 2, v_tag_507_);
v___x_560_ = lean_unbox_float(v_fst_537_);
lean_dec(v_fst_537_);
lean_ctor_set_float(v_data_559_, sizeof(void*)*3, v___x_560_);
v___x_561_ = lean_unbox_float(v_snd_538_);
lean_dec(v_snd_538_);
lean_ctor_set_float(v_data_559_, sizeof(void*)*3 + 8, v___x_561_);
lean_ctor_set_uint8(v_data_559_, sizeof(void*)*3 + 16, v_collapsed_506_);
v___y_524_ = v_m_554_;
v___y_525_ = v___y_545_;
v_data_526_ = v_data_559_;
goto v___jp_523_;
}
}
}
}
v___jp_564_:
{
lean_object* v_ref_565_; lean_object* v___x_566_; 
v_ref_565_ = lean_ctor_get(v___y_515_, 5);
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
lean_inc(v_fst_518_);
v___x_566_ = lean_apply_6(v_msg_511_, v_fst_518_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, lean_box(0));
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref(v___x_566_);
v___y_545_ = v_ref_565_;
v_a_546_ = v_a_567_;
goto v___jp_544_;
}
else
{
lean_object* v___x_568_; 
lean_dec_ref(v___x_566_);
v___x_568_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4);
v___y_545_ = v_ref_565_;
v_a_546_ = v___x_568_;
goto v___jp_544_;
}
}
v___jp_569_:
{
if (v_clsEnabled_509_ == 0)
{
if (v___y_570_ == 0)
{
lean_object* v___x_571_; lean_object* v_traceState_572_; lean_object* v_env_573_; lean_object* v_nextMacroScope_574_; lean_object* v_ngen_575_; lean_object* v_auxDeclNGen_576_; lean_object* v_cache_577_; lean_object* v_messages_578_; lean_object* v_infoState_579_; lean_object* v_snapshotTasks_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_599_; 
lean_del_object(v___x_540_);
lean_dec(v_snd_538_);
lean_dec(v_fst_537_);
lean_del_object(v___x_521_);
lean_dec_ref(v_msg_511_);
lean_dec_ref(v_tag_507_);
lean_dec(v_cls_505_);
v___x_571_ = lean_st_ref_take(v___y_516_);
v_traceState_572_ = lean_ctor_get(v___x_571_, 4);
v_env_573_ = lean_ctor_get(v___x_571_, 0);
v_nextMacroScope_574_ = lean_ctor_get(v___x_571_, 1);
v_ngen_575_ = lean_ctor_get(v___x_571_, 2);
v_auxDeclNGen_576_ = lean_ctor_get(v___x_571_, 3);
v_cache_577_ = lean_ctor_get(v___x_571_, 5);
v_messages_578_ = lean_ctor_get(v___x_571_, 6);
v_infoState_579_ = lean_ctor_get(v___x_571_, 7);
v_snapshotTasks_580_ = lean_ctor_get(v___x_571_, 8);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_599_ == 0)
{
v___x_582_ = v___x_571_;
v_isShared_583_ = v_isSharedCheck_599_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_snapshotTasks_580_);
lean_inc(v_infoState_579_);
lean_inc(v_messages_578_);
lean_inc(v_cache_577_);
lean_inc(v_traceState_572_);
lean_inc(v_auxDeclNGen_576_);
lean_inc(v_ngen_575_);
lean_inc(v_nextMacroScope_574_);
lean_inc(v_env_573_);
lean_dec(v___x_571_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_599_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
uint64_t v_tid_584_; lean_object* v_traces_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_598_; 
v_tid_584_ = lean_ctor_get_uint64(v_traceState_572_, sizeof(void*)*1);
v_traces_585_ = lean_ctor_get(v_traceState_572_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_traceState_572_);
if (v_isSharedCheck_598_ == 0)
{
v___x_587_ = v_traceState_572_;
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_traces_585_);
lean_dec(v_traceState_572_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_510_, v_traces_585_);
lean_dec_ref(v_traces_585_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_589_);
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_589_);
lean_ctor_set_uint64(v_reuseFailAlloc_597_, sizeof(void*)*1, v_tid_584_);
v___x_591_ = v_reuseFailAlloc_597_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 4, v___x_591_);
v___x_593_ = v___x_582_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_env_573_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_nextMacroScope_574_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_ngen_575_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_auxDeclNGen_576_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_596_, 5, v_cache_577_);
lean_ctor_set(v_reuseFailAlloc_596_, 6, v_messages_578_);
lean_ctor_set(v_reuseFailAlloc_596_, 7, v_infoState_579_);
lean_ctor_set(v_reuseFailAlloc_596_, 8, v_snapshotTasks_580_);
v___x_593_ = v_reuseFailAlloc_596_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_st_ref_set(v___y_516_, v___x_593_);
v___x_595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(v_fst_518_);
return v___x_595_;
}
}
}
}
}
else
{
goto v___jp_564_;
}
}
else
{
goto v___jp_564_;
}
}
v___jp_600_:
{
double v___x_602_; double v___x_603_; double v___x_604_; uint8_t v___x_605_; 
v___x_602_ = lean_unbox_float(v_snd_538_);
v___x_603_ = lean_unbox_float(v_fst_537_);
v___x_604_ = lean_float_sub(v___x_602_, v___x_603_);
v___x_605_ = lean_float_decLt(v___y_601_, v___x_604_);
v___y_570_ = v___x_605_;
goto v___jp_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___boxed(lean_object* v_cls_618_, lean_object* v_collapsed_619_, lean_object* v_tag_620_, lean_object* v_opts_621_, lean_object* v_clsEnabled_622_, lean_object* v_oldTraces_623_, lean_object* v_msg_624_, lean_object* v_resStartStop_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
uint8_t v_collapsed_boxed_631_; uint8_t v_clsEnabled_boxed_632_; lean_object* v_res_633_; 
v_collapsed_boxed_631_ = lean_unbox(v_collapsed_619_);
v_clsEnabled_boxed_632_ = lean_unbox(v_clsEnabled_622_);
v_res_633_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(v_cls_618_, v_collapsed_boxed_631_, v_tag_620_, v_opts_621_, v_clsEnabled_boxed_632_, v_oldTraces_623_, v_msg_624_, v_resStartStop_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v_opts_621_);
return v_res_633_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4));
v___x_646_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__6));
v___x_647_ = l_Lean_Name_append(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8(void){
_start:
{
lean_object* v___x_648_; double v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(1000000000u);
v___x_649_ = lean_float_of_nat(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(lean_object* v_ctx_650_, lean_object* v___f_651_, lean_object* v_x_652_, lean_object* v_reflectionResult_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_options_660_; uint8_t v_hasTrace_661_; 
v_options_660_ = lean_ctor_get(v___y_657_, 2);
v_hasTrace_661_ = lean_ctor_get_uint8(v_options_660_, sizeof(void*)*1);
if (v_hasTrace_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v___f_651_);
v___x_662_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_650_, v_reflectionResult_653_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_673_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_673_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_673_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_673_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_667_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_a_663_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_669_);
v___x_671_ = v___x_665_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_a_674_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_662_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_662_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v_a_690_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v_a_705_; 
v_inheritedTraceOptions_682_ = lean_ctor_get(v___y_657_, 13);
v___x_683_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4));
v___x_684_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
v___x_685_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7);
v___x_686_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_682_, v_options_660_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = l_Lean_trace_profiler;
v___x_768_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_660_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref(v___f_651_);
v___x_769_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_650_, v_reflectionResult_653_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_779_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_779_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_a_770_);
lean_ctor_set(v___x_774_, 1, v___x_684_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_775_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_a_780_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_769_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_769_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
goto v___jp_714_;
}
}
else
{
goto v___jp_714_;
}
v___jp_687_:
{
lean_object* v___x_691_; double v___x_692_; double v___x_693_; double v___x_694_; double v___x_695_; double v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_691_ = lean_io_mono_nanos_now();
v___x_692_ = lean_float_of_nat(v___y_689_);
v___x_693_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8);
v___x_694_ = lean_float_div(v___x_692_, v___x_693_);
v___x_695_ = lean_float_of_nat(v___x_691_);
v___x_696_ = lean_float_div(v___x_695_, v___x_693_);
v___x_697_ = lean_box_float(v___x_694_);
v___x_698_ = lean_box_float(v___x_696_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_a_690_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(v___x_683_, v_hasTrace_661_, v___x_684_, v_options_660_, v___x_686_, v___y_688_, v___f_651_, v___x_700_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_701_;
}
v___jp_702_:
{
lean_object* v___x_706_; double v___x_707_; double v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_706_ = lean_io_get_num_heartbeats();
v___x_707_ = lean_float_of_nat(v___y_704_);
v___x_708_ = lean_float_of_nat(v___x_706_);
v___x_709_ = lean_box_float(v___x_707_);
v___x_710_ = lean_box_float(v___x_708_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_a_705_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(v___x_683_, v_hasTrace_661_, v___x_684_, v_options_660_, v___x_686_, v___y_703_, v___f_651_, v___x_712_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_713_;
}
v___jp_714_:
{
lean_object* v___x_715_; lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_766_; 
v___x_715_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v___y_658_);
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_766_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_766_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_766_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_trace_profiler_useHeartbeats;
v___x_721_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_660_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_io_mono_nanos_now();
v___x_723_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_650_, v_reflectionResult_653_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_735_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_735_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_735_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_735_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_a_724_);
lean_ctor_set(v___x_728_, 1, v___x_684_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 1);
lean_ctor_set(v___x_726_, 0, v___x_728_);
v___x_730_ = v___x_726_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 1);
lean_ctor_set(v___x_718_, 0, v___x_730_);
v___x_732_ = v___x_718_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
v___y_688_ = v_a_716_;
v___y_689_ = v___x_722_;
v_a_690_ = v___x_732_;
goto v___jp_687_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_del_object(v___x_718_);
v_a_736_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_723_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_723_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 0);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
v___y_688_ = v_a_716_;
v___y_689_ = v___x_722_;
v_a_690_ = v___x_741_;
goto v___jp_687_;
}
}
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_io_get_num_heartbeats();
v___x_745_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_650_, v_reflectionResult_653_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_757_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_757_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_757_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_757_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_a_746_);
lean_ctor_set(v___x_750_, 1, v___x_684_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 1);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 1);
lean_ctor_set(v___x_718_, 0, v___x_752_);
v___x_754_ = v___x_718_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
v___y_703_ = v_a_716_;
v___y_704_ = v___x_744_;
v_a_705_ = v___x_754_;
goto v___jp_702_;
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_del_object(v___x_718_);
v_a_758_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_745_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_745_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 0);
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
v___y_703_ = v_a_716_;
v___y_704_ = v___x_744_;
v_a_705_ = v___x_763_;
goto v___jp_702_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed(lean_object* v_ctx_788_, lean_object* v___f_789_, lean_object* v_x_790_, lean_object* v_reflectionResult_791_, lean_object* v_x_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(v_ctx_788_, v___f_789_, v_x_790_, v_reflectionResult_791_, v_x_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec_ref(v_x_792_);
lean_dec(v_x_790_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object* v_g_800_, lean_object* v_ctx_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___f_807_; lean_object* v_unsatProver_808_; lean_object* v___x_809_; 
v___f_807_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0));
v_unsatProver_808_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed), 10, 2);
lean_closure_set(v_unsatProver_808_, 0, v_ctx_801_);
lean_closure_set(v_unsatProver_808_, 1, v___f_807_);
v___x_809_ = l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(v_g_800_, v_unsatProver_808_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_809_, 0);
lean_dec(v_unused_818_);
v___x_811_ = v___x_809_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_dec(v___x_809_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_box(0);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v_a_819_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_809_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_809_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___boxed(lean_object* v_g_827_, lean_object* v_ctx_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(v_g_827_, v_ctx_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3(lean_object* v_00_u03b1_835_, lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(v_x_836_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___boxed(lean_object* v_00_u03b1_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3(v_00_u03b1_843_, v_x_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_850_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_box(0);
v___x_852_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v___x_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(lean_object* v_00_u03b1_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___boxed(lean_object* v_00_u03b1_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(v_00_u03b1_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_880_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_887_, uint8_t v_suppressElabErrors_888_, lean_object* v_x_889_){
_start:
{
if (lean_obj_tag(v_x_889_) == 1)
{
lean_object* v_pre_890_; 
v_pre_890_ = lean_ctor_get(v_x_889_, 0);
switch(lean_obj_tag(v_pre_890_))
{
case 1:
{
lean_object* v_pre_891_; 
v_pre_891_ = lean_ctor_get(v_pre_890_, 0);
switch(lean_obj_tag(v_pre_891_))
{
case 0:
{
lean_object* v_str_892_; lean_object* v_str_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v_str_892_ = lean_ctor_get(v_x_889_, 1);
v_str_893_ = lean_ctor_get(v_pre_890_, 1);
v___x_894_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_895_ = lean_string_dec_eq(v_str_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2));
v___x_897_ = lean_string_dec_eq(v_str_893_, v___x_896_);
if (v___x_897_ == 0)
{
return v___y_887_;
}
else
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_899_ = lean_string_dec_eq(v_str_892_, v___x_898_);
if (v___x_899_ == 0)
{
return v___y_887_;
}
else
{
return v_suppressElabErrors_888_;
}
}
}
else
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_901_ = lean_string_dec_eq(v_str_892_, v___x_900_);
if (v___x_901_ == 0)
{
return v___y_887_;
}
else
{
return v_suppressElabErrors_888_;
}
}
}
case 1:
{
lean_object* v_pre_902_; 
v_pre_902_ = lean_ctor_get(v_pre_891_, 0);
if (lean_obj_tag(v_pre_902_) == 0)
{
lean_object* v_str_903_; lean_object* v_str_904_; lean_object* v_str_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_str_903_ = lean_ctor_get(v_x_889_, 1);
v_str_904_ = lean_ctor_get(v_pre_890_, 1);
v_str_905_ = lean_ctor_get(v_pre_891_, 1);
v___x_906_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_907_ = lean_string_dec_eq(v_str_905_, v___x_906_);
if (v___x_907_ == 0)
{
return v___y_887_;
}
else
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_909_ = lean_string_dec_eq(v_str_904_, v___x_908_);
if (v___x_909_ == 0)
{
return v___y_887_;
}
else
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_911_ = lean_string_dec_eq(v_str_903_, v___x_910_);
if (v___x_911_ == 0)
{
return v___y_887_;
}
else
{
return v_suppressElabErrors_888_;
}
}
}
}
else
{
return v___y_887_;
}
}
default: 
{
return v___y_887_;
}
}
}
case 0:
{
lean_object* v_str_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_str_912_ = lean_ctor_get(v_x_889_, 1);
v___x_913_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5));
v___x_914_ = lean_string_dec_eq(v_str_912_, v___x_913_);
if (v___x_914_ == 0)
{
return v___y_887_;
}
else
{
return v_suppressElabErrors_888_;
}
}
default: 
{
return v___y_887_;
}
}
}
else
{
return v___y_887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_915_, lean_object* v_suppressElabErrors_916_, lean_object* v_x_917_){
_start:
{
uint8_t v___y_6476__boxed_918_; uint8_t v_suppressElabErrors_boxed_919_; uint8_t v_res_920_; lean_object* v_r_921_; 
v___y_6476__boxed_918_ = lean_unbox(v___y_915_);
v_suppressElabErrors_boxed_919_ = lean_unbox(v_suppressElabErrors_916_);
v_res_920_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(v___y_6476__boxed_918_, v_suppressElabErrors_boxed_919_, v_x_917_);
lean_dec(v_x_917_);
v_r_921_ = lean_box(v_res_920_);
return v_r_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object* v_ref_922_, lean_object* v_msgData_923_, uint8_t v_severity_924_, uint8_t v_isSilent_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; uint8_t v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; uint8_t v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_968_; lean_object* v___y_969_; uint8_t v___y_970_; lean_object* v___y_971_; uint8_t v___y_972_; uint8_t v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_993_; lean_object* v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; uint8_t v___y_998_; uint8_t v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; uint8_t v___y_1008_; uint8_t v___y_1009_; uint8_t v___y_1010_; uint8_t v___x_1015_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___y_1021_; uint8_t v___y_1022_; uint8_t v___y_1023_; uint8_t v___y_1025_; uint8_t v___x_1040_; 
v___x_1015_ = 2;
v___x_1040_ = l_Lean_instBEqMessageSeverity_beq(v_severity_924_, v___x_1015_);
if (v___x_1040_ == 0)
{
v___y_1025_ = v___x_1040_;
goto v___jp_1024_;
}
else
{
uint8_t v___x_1041_; 
lean_inc_ref(v_msgData_923_);
v___x_1041_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_923_);
v___y_1025_ = v___x_1041_;
goto v___jp_1024_;
}
v___jp_931_:
{
lean_object* v___x_941_; lean_object* v_currNamespace_942_; lean_object* v_openDecls_943_; lean_object* v_env_944_; lean_object* v_nextMacroScope_945_; lean_object* v_ngen_946_; lean_object* v_auxDeclNGen_947_; lean_object* v_traceState_948_; lean_object* v_cache_949_; lean_object* v_messages_950_; lean_object* v_infoState_951_; lean_object* v_snapshotTasks_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_966_; 
v___x_941_ = lean_st_ref_take(v___y_940_);
v_currNamespace_942_ = lean_ctor_get(v___y_939_, 6);
v_openDecls_943_ = lean_ctor_get(v___y_939_, 7);
v_env_944_ = lean_ctor_get(v___x_941_, 0);
v_nextMacroScope_945_ = lean_ctor_get(v___x_941_, 1);
v_ngen_946_ = lean_ctor_get(v___x_941_, 2);
v_auxDeclNGen_947_ = lean_ctor_get(v___x_941_, 3);
v_traceState_948_ = lean_ctor_get(v___x_941_, 4);
v_cache_949_ = lean_ctor_get(v___x_941_, 5);
v_messages_950_ = lean_ctor_get(v___x_941_, 6);
v_infoState_951_ = lean_ctor_get(v___x_941_, 7);
v_snapshotTasks_952_ = lean_ctor_get(v___x_941_, 8);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_966_ == 0)
{
v___x_954_ = v___x_941_;
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snapshotTasks_952_);
lean_inc(v_infoState_951_);
lean_inc(v_messages_950_);
lean_inc(v_cache_949_);
lean_inc(v_traceState_948_);
lean_inc(v_auxDeclNGen_947_);
lean_inc(v_ngen_946_);
lean_inc(v_nextMacroScope_945_);
lean_inc(v_env_944_);
lean_dec(v___x_941_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
lean_inc(v_openDecls_943_);
lean_inc(v_currNamespace_942_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_currNamespace_942_);
lean_ctor_set(v___x_956_, 1, v_openDecls_943_);
v___x_957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___y_936_);
lean_inc_ref(v___y_932_);
lean_inc_ref(v___y_934_);
v___x_958_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_958_, 0, v___y_934_);
lean_ctor_set(v___x_958_, 1, v___y_937_);
lean_ctor_set(v___x_958_, 2, v___y_933_);
lean_ctor_set(v___x_958_, 3, v___y_932_);
lean_ctor_set(v___x_958_, 4, v___x_957_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*5, v___y_938_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*5 + 1, v___y_935_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*5 + 2, v_isSilent_925_);
v___x_959_ = l_Lean_MessageLog_add(v___x_958_, v_messages_950_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 6, v___x_959_);
v___x_961_ = v___x_954_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_env_944_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_nextMacroScope_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_ngen_946_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_auxDeclNGen_947_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_traceState_948_);
lean_ctor_set(v_reuseFailAlloc_965_, 5, v_cache_949_);
lean_ctor_set(v_reuseFailAlloc_965_, 6, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_965_, 7, v_infoState_951_);
lean_ctor_set(v_reuseFailAlloc_965_, 8, v_snapshotTasks_952_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_st_ref_set(v___y_940_, v___x_961_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
v___jp_967_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_991_; 
v___x_976_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_923_);
v___x_977_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v___x_976_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_991_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_991_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_991_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_inc_ref_n(v___y_971_, 2);
v___x_982_ = l_Lean_FileMap_toPosition(v___y_971_, v___y_974_);
lean_dec(v___y_974_);
v___x_983_ = l_Lean_FileMap_toPosition(v___y_971_, v___y_975_);
lean_dec(v___y_975_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
if (v___y_972_ == 0)
{
lean_del_object(v___x_980_);
lean_dec_ref(v___y_968_);
v___y_932_ = v___x_985_;
v___y_933_ = v___x_984_;
v___y_934_ = v___y_969_;
v___y_935_ = v___y_970_;
v___y_936_ = v_a_978_;
v___y_937_ = v___x_982_;
v___y_938_ = v___y_973_;
v___y_939_ = v___y_928_;
v___y_940_ = v___y_929_;
goto v___jp_931_;
}
else
{
uint8_t v___x_986_; 
lean_inc(v_a_978_);
v___x_986_ = l_Lean_MessageData_hasTag(v___y_968_, v_a_978_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_989_; 
lean_dec_ref(v___x_984_);
lean_dec_ref(v___x_982_);
lean_dec(v_a_978_);
v___x_987_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_987_);
v___x_989_ = v___x_980_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
else
{
lean_del_object(v___x_980_);
v___y_932_ = v___x_985_;
v___y_933_ = v___x_984_;
v___y_934_ = v___y_969_;
v___y_935_ = v___y_970_;
v___y_936_ = v_a_978_;
v___y_937_ = v___x_982_;
v___y_938_ = v___y_973_;
v___y_939_ = v___y_928_;
v___y_940_ = v___y_929_;
goto v___jp_931_;
}
}
}
}
v___jp_992_:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Syntax_getTailPos_x3f(v___y_996_, v___y_999_);
lean_dec(v___y_996_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_inc(v___y_1000_);
v___y_968_ = v___y_993_;
v___y_969_ = v___y_994_;
v___y_970_ = v___y_995_;
v___y_971_ = v___y_997_;
v___y_972_ = v___y_998_;
v___y_973_ = v___y_999_;
v___y_974_ = v___y_1000_;
v___y_975_ = v___y_1000_;
goto v___jp_967_;
}
else
{
lean_object* v_val_1002_; 
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref(v___x_1001_);
v___y_968_ = v___y_993_;
v___y_969_ = v___y_994_;
v___y_970_ = v___y_995_;
v___y_971_ = v___y_997_;
v___y_972_ = v___y_998_;
v___y_973_ = v___y_999_;
v___y_974_ = v___y_1000_;
v___y_975_ = v_val_1002_;
goto v___jp_967_;
}
}
v___jp_1003_:
{
lean_object* v_ref_1011_; lean_object* v___x_1012_; 
v_ref_1011_ = l_Lean_replaceRef(v_ref_922_, v___y_1007_);
v___x_1012_ = l_Lean_Syntax_getPos_x3f(v_ref_1011_, v___y_1009_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___y_993_ = v___y_1004_;
v___y_994_ = v___y_1005_;
v___y_995_ = v___y_1010_;
v___y_996_ = v_ref_1011_;
v___y_997_ = v___y_1006_;
v___y_998_ = v___y_1008_;
v___y_999_ = v___y_1009_;
v___y_1000_ = v___x_1013_;
goto v___jp_992_;
}
else
{
lean_object* v_val_1014_; 
v_val_1014_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_val_1014_);
lean_dec_ref(v___x_1012_);
v___y_993_ = v___y_1004_;
v___y_994_ = v___y_1005_;
v___y_995_ = v___y_1010_;
v___y_996_ = v_ref_1011_;
v___y_997_ = v___y_1006_;
v___y_998_ = v___y_1008_;
v___y_999_ = v___y_1009_;
v___y_1000_ = v_val_1014_;
goto v___jp_992_;
}
}
v___jp_1016_:
{
if (v___y_1023_ == 0)
{
v___y_1004_ = v___y_1020_;
v___y_1005_ = v___y_1017_;
v___y_1006_ = v___y_1018_;
v___y_1007_ = v___y_1019_;
v___y_1008_ = v___y_1021_;
v___y_1009_ = v___y_1022_;
v___y_1010_ = v_severity_924_;
goto v___jp_1003_;
}
else
{
v___y_1004_ = v___y_1020_;
v___y_1005_ = v___y_1017_;
v___y_1006_ = v___y_1018_;
v___y_1007_ = v___y_1019_;
v___y_1008_ = v___y_1021_;
v___y_1009_ = v___y_1022_;
v___y_1010_ = v___x_1015_;
goto v___jp_1003_;
}
}
v___jp_1024_:
{
if (v___y_1025_ == 0)
{
lean_object* v_fileName_1026_; lean_object* v_fileMap_1027_; lean_object* v_options_1028_; lean_object* v_ref_1029_; uint8_t v_suppressElabErrors_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; uint8_t v___x_1034_; uint8_t v___x_1035_; 
v_fileName_1026_ = lean_ctor_get(v___y_928_, 0);
v_fileMap_1027_ = lean_ctor_get(v___y_928_, 1);
v_options_1028_ = lean_ctor_get(v___y_928_, 2);
v_ref_1029_ = lean_ctor_get(v___y_928_, 5);
v_suppressElabErrors_1030_ = lean_ctor_get_uint8(v___y_928_, sizeof(void*)*14 + 1);
v___x_1031_ = lean_box(v___y_1025_);
v___x_1032_ = lean_box(v_suppressElabErrors_1030_);
v___f_1033_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1033_, 0, v___x_1031_);
lean_closure_set(v___f_1033_, 1, v___x_1032_);
v___x_1034_ = 1;
v___x_1035_ = l_Lean_instBEqMessageSeverity_beq(v_severity_924_, v___x_1034_);
if (v___x_1035_ == 0)
{
v___y_1017_ = v_fileName_1026_;
v___y_1018_ = v_fileMap_1027_;
v___y_1019_ = v_ref_1029_;
v___y_1020_ = v___f_1033_;
v___y_1021_ = v_suppressElabErrors_1030_;
v___y_1022_ = v___y_1025_;
v___y_1023_ = v___x_1035_;
goto v___jp_1016_;
}
else
{
lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = l_Lean_warningAsError;
v___x_1037_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1028_, v___x_1036_);
v___y_1017_ = v_fileName_1026_;
v___y_1018_ = v_fileMap_1027_;
v___y_1019_ = v_ref_1029_;
v___y_1020_ = v___f_1033_;
v___y_1021_ = v_suppressElabErrors_1030_;
v___y_1022_ = v___y_1025_;
v___y_1023_ = v___x_1037_;
goto v___jp_1016_;
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec_ref(v_msgData_923_);
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_1042_, lean_object* v_msgData_1043_, lean_object* v_severity_1044_, lean_object* v_isSilent_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v_severity_boxed_1051_; uint8_t v_isSilent_boxed_1052_; lean_object* v_res_1053_; 
v_severity_boxed_1051_ = lean_unbox(v_severity_1044_);
v_isSilent_boxed_1052_ = lean_unbox(v_isSilent_1045_);
v_res_1053_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1042_, v_msgData_1043_, v_severity_boxed_1051_, v_isSilent_boxed_1052_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v_ref_1042_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(lean_object* v_msgData_1054_, uint8_t v_severity_1055_, uint8_t v_isSilent_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_ref_1062_; lean_object* v___x_1063_; 
v_ref_1062_ = lean_ctor_get(v___y_1059_, 5);
v___x_1063_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1062_, v_msgData_1054_, v_severity_1055_, v_isSilent_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object* v_msgData_1064_, lean_object* v_severity_1065_, lean_object* v_isSilent_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v_severity_boxed_1072_; uint8_t v_isSilent_boxed_1073_; lean_object* v_res_1074_; 
v_severity_boxed_1072_ = lean_unbox(v_severity_1065_);
v_isSilent_boxed_1073_ = lean_unbox(v_isSilent_1066_);
v_res_1074_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1064_, v_severity_boxed_1072_, v_isSilent_boxed_1073_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(lean_object* v_msgData_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = 1;
v___x_1082_ = 0;
v___x_1083_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1075_, v___x_1081_, v___x_1082_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1___boxed(lean_object* v_msgData_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(v_msgData_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1090_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__0));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(lean_object* v_a_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v_tk_1105_, lean_object* v_a_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___y_1117_; lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1108_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(v_a_1130_, v_a_1100_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v___x_1131_);
if (lean_obj_tag(v_a_1132_) == 0)
{
lean_object* v_ref_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref(v_a_1106_);
v_ref_1133_ = lean_ctor_get(v___y_1113_, 5);
v___x_1134_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1);
v___x_1135_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(v___x_1134_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1156_; 
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v___x_1135_, 0);
lean_dec(v_unused_1157_);
v___x_1137_ = v___x_1135_;
v_isShared_1138_ = v_isSharedCheck_1156_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v___x_1135_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1156_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1139_ = 0;
v___x_1140_ = l_Lean_SourceInfo_fromRef(v_ref_1133_, v___x_1139_);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__2));
lean_inc(v___x_1140_);
v___x_1142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__4));
v___x_1144_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__5));
v___x_1145_ = l_Lean_Name_mkStr4(v___x_1101_, v___x_1102_, v___x_1103_, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_node2(v___x_1140_, v___x_1145_, v___x_1142_, v___x_1104_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1143_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_box(0);
v___x_1149_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
lean_ctor_set(v___x_1149_, 2, v___x_1148_);
lean_ctor_set(v___x_1149_, 3, v___x_1148_);
lean_ctor_set(v___x_1149_, 4, v___x_1148_);
lean_ctor_set(v___x_1149_, 5, v___x_1148_);
lean_inc(v_ref_1133_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
lean_ctor_set(v___x_1137_, 0, v_ref_1133_);
v___x_1151_ = v___x_1137_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_ref_1133_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__6));
v___x_1153_ = 4;
v___x_1154_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1105_, v___x_1149_, v___x_1151_, v___x_1152_, v___x_1148_, v___x_1153_, v___y_1113_, v___y_1114_);
v___y_1117_ = v___x_1154_;
goto v___jp_1116_;
}
}
}
else
{
lean_dec(v_tk_1105_);
lean_dec(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v___x_1101_);
v___y_1117_ = v___x_1135_;
goto v___jp_1116_;
}
}
else
{
lean_object* v_val_1158_; lean_object* v___x_1159_; 
lean_dec(v_tk_1105_);
lean_dec(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v___x_1101_);
v_val_1158_ = lean_ctor_get(v_a_1132_, 0);
lean_inc(v_val_1158_);
lean_dec_ref(v_a_1132_);
v___x_1159_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(v_val_1158_, v_a_1106_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
v___y_1117_ = v___x_1159_;
goto v___jp_1116_;
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_a_1106_);
lean_dec(v_tk_1105_);
lean_dec(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v___x_1101_);
v_a_1160_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1131_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1131_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_a_1106_);
lean_dec(v_tk_1105_);
lean_dec(v___x_1104_);
lean_dec_ref(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v___x_1101_);
v_a_1168_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1129_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1129_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
v___jp_1116_:
{
if (lean_obj_tag(v___y_1117_) == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v___y_1117_);
v___x_1118_ = lean_box(0);
v___x_1119_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1118_, v___y_1108_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v___x_1119_, 0);
lean_dec(v_unused_1128_);
v___x_1121_ = v___x_1119_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v___x_1119_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = lean_box(0);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
return v___x_1119_;
}
}
else
{
return v___y_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed(lean_object* v_a_1176_, lean_object* v___x_1177_, lean_object* v___x_1178_, lean_object* v___x_1179_, lean_object* v___x_1180_, lean_object* v_tk_1181_, lean_object* v_a_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(v_a_1176_, v___x_1177_, v___x_1178_, v___x_1179_, v___x_1180_, v_tk_1181_, v_a_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec_ref(v_a_1176_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(lean_object* v_x_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1220_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0));
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1));
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2));
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3));
lean_inc(v_x_1210_);
v___x_1224_ = l_Lean_Syntax_isOfKind(v_x_1210_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec(v_x_1210_);
v___x_1225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = l_Lean_Syntax_getArg(v_x_1210_, v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5));
lean_inc(v___x_1227_);
v___x_1229_ = l_Lean_Syntax_isOfKind(v___x_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec(v___x_1227_);
lean_dec(v_x_1210_);
v___x_1230_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; lean_object* v_path_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1231_ = lean_unsigned_to_nat(2u);
v_path_1232_ = l_Lean_Syntax_getArg(v_x_1210_, v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__7));
lean_inc(v_path_1232_);
v___x_1234_ = l_Lean_Syntax_isOfKind(v_path_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_path_1232_);
lean_dec(v___x_1227_);
lean_dec(v_x_1210_);
v___x_1235_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; 
lean_inc(v___x_1227_);
v___x_1236_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v___x_1227_, v_a_1211_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc_n(v_a_1237_, 2);
lean_dec_ref(v___x_1236_);
v___x_1238_ = l_Lean_TSyntax_getString(v_path_1232_);
lean_dec(v_path_1232_);
v___x_1239_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(v___x_1238_, v_a_1237_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; lean_object* v_tk_1242_; lean_object* v___f_1243_; lean_object* v___x_1244_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v_tk_1242_ = l_Lean_Syntax_getArg(v_x_1210_, v___x_1241_);
lean_dec(v_x_1210_);
v___f_1243_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1243_, 0, v_a_1237_);
lean_closure_set(v___f_1243_, 1, v___x_1220_);
lean_closure_set(v___f_1243_, 2, v___x_1221_);
lean_closure_set(v___f_1243_, 3, v___x_1222_);
lean_closure_set(v___f_1243_, 4, v___x_1227_);
lean_closure_set(v___f_1243_, 5, v_tk_1242_);
lean_closure_set(v___f_1243_, 6, v_a_1240_);
v___x_1244_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1243_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
return v___x_1244_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_a_1237_);
lean_dec(v___x_1227_);
lean_dec(v_x_1210_);
v_a_1245_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1239_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1239_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_path_1232_);
lean_dec(v___x_1227_);
lean_dec(v_x_1210_);
v_a_1253_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1236_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1236_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed(lean_object* v_x_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(v_x_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1285_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1286_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3));
v___x_1287_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4));
v___x_1288_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed), 10, 0);
v___x_1289_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1285_, v___x_1286_, v___x_1287_, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___boxed(lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1();
return v_res_1291_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(builtin);
}
#ifdef __cplusplus
}
#endif
