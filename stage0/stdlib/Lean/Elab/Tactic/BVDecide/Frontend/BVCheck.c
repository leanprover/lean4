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
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
v___x_119_ = l_Lean_Elab_getBetterRef(v_ref_115_, v_macroStack_118_);
lean_inc(v_macroStack_118_);
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
lean_object* v___x_288_; lean_object* v_traceState_289_; lean_object* v_traces_290_; lean_object* v___x_291_; lean_object* v_traceState_292_; lean_object* v_env_293_; lean_object* v_nextMacroScope_294_; lean_object* v_ngen_295_; lean_object* v_auxDeclNGen_296_; lean_object* v_cache_297_; lean_object* v_messages_298_; lean_object* v_infoState_299_; lean_object* v_snapshotTasks_300_; lean_object* v_newDecls_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_320_; 
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
v_newDecls_301_ = lean_ctor_get(v___x_291_, 9);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_320_ == 0)
{
v___x_303_ = v___x_291_;
v_isShared_304_ = v_isSharedCheck_320_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_newDecls_301_);
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
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_320_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
uint64_t v_tid_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_318_; 
v_tid_305_ = lean_ctor_get_uint64(v_traceState_292_, sizeof(void*)*1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_traceState_292_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v_traceState_292_, 0);
lean_dec(v_unused_319_);
v___x_307_ = v_traceState_292_;
v_isShared_308_ = v_isSharedCheck_318_;
goto v_resetjp_306_;
}
else
{
lean_dec(v_traceState_292_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_318_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_309_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_309_);
lean_ctor_set_uint64(v_reuseFailAlloc_317_, sizeof(void*)*1, v_tid_305_);
v___x_311_ = v_reuseFailAlloc_317_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 4, v___x_311_);
v___x_313_ = v___x_303_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_env_293_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_nextMacroScope_294_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_ngen_295_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_auxDeclNGen_296_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_316_, 5, v_cache_297_);
lean_ctor_set(v_reuseFailAlloc_316_, 6, v_messages_298_);
lean_ctor_set(v_reuseFailAlloc_316_, 7, v_infoState_299_);
lean_ctor_set(v_reuseFailAlloc_316_, 8, v_snapshotTasks_300_);
lean_ctor_set(v_reuseFailAlloc_316_, 9, v_newDecls_301_);
v___x_313_ = v_reuseFailAlloc_316_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_st_ref_set(v___y_286_, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_traces_290_);
return v___x_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___boxed(lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v___y_321_);
lean_dec(v___y_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0(lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v___y_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___boxed(lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0(v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_335_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1));
v___x_340_ = l_Lean_MessageData_ofFormat(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0(lean_object* v_x_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___boxed(lean_object* v_x_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0(v_x_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec_ref(v_x_349_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v_x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_356_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v_x_356_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v_x_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_a_366_ = lean_ctor_get(v_x_356_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_356_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v_x_356_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v_x_356_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 0);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg___boxed(lean_object* v_x_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(v_x_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(lean_object* v_opts_377_, lean_object* v_opt_378_){
_start:
{
lean_object* v_name_379_; lean_object* v_defValue_380_; lean_object* v_map_381_; lean_object* v___x_382_; 
v_name_379_ = lean_ctor_get(v_opt_378_, 0);
v_defValue_380_ = lean_ctor_get(v_opt_378_, 1);
v_map_381_ = lean_ctor_get(v_opts_377_, 0);
v___x_382_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_381_, v_name_379_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_inc(v_defValue_380_);
return v_defValue_380_;
}
else
{
lean_object* v_val_383_; 
v_val_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_383_);
lean_dec_ref(v___x_382_);
if (lean_obj_tag(v_val_383_) == 3)
{
lean_object* v_v_384_; 
v_v_384_ = lean_ctor_get(v_val_383_, 0);
lean_inc(v_v_384_);
lean_dec_ref(v_val_383_);
return v_v_384_;
}
else
{
lean_dec(v_val_383_);
lean_inc(v_defValue_380_);
return v_defValue_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4___boxed(lean_object* v_opts_385_, lean_object* v_opt_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(v_opts_385_, v_opt_386_);
lean_dec_ref(v_opt_386_);
lean_dec_ref(v_opts_385_);
return v_res_387_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1(lean_object* v_e_388_){
_start:
{
if (lean_obj_tag(v_e_388_) == 0)
{
uint8_t v___x_389_; 
v___x_389_ = 2;
return v___x_389_;
}
else
{
uint8_t v___x_390_; 
v___x_390_ = 0;
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1___boxed(lean_object* v_e_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1(v_e_391_);
lean_dec_ref(v_e_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3(size_t v_sz_394_, size_t v_i_395_, lean_object* v_bs_396_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_lt(v_i_395_, v_sz_394_);
if (v___x_397_ == 0)
{
return v_bs_396_;
}
else
{
lean_object* v_v_398_; lean_object* v_msg_399_; lean_object* v___x_400_; lean_object* v_bs_x27_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v___x_404_; 
v_v_398_ = lean_array_uget_borrowed(v_bs_396_, v_i_395_);
v_msg_399_ = lean_ctor_get(v_v_398_, 1);
lean_inc_ref(v_msg_399_);
v___x_400_ = lean_unsigned_to_nat(0u);
v_bs_x27_401_ = lean_array_uset(v_bs_396_, v_i_395_, v___x_400_);
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_add(v_i_395_, v___x_402_);
v___x_404_ = lean_array_uset(v_bs_x27_401_, v_i_395_, v_msg_399_);
v_i_395_ = v___x_403_;
v_bs_396_ = v___x_404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3___boxed(lean_object* v_sz_406_, lean_object* v_i_407_, lean_object* v_bs_408_){
_start:
{
size_t v_sz_boxed_409_; size_t v_i_boxed_410_; lean_object* v_res_411_; 
v_sz_boxed_409_ = lean_unbox_usize(v_sz_406_);
lean_dec(v_sz_406_);
v_i_boxed_410_ = lean_unbox_usize(v_i_407_);
lean_dec(v_i_407_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3(v_sz_boxed_409_, v_i_boxed_410_, v_bs_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2(lean_object* v_oldTraces_412_, lean_object* v_data_413_, lean_object* v_ref_414_, lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_fileName_421_; lean_object* v_fileMap_422_; lean_object* v_options_423_; lean_object* v_currRecDepth_424_; lean_object* v_maxRecDepth_425_; lean_object* v_ref_426_; lean_object* v_currNamespace_427_; lean_object* v_openDecls_428_; lean_object* v_initHeartbeats_429_; lean_object* v_maxHeartbeats_430_; lean_object* v_quotContext_431_; lean_object* v_currMacroScope_432_; uint8_t v_diag_433_; lean_object* v_cancelTk_x3f_434_; uint8_t v_suppressElabErrors_435_; lean_object* v_inheritedTraceOptions_436_; lean_object* v___x_437_; lean_object* v_traceState_438_; lean_object* v_traces_439_; lean_object* v_ref_440_; lean_object* v___x_441_; lean_object* v___x_442_; size_t v_sz_443_; size_t v___x_444_; lean_object* v___x_445_; lean_object* v_msg_446_; lean_object* v___x_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_486_; 
v_fileName_421_ = lean_ctor_get(v___y_418_, 0);
v_fileMap_422_ = lean_ctor_get(v___y_418_, 1);
v_options_423_ = lean_ctor_get(v___y_418_, 2);
v_currRecDepth_424_ = lean_ctor_get(v___y_418_, 3);
v_maxRecDepth_425_ = lean_ctor_get(v___y_418_, 4);
v_ref_426_ = lean_ctor_get(v___y_418_, 5);
v_currNamespace_427_ = lean_ctor_get(v___y_418_, 6);
v_openDecls_428_ = lean_ctor_get(v___y_418_, 7);
v_initHeartbeats_429_ = lean_ctor_get(v___y_418_, 8);
v_maxHeartbeats_430_ = lean_ctor_get(v___y_418_, 9);
v_quotContext_431_ = lean_ctor_get(v___y_418_, 10);
v_currMacroScope_432_ = lean_ctor_get(v___y_418_, 11);
v_diag_433_ = lean_ctor_get_uint8(v___y_418_, sizeof(void*)*14);
v_cancelTk_x3f_434_ = lean_ctor_get(v___y_418_, 12);
v_suppressElabErrors_435_ = lean_ctor_get_uint8(v___y_418_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_436_ = lean_ctor_get(v___y_418_, 13);
v___x_437_ = lean_st_ref_get(v___y_419_);
v_traceState_438_ = lean_ctor_get(v___x_437_, 4);
lean_inc_ref(v_traceState_438_);
lean_dec(v___x_437_);
v_traces_439_ = lean_ctor_get(v_traceState_438_, 0);
lean_inc_ref(v_traces_439_);
lean_dec_ref(v_traceState_438_);
v_ref_440_ = l_Lean_replaceRef(v_ref_414_, v_ref_426_);
lean_inc_ref(v_inheritedTraceOptions_436_);
lean_inc(v_cancelTk_x3f_434_);
lean_inc(v_currMacroScope_432_);
lean_inc(v_quotContext_431_);
lean_inc(v_maxHeartbeats_430_);
lean_inc(v_initHeartbeats_429_);
lean_inc(v_openDecls_428_);
lean_inc(v_currNamespace_427_);
lean_inc(v_maxRecDepth_425_);
lean_inc(v_currRecDepth_424_);
lean_inc_ref(v_options_423_);
lean_inc_ref(v_fileMap_422_);
lean_inc_ref(v_fileName_421_);
v___x_441_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_441_, 0, v_fileName_421_);
lean_ctor_set(v___x_441_, 1, v_fileMap_422_);
lean_ctor_set(v___x_441_, 2, v_options_423_);
lean_ctor_set(v___x_441_, 3, v_currRecDepth_424_);
lean_ctor_set(v___x_441_, 4, v_maxRecDepth_425_);
lean_ctor_set(v___x_441_, 5, v_ref_440_);
lean_ctor_set(v___x_441_, 6, v_currNamespace_427_);
lean_ctor_set(v___x_441_, 7, v_openDecls_428_);
lean_ctor_set(v___x_441_, 8, v_initHeartbeats_429_);
lean_ctor_set(v___x_441_, 9, v_maxHeartbeats_430_);
lean_ctor_set(v___x_441_, 10, v_quotContext_431_);
lean_ctor_set(v___x_441_, 11, v_currMacroScope_432_);
lean_ctor_set(v___x_441_, 12, v_cancelTk_x3f_434_);
lean_ctor_set(v___x_441_, 13, v_inheritedTraceOptions_436_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*14, v_diag_433_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*14 + 1, v_suppressElabErrors_435_);
v___x_442_ = l_Lean_PersistentArray_toArray___redArg(v_traces_439_);
lean_dec_ref(v_traces_439_);
v_sz_443_ = lean_array_size(v___x_442_);
v___x_444_ = ((size_t)0ULL);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2_spec__3(v_sz_443_, v___x_444_, v___x_442_);
v_msg_446_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_446_, 0, v_data_413_);
lean_ctor_set(v_msg_446_, 1, v_msg_415_);
lean_ctor_set(v_msg_446_, 2, v___x_445_);
v___x_447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v_msg_446_, v___y_416_, v___y_417_, v___x_441_, v___y_419_);
lean_dec_ref(v___x_441_);
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_486_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_486_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_486_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v_traceState_453_; lean_object* v_env_454_; lean_object* v_nextMacroScope_455_; lean_object* v_ngen_456_; lean_object* v_auxDeclNGen_457_; lean_object* v_cache_458_; lean_object* v_messages_459_; lean_object* v_infoState_460_; lean_object* v_snapshotTasks_461_; lean_object* v_newDecls_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_485_; 
v___x_452_ = lean_st_ref_take(v___y_419_);
v_traceState_453_ = lean_ctor_get(v___x_452_, 4);
v_env_454_ = lean_ctor_get(v___x_452_, 0);
v_nextMacroScope_455_ = lean_ctor_get(v___x_452_, 1);
v_ngen_456_ = lean_ctor_get(v___x_452_, 2);
v_auxDeclNGen_457_ = lean_ctor_get(v___x_452_, 3);
v_cache_458_ = lean_ctor_get(v___x_452_, 5);
v_messages_459_ = lean_ctor_get(v___x_452_, 6);
v_infoState_460_ = lean_ctor_get(v___x_452_, 7);
v_snapshotTasks_461_ = lean_ctor_get(v___x_452_, 8);
v_newDecls_462_ = lean_ctor_get(v___x_452_, 9);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_485_ == 0)
{
v___x_464_ = v___x_452_;
v_isShared_465_ = v_isSharedCheck_485_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_newDecls_462_);
lean_inc(v_snapshotTasks_461_);
lean_inc(v_infoState_460_);
lean_inc(v_messages_459_);
lean_inc(v_cache_458_);
lean_inc(v_traceState_453_);
lean_inc(v_auxDeclNGen_457_);
lean_inc(v_ngen_456_);
lean_inc(v_nextMacroScope_455_);
lean_inc(v_env_454_);
lean_dec(v___x_452_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_485_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint64_t v_tid_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_483_; 
v_tid_466_ = lean_ctor_get_uint64(v_traceState_453_, sizeof(void*)*1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_traceState_453_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_traceState_453_, 0);
lean_dec(v_unused_484_);
v___x_468_ = v_traceState_453_;
v_isShared_469_ = v_isSharedCheck_483_;
goto v_resetjp_467_;
}
else
{
lean_dec(v_traceState_453_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_483_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_ref_414_);
lean_ctor_set(v___x_470_, 1, v_a_448_);
v___x_471_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_412_, v___x_470_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_471_);
lean_ctor_set_uint64(v_reuseFailAlloc_482_, sizeof(void*)*1, v_tid_466_);
v___x_473_ = v_reuseFailAlloc_482_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v___x_473_);
v___x_475_ = v___x_464_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_env_454_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_nextMacroScope_455_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_ngen_456_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_auxDeclNGen_457_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v_cache_458_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v_messages_459_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_infoState_460_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v_snapshotTasks_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 9, v_newDecls_462_);
v___x_475_ = v_reuseFailAlloc_481_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_st_ref_set(v___y_419_, v___x_475_);
v___x_477_ = lean_box(0);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_477_);
v___x_479_ = v___x_450_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2___boxed(lean_object* v_oldTraces_487_, lean_object* v_data_488_, lean_object* v_ref_489_, lean_object* v_msg_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2(v_oldTraces_487_, v_data_488_, v_ref_489_, v_msg_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_496_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__0));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2(void){
_start:
{
lean_object* v___x_500_; double v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_float_of_nat(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__3));
v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
return v___x_504_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5(void){
_start:
{
lean_object* v___x_505_; double v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(1000u);
v___x_506_ = lean_float_of_nat(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(lean_object* v_cls_507_, uint8_t v_collapsed_508_, lean_object* v_tag_509_, lean_object* v_opts_510_, uint8_t v_clsEnabled_511_, lean_object* v_oldTraces_512_, lean_object* v_msg_513_, lean_object* v_resStartStop_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_fst_520_; lean_object* v_snd_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_620_; 
v_fst_520_ = lean_ctor_get(v_resStartStop_514_, 0);
v_snd_521_ = lean_ctor_get(v_resStartStop_514_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_resStartStop_514_);
if (v_isSharedCheck_620_ == 0)
{
v___x_523_ = v_resStartStop_514_;
v_isShared_524_ = v_isSharedCheck_620_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_snd_521_);
lean_inc(v_fst_520_);
lean_dec(v_resStartStop_514_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_620_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v_data_528_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_619_; 
v_fst_539_ = lean_ctor_get(v_snd_521_, 0);
v_snd_540_ = lean_ctor_get(v_snd_521_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_snd_521_);
if (v_isSharedCheck_619_ == 0)
{
v___x_542_ = v_snd_521_;
v_isShared_543_ = v_isSharedCheck_619_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_snd_540_);
lean_inc(v_fst_539_);
lean_dec(v_snd_521_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_619_;
goto v_resetjp_541_;
}
v___jp_525_:
{
lean_object* v___x_529_; 
lean_inc(v___y_526_);
v___x_529_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__2(v_oldTraces_512_, v_data_528_, v___y_526_, v___y_527_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; 
lean_dec_ref(v___x_529_);
v___x_530_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(v_fst_520_);
return v___x_530_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_fst_520_);
v_a_531_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_529_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
v_resetjp_541_:
{
lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___y_547_; lean_object* v_a_548_; uint8_t v___y_572_; double v___y_604_; 
v___x_544_ = l_Lean_trace_profiler;
v___x_545_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_510_, v___x_544_);
if (v___x_545_ == 0)
{
v___y_572_ = v___x_545_;
goto v___jp_571_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = l_Lean_trace_profiler_useHeartbeats;
v___x_610_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_510_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; double v___x_613_; double v___x_614_; double v___x_615_; 
v___x_611_ = l_Lean_trace_profiler_threshold;
v___x_612_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(v_opts_510_, v___x_611_);
v___x_613_ = lean_float_of_nat(v___x_612_);
v___x_614_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__5);
v___x_615_ = lean_float_div(v___x_613_, v___x_614_);
v___y_604_ = v___x_615_;
goto v___jp_603_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; double v___x_618_; 
v___x_616_ = l_Lean_trace_profiler_threshold;
v___x_617_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__4(v_opts_510_, v___x_616_);
v___x_618_ = lean_float_of_nat(v___x_617_);
v___y_604_ = v___x_618_;
goto v___jp_603_;
}
}
v___jp_546_:
{
uint8_t v_result_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v_result_549_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__1(v_fst_520_);
v___x_550_ = l_Lean_TraceResult_toEmoji(v_result_549_);
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
v___x_552_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__1);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 7);
lean_ctor_set(v___x_542_, 1, v___x_552_);
lean_ctor_set(v___x_542_, 0, v___x_551_);
v___x_554_ = v___x_542_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_565_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v_m_556_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set_tag(v___x_523_, 7);
lean_ctor_set(v___x_523_, 1, v_a_548_);
lean_ctor_set(v___x_523_, 0, v___x_554_);
v_m_556_ = v___x_523_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_a_548_);
v_m_556_ = v_reuseFailAlloc_564_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; double v___x_559_; lean_object* v_data_560_; 
v___x_557_ = lean_box(v_result_549_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___x_559_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__2);
lean_inc_ref(v_tag_509_);
lean_inc_ref(v___x_558_);
lean_inc(v_cls_507_);
v_data_560_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_560_, 0, v_cls_507_);
lean_ctor_set(v_data_560_, 1, v___x_558_);
lean_ctor_set(v_data_560_, 2, v_tag_509_);
lean_ctor_set_float(v_data_560_, sizeof(void*)*3, v___x_559_);
lean_ctor_set_float(v_data_560_, sizeof(void*)*3 + 8, v___x_559_);
lean_ctor_set_uint8(v_data_560_, sizeof(void*)*3 + 16, v_collapsed_508_);
if (v___x_545_ == 0)
{
lean_dec_ref(v___x_558_);
lean_dec(v_snd_540_);
lean_dec(v_fst_539_);
lean_dec_ref(v_tag_509_);
lean_dec(v_cls_507_);
v___y_526_ = v___y_547_;
v___y_527_ = v_m_556_;
v_data_528_ = v_data_560_;
goto v___jp_525_;
}
else
{
lean_object* v_data_561_; double v___x_562_; double v___x_563_; 
lean_dec_ref(v_data_560_);
v_data_561_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_561_, 0, v_cls_507_);
lean_ctor_set(v_data_561_, 1, v___x_558_);
lean_ctor_set(v_data_561_, 2, v_tag_509_);
v___x_562_ = lean_unbox_float(v_fst_539_);
lean_dec(v_fst_539_);
lean_ctor_set_float(v_data_561_, sizeof(void*)*3, v___x_562_);
v___x_563_ = lean_unbox_float(v_snd_540_);
lean_dec(v_snd_540_);
lean_ctor_set_float(v_data_561_, sizeof(void*)*3 + 8, v___x_563_);
lean_ctor_set_uint8(v_data_561_, sizeof(void*)*3 + 16, v_collapsed_508_);
v___y_526_ = v___y_547_;
v___y_527_ = v_m_556_;
v_data_528_ = v_data_561_;
goto v___jp_525_;
}
}
}
}
v___jp_566_:
{
lean_object* v_ref_567_; lean_object* v___x_568_; 
v_ref_567_ = lean_ctor_get(v___y_517_, 5);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v_fst_520_);
v___x_568_ = lean_apply_6(v_msg_513_, v_fst_520_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, lean_box(0));
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_568_);
v___y_547_ = v_ref_567_;
v_a_548_ = v_a_569_;
goto v___jp_546_;
}
else
{
lean_object* v___x_570_; 
lean_dec_ref(v___x_568_);
v___x_570_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___closed__4);
v___y_547_ = v_ref_567_;
v_a_548_ = v___x_570_;
goto v___jp_546_;
}
}
v___jp_571_:
{
if (v_clsEnabled_511_ == 0)
{
if (v___y_572_ == 0)
{
lean_object* v___x_573_; lean_object* v_traceState_574_; lean_object* v_env_575_; lean_object* v_nextMacroScope_576_; lean_object* v_ngen_577_; lean_object* v_auxDeclNGen_578_; lean_object* v_cache_579_; lean_object* v_messages_580_; lean_object* v_infoState_581_; lean_object* v_snapshotTasks_582_; lean_object* v_newDecls_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_602_; 
lean_del_object(v___x_542_);
lean_dec(v_snd_540_);
lean_dec(v_fst_539_);
lean_del_object(v___x_523_);
lean_dec_ref(v_msg_513_);
lean_dec_ref(v_tag_509_);
lean_dec(v_cls_507_);
v___x_573_ = lean_st_ref_take(v___y_518_);
v_traceState_574_ = lean_ctor_get(v___x_573_, 4);
v_env_575_ = lean_ctor_get(v___x_573_, 0);
v_nextMacroScope_576_ = lean_ctor_get(v___x_573_, 1);
v_ngen_577_ = lean_ctor_get(v___x_573_, 2);
v_auxDeclNGen_578_ = lean_ctor_get(v___x_573_, 3);
v_cache_579_ = lean_ctor_get(v___x_573_, 5);
v_messages_580_ = lean_ctor_get(v___x_573_, 6);
v_infoState_581_ = lean_ctor_get(v___x_573_, 7);
v_snapshotTasks_582_ = lean_ctor_get(v___x_573_, 8);
v_newDecls_583_ = lean_ctor_get(v___x_573_, 9);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_602_ == 0)
{
v___x_585_ = v___x_573_;
v_isShared_586_ = v_isSharedCheck_602_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_newDecls_583_);
lean_inc(v_snapshotTasks_582_);
lean_inc(v_infoState_581_);
lean_inc(v_messages_580_);
lean_inc(v_cache_579_);
lean_inc(v_traceState_574_);
lean_inc(v_auxDeclNGen_578_);
lean_inc(v_ngen_577_);
lean_inc(v_nextMacroScope_576_);
lean_inc(v_env_575_);
lean_dec(v___x_573_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_602_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
uint64_t v_tid_587_; lean_object* v_traces_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_601_; 
v_tid_587_ = lean_ctor_get_uint64(v_traceState_574_, sizeof(void*)*1);
v_traces_588_ = lean_ctor_get(v_traceState_574_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_traceState_574_);
if (v_isSharedCheck_601_ == 0)
{
v___x_590_ = v_traceState_574_;
v_isShared_591_ = v_isSharedCheck_601_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_traces_588_);
lean_dec(v_traceState_574_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_601_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_512_, v_traces_588_);
lean_dec_ref(v_traces_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_592_);
lean_ctor_set_uint64(v_reuseFailAlloc_600_, sizeof(void*)*1, v_tid_587_);
v___x_594_ = v_reuseFailAlloc_600_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v___x_594_);
v___x_596_ = v___x_585_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_env_575_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_nextMacroScope_576_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_ngen_577_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_auxDeclNGen_578_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_599_, 5, v_cache_579_);
lean_ctor_set(v_reuseFailAlloc_599_, 6, v_messages_580_);
lean_ctor_set(v_reuseFailAlloc_599_, 7, v_infoState_581_);
lean_ctor_set(v_reuseFailAlloc_599_, 8, v_snapshotTasks_582_);
lean_ctor_set(v_reuseFailAlloc_599_, 9, v_newDecls_583_);
v___x_596_ = v_reuseFailAlloc_599_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_st_ref_set(v___y_518_, v___x_596_);
v___x_598_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(v_fst_520_);
return v___x_598_;
}
}
}
}
}
else
{
goto v___jp_566_;
}
}
else
{
goto v___jp_566_;
}
}
v___jp_603_:
{
double v___x_605_; double v___x_606_; double v___x_607_; uint8_t v___x_608_; 
v___x_605_ = lean_unbox_float(v_snd_540_);
v___x_606_ = lean_unbox_float(v_fst_539_);
v___x_607_ = lean_float_sub(v___x_605_, v___x_606_);
v___x_608_ = lean_float_decLt(v___y_604_, v___x_607_);
v___y_572_ = v___x_608_;
goto v___jp_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___boxed(lean_object* v_cls_621_, lean_object* v_collapsed_622_, lean_object* v_tag_623_, lean_object* v_opts_624_, lean_object* v_clsEnabled_625_, lean_object* v_oldTraces_626_, lean_object* v_msg_627_, lean_object* v_resStartStop_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
uint8_t v_collapsed_boxed_634_; uint8_t v_clsEnabled_boxed_635_; lean_object* v_res_636_; 
v_collapsed_boxed_634_ = lean_unbox(v_collapsed_622_);
v_clsEnabled_boxed_635_ = lean_unbox(v_clsEnabled_625_);
v_res_636_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(v_cls_621_, v_collapsed_boxed_634_, v_tag_623_, v_opts_624_, v_clsEnabled_boxed_635_, v_oldTraces_626_, v_msg_627_, v_resStartStop_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_opts_624_);
return v_res_636_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4));
v___x_649_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__6));
v___x_650_ = l_Lean_Name_append(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8(void){
_start:
{
lean_object* v___x_651_; double v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(1000000000u);
v___x_652_ = lean_float_of_nat(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(lean_object* v_ctx_653_, lean_object* v___f_654_, lean_object* v_x_655_, lean_object* v_reflectionResult_656_, lean_object* v_x_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_options_663_; uint8_t v_hasTrace_664_; 
v_options_663_ = lean_ctor_get(v___y_660_, 2);
v_hasTrace_664_ = lean_ctor_get_uint8(v_options_663_, sizeof(void*)*1);
if (v_hasTrace_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v___f_654_);
v___x_665_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_653_, v_reflectionResult_656_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_676_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_676_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_a_666_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_672_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
v_a_677_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_665_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_665_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v_a_693_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v_a_708_; 
v_inheritedTraceOptions_685_ = lean_ctor_get(v___y_660_, 13);
v___x_686_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4));
v___x_687_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
v___x_688_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__7);
v___x_689_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_685_, v_options_663_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = l_Lean_trace_profiler;
v___x_771_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_663_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec_ref(v___f_654_);
v___x_772_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_653_, v_reflectionResult_656_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_782_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_782_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_a_773_);
lean_ctor_set(v___x_777_, 1, v___x_687_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_778_);
v___x_780_ = v___x_775_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_772_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_772_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
goto v___jp_717_;
}
}
else
{
goto v___jp_717_;
}
v___jp_690_:
{
lean_object* v___x_694_; double v___x_695_; double v___x_696_; double v___x_697_; double v___x_698_; double v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_694_ = lean_io_mono_nanos_now();
v___x_695_ = lean_float_of_nat(v___y_691_);
v___x_696_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__8);
v___x_697_ = lean_float_div(v___x_695_, v___x_696_);
v___x_698_ = lean_float_of_nat(v___x_694_);
v___x_699_ = lean_float_div(v___x_698_, v___x_696_);
v___x_700_ = lean_box_float(v___x_697_);
v___x_701_ = lean_box_float(v___x_699_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_a_693_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(v___x_686_, v_hasTrace_664_, v___x_687_, v_options_663_, v___x_689_, v___y_692_, v___f_654_, v___x_703_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_704_;
}
v___jp_705_:
{
lean_object* v___x_709_; double v___x_710_; double v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_709_ = lean_io_get_num_heartbeats();
v___x_710_ = lean_float_of_nat(v___y_706_);
v___x_711_ = lean_float_of_nat(v___x_709_);
v___x_712_ = lean_box_float(v___x_710_);
v___x_713_ = lean_box_float(v___x_711_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_a_708_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(v___x_686_, v_hasTrace_664_, v___x_687_, v_options_663_, v___x_689_, v___y_707_, v___f_654_, v___x_715_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_716_;
}
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_769_; 
v___x_718_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v___y_661_);
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_769_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_769_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_769_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = l_Lean_trace_profiler_useHeartbeats;
v___x_724_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_663_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_io_mono_nanos_now();
v___x_726_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_653_, v_reflectionResult_656_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_738_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_738_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_738_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_738_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_a_727_);
lean_ctor_set(v___x_731_, 1, v___x_687_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 1);
lean_ctor_set(v___x_721_, 0, v___x_733_);
v___x_735_ = v___x_721_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v___y_691_ = v___x_725_;
v___y_692_ = v_a_719_;
v_a_693_ = v___x_735_;
goto v___jp_690_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_del_object(v___x_721_);
v_a_739_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_726_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_726_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set_tag(v___x_741_, 0);
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
v___y_691_ = v___x_725_;
v___y_692_ = v_a_719_;
v_a_693_ = v___x_744_;
goto v___jp_690_;
}
}
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_io_get_num_heartbeats();
v___x_748_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_653_, v_reflectionResult_656_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_760_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_760_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_760_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_760_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_a_749_);
lean_ctor_set(v___x_753_, 1, v___x_687_);
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 1);
lean_ctor_set(v___x_751_, 0, v___x_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 1);
lean_ctor_set(v___x_721_, 0, v___x_755_);
v___x_757_ = v___x_721_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
v___y_706_ = v___x_747_;
v___y_707_ = v_a_719_;
v_a_708_ = v___x_757_;
goto v___jp_705_;
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_del_object(v___x_721_);
v_a_761_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_748_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_748_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 0);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
v___y_706_ = v___x_747_;
v___y_707_ = v_a_719_;
v_a_708_ = v___x_766_;
goto v___jp_705_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed(lean_object* v_ctx_791_, lean_object* v___f_792_, lean_object* v_x_793_, lean_object* v_reflectionResult_794_, lean_object* v_x_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(v_ctx_791_, v___f_792_, v_x_793_, v_reflectionResult_794_, v_x_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec_ref(v_x_795_);
lean_dec(v_x_793_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object* v_g_803_, lean_object* v_ctx_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___f_810_; lean_object* v_unsatProver_811_; lean_object* v___x_812_; 
v___f_810_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0));
v_unsatProver_811_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed), 10, 2);
lean_closure_set(v_unsatProver_811_, 0, v_ctx_804_);
lean_closure_set(v_unsatProver_811_, 1, v___f_810_);
v___x_812_ = l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(v_g_803_, v_unsatProver_811_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_820_; 
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_821_);
v___x_814_ = v___x_812_;
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
else
{
lean_dec(v___x_812_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_box(0);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_822_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_812_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_812_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___boxed(lean_object* v_g_830_, lean_object* v_ctx_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(v_g_830_, v_ctx_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3(lean_object* v_00_u03b1_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___redArg(v_x_839_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3___boxed(lean_object* v_00_u03b1_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1_spec__3(v_00_u03b1_846_, v_x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_853_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_box(0);
v___x_855_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(lean_object* v_00_u03b1_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___boxed(lean_object* v_00_u03b1_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(v_00_u03b1_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_883_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_890_, uint8_t v_suppressElabErrors_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_892_) == 1)
{
lean_object* v_pre_893_; 
v_pre_893_ = lean_ctor_get(v_x_892_, 0);
switch(lean_obj_tag(v_pre_893_))
{
case 1:
{
lean_object* v_pre_894_; 
v_pre_894_ = lean_ctor_get(v_pre_893_, 0);
switch(lean_obj_tag(v_pre_894_))
{
case 0:
{
lean_object* v_str_895_; lean_object* v_str_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_str_895_ = lean_ctor_get(v_x_892_, 1);
v_str_896_ = lean_ctor_get(v_pre_893_, 1);
v___x_897_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_898_ = lean_string_dec_eq(v_str_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2));
v___x_900_ = lean_string_dec_eq(v_str_896_, v___x_899_);
if (v___x_900_ == 0)
{
return v___y_890_;
}
else
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_902_ = lean_string_dec_eq(v_str_895_, v___x_901_);
if (v___x_902_ == 0)
{
return v___y_890_;
}
else
{
return v_suppressElabErrors_891_;
}
}
}
else
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_904_ = lean_string_dec_eq(v_str_895_, v___x_903_);
if (v___x_904_ == 0)
{
return v___y_890_;
}
else
{
return v_suppressElabErrors_891_;
}
}
}
case 1:
{
lean_object* v_pre_905_; 
v_pre_905_ = lean_ctor_get(v_pre_894_, 0);
if (lean_obj_tag(v_pre_905_) == 0)
{
lean_object* v_str_906_; lean_object* v_str_907_; lean_object* v_str_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_str_906_ = lean_ctor_get(v_x_892_, 1);
v_str_907_ = lean_ctor_get(v_pre_893_, 1);
v_str_908_ = lean_ctor_get(v_pre_894_, 1);
v___x_909_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_910_ = lean_string_dec_eq(v_str_908_, v___x_909_);
if (v___x_910_ == 0)
{
return v___y_890_;
}
else
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_912_ = lean_string_dec_eq(v_str_907_, v___x_911_);
if (v___x_912_ == 0)
{
return v___y_890_;
}
else
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_914_ = lean_string_dec_eq(v_str_906_, v___x_913_);
if (v___x_914_ == 0)
{
return v___y_890_;
}
else
{
return v_suppressElabErrors_891_;
}
}
}
}
else
{
return v___y_890_;
}
}
default: 
{
return v___y_890_;
}
}
}
case 0:
{
lean_object* v_str_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_str_915_ = lean_ctor_get(v_x_892_, 1);
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5));
v___x_917_ = lean_string_dec_eq(v_str_915_, v___x_916_);
if (v___x_917_ == 0)
{
return v___y_890_;
}
else
{
return v_suppressElabErrors_891_;
}
}
default: 
{
return v___y_890_;
}
}
}
else
{
return v___y_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_918_, lean_object* v_suppressElabErrors_919_, lean_object* v_x_920_){
_start:
{
uint8_t v___y_6522__boxed_921_; uint8_t v_suppressElabErrors_boxed_922_; uint8_t v_res_923_; lean_object* v_r_924_; 
v___y_6522__boxed_921_ = lean_unbox(v___y_918_);
v_suppressElabErrors_boxed_922_ = lean_unbox(v_suppressElabErrors_919_);
v_res_923_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(v___y_6522__boxed_921_, v_suppressElabErrors_boxed_922_, v_x_920_);
lean_dec(v_x_920_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object* v_ref_925_, lean_object* v_msgData_926_, uint8_t v_severity_927_, uint8_t v_isSilent_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___y_935_; lean_object* v___y_936_; uint8_t v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; uint8_t v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_972_; lean_object* v___y_973_; uint8_t v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; uint8_t v___y_977_; uint8_t v___y_978_; lean_object* v___y_979_; lean_object* v___y_997_; uint8_t v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; uint8_t v___y_1002_; uint8_t v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; uint8_t v___y_1012_; uint8_t v___y_1013_; uint8_t v___y_1014_; uint8_t v___x_1019_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; uint8_t v___y_1025_; uint8_t v___y_1026_; uint8_t v___y_1027_; uint8_t v___y_1029_; uint8_t v___x_1044_; 
v___x_1019_ = 2;
v___x_1044_ = l_Lean_instBEqMessageSeverity_beq(v_severity_927_, v___x_1019_);
if (v___x_1044_ == 0)
{
v___y_1029_ = v___x_1044_;
goto v___jp_1028_;
}
else
{
uint8_t v___x_1045_; 
lean_inc_ref(v_msgData_926_);
v___x_1045_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_926_);
v___y_1029_ = v___x_1045_;
goto v___jp_1028_;
}
v___jp_934_:
{
lean_object* v___x_944_; lean_object* v_currNamespace_945_; lean_object* v_openDecls_946_; lean_object* v_env_947_; lean_object* v_nextMacroScope_948_; lean_object* v_ngen_949_; lean_object* v_auxDeclNGen_950_; lean_object* v_traceState_951_; lean_object* v_cache_952_; lean_object* v_messages_953_; lean_object* v_infoState_954_; lean_object* v_snapshotTasks_955_; lean_object* v_newDecls_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_970_; 
v___x_944_ = lean_st_ref_take(v___y_943_);
v_currNamespace_945_ = lean_ctor_get(v___y_942_, 6);
v_openDecls_946_ = lean_ctor_get(v___y_942_, 7);
v_env_947_ = lean_ctor_get(v___x_944_, 0);
v_nextMacroScope_948_ = lean_ctor_get(v___x_944_, 1);
v_ngen_949_ = lean_ctor_get(v___x_944_, 2);
v_auxDeclNGen_950_ = lean_ctor_get(v___x_944_, 3);
v_traceState_951_ = lean_ctor_get(v___x_944_, 4);
v_cache_952_ = lean_ctor_get(v___x_944_, 5);
v_messages_953_ = lean_ctor_get(v___x_944_, 6);
v_infoState_954_ = lean_ctor_get(v___x_944_, 7);
v_snapshotTasks_955_ = lean_ctor_get(v___x_944_, 8);
v_newDecls_956_ = lean_ctor_get(v___x_944_, 9);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_970_ == 0)
{
v___x_958_ = v___x_944_;
v_isShared_959_ = v_isSharedCheck_970_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_newDecls_956_);
lean_inc(v_snapshotTasks_955_);
lean_inc(v_infoState_954_);
lean_inc(v_messages_953_);
lean_inc(v_cache_952_);
lean_inc(v_traceState_951_);
lean_inc(v_auxDeclNGen_950_);
lean_inc(v_ngen_949_);
lean_inc(v_nextMacroScope_948_);
lean_inc(v_env_947_);
lean_dec(v___x_944_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_970_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
lean_inc(v_openDecls_946_);
lean_inc(v_currNamespace_945_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_currNamespace_945_);
lean_ctor_set(v___x_960_, 1, v_openDecls_946_);
v___x_961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___y_939_);
lean_inc_ref(v___y_936_);
lean_inc_ref(v___y_938_);
v___x_962_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_962_, 0, v___y_938_);
lean_ctor_set(v___x_962_, 1, v___y_935_);
lean_ctor_set(v___x_962_, 2, v___y_940_);
lean_ctor_set(v___x_962_, 3, v___y_936_);
lean_ctor_set(v___x_962_, 4, v___x_961_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*5, v___y_941_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*5 + 1, v___y_937_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*5 + 2, v_isSilent_928_);
v___x_963_ = l_Lean_MessageLog_add(v___x_962_, v_messages_953_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 6, v___x_963_);
v___x_965_ = v___x_958_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_env_947_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_nextMacroScope_948_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_ngen_949_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_auxDeclNGen_950_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_traceState_951_);
lean_ctor_set(v_reuseFailAlloc_969_, 5, v_cache_952_);
lean_ctor_set(v_reuseFailAlloc_969_, 6, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_969_, 7, v_infoState_954_);
lean_ctor_set(v_reuseFailAlloc_969_, 8, v_snapshotTasks_955_);
lean_ctor_set(v_reuseFailAlloc_969_, 9, v_newDecls_956_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = lean_st_ref_set(v___y_943_, v___x_965_);
v___x_967_ = lean_box(0);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
}
v___jp_971_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_995_; 
v___x_980_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_926_);
v___x_981_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v___x_980_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_995_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_995_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_995_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_inc_ref_n(v___y_976_, 2);
v___x_986_ = l_Lean_FileMap_toPosition(v___y_976_, v___y_975_);
lean_dec(v___y_975_);
v___x_987_ = l_Lean_FileMap_toPosition(v___y_976_, v___y_979_);
lean_dec(v___y_979_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
v___x_989_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
if (v___y_977_ == 0)
{
lean_del_object(v___x_984_);
lean_dec_ref(v___y_972_);
v___y_935_ = v___x_986_;
v___y_936_ = v___x_989_;
v___y_937_ = v___y_974_;
v___y_938_ = v___y_973_;
v___y_939_ = v_a_982_;
v___y_940_ = v___x_988_;
v___y_941_ = v___y_978_;
v___y_942_ = v___y_931_;
v___y_943_ = v___y_932_;
goto v___jp_934_;
}
else
{
uint8_t v___x_990_; 
lean_inc(v_a_982_);
v___x_990_ = l_Lean_MessageData_hasTag(v___y_972_, v_a_982_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec_ref(v___x_988_);
lean_dec_ref(v___x_986_);
lean_dec(v_a_982_);
v___x_991_ = lean_box(0);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_991_);
v___x_993_ = v___x_984_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_del_object(v___x_984_);
v___y_935_ = v___x_986_;
v___y_936_ = v___x_989_;
v___y_937_ = v___y_974_;
v___y_938_ = v___y_973_;
v___y_939_ = v_a_982_;
v___y_940_ = v___x_988_;
v___y_941_ = v___y_978_;
v___y_942_ = v___y_931_;
v___y_943_ = v___y_932_;
goto v___jp_934_;
}
}
}
}
v___jp_996_:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Syntax_getTailPos_x3f(v___y_1001_, v___y_1003_);
lean_dec(v___y_1001_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_inc(v___y_1004_);
v___y_972_ = v___y_997_;
v___y_973_ = v___y_999_;
v___y_974_ = v___y_998_;
v___y_975_ = v___y_1004_;
v___y_976_ = v___y_1000_;
v___y_977_ = v___y_1002_;
v___y_978_ = v___y_1003_;
v___y_979_ = v___y_1004_;
goto v___jp_971_;
}
else
{
lean_object* v_val_1006_; 
v_val_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_val_1006_);
lean_dec_ref(v___x_1005_);
v___y_972_ = v___y_997_;
v___y_973_ = v___y_999_;
v___y_974_ = v___y_998_;
v___y_975_ = v___y_1004_;
v___y_976_ = v___y_1000_;
v___y_977_ = v___y_1002_;
v___y_978_ = v___y_1003_;
v___y_979_ = v_val_1006_;
goto v___jp_971_;
}
}
v___jp_1007_:
{
lean_object* v_ref_1015_; lean_object* v___x_1016_; 
v_ref_1015_ = l_Lean_replaceRef(v_ref_925_, v___y_1009_);
v___x_1016_ = l_Lean_Syntax_getPos_x3f(v_ref_1015_, v___y_1013_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___y_997_ = v___y_1008_;
v___y_998_ = v___y_1014_;
v___y_999_ = v___y_1010_;
v___y_1000_ = v___y_1011_;
v___y_1001_ = v_ref_1015_;
v___y_1002_ = v___y_1012_;
v___y_1003_ = v___y_1013_;
v___y_1004_ = v___x_1017_;
goto v___jp_996_;
}
else
{
lean_object* v_val_1018_; 
v_val_1018_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_val_1018_);
lean_dec_ref(v___x_1016_);
v___y_997_ = v___y_1008_;
v___y_998_ = v___y_1014_;
v___y_999_ = v___y_1010_;
v___y_1000_ = v___y_1011_;
v___y_1001_ = v_ref_1015_;
v___y_1002_ = v___y_1012_;
v___y_1003_ = v___y_1013_;
v___y_1004_ = v_val_1018_;
goto v___jp_996_;
}
}
v___jp_1020_:
{
if (v___y_1027_ == 0)
{
v___y_1008_ = v___y_1023_;
v___y_1009_ = v___y_1021_;
v___y_1010_ = v___y_1022_;
v___y_1011_ = v___y_1024_;
v___y_1012_ = v___y_1025_;
v___y_1013_ = v___y_1026_;
v___y_1014_ = v_severity_927_;
goto v___jp_1007_;
}
else
{
v___y_1008_ = v___y_1023_;
v___y_1009_ = v___y_1021_;
v___y_1010_ = v___y_1022_;
v___y_1011_ = v___y_1024_;
v___y_1012_ = v___y_1025_;
v___y_1013_ = v___y_1026_;
v___y_1014_ = v___x_1019_;
goto v___jp_1007_;
}
}
v___jp_1028_:
{
if (v___y_1029_ == 0)
{
lean_object* v_fileName_1030_; lean_object* v_fileMap_1031_; lean_object* v_options_1032_; lean_object* v_ref_1033_; uint8_t v_suppressElabErrors_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; uint8_t v___x_1038_; uint8_t v___x_1039_; 
v_fileName_1030_ = lean_ctor_get(v___y_931_, 0);
v_fileMap_1031_ = lean_ctor_get(v___y_931_, 1);
v_options_1032_ = lean_ctor_get(v___y_931_, 2);
v_ref_1033_ = lean_ctor_get(v___y_931_, 5);
v_suppressElabErrors_1034_ = lean_ctor_get_uint8(v___y_931_, sizeof(void*)*14 + 1);
v___x_1035_ = lean_box(v___y_1029_);
v___x_1036_ = lean_box(v_suppressElabErrors_1034_);
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1037_, 0, v___x_1035_);
lean_closure_set(v___f_1037_, 1, v___x_1036_);
v___x_1038_ = 1;
v___x_1039_ = l_Lean_instBEqMessageSeverity_beq(v_severity_927_, v___x_1038_);
if (v___x_1039_ == 0)
{
v___y_1021_ = v_ref_1033_;
v___y_1022_ = v_fileName_1030_;
v___y_1023_ = v___f_1037_;
v___y_1024_ = v_fileMap_1031_;
v___y_1025_ = v_suppressElabErrors_1034_;
v___y_1026_ = v___y_1029_;
v___y_1027_ = v___x_1039_;
goto v___jp_1020_;
}
else
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = l_Lean_warningAsError;
v___x_1041_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1032_, v___x_1040_);
v___y_1021_ = v_ref_1033_;
v___y_1022_ = v_fileName_1030_;
v___y_1023_ = v___f_1037_;
v___y_1024_ = v_fileMap_1031_;
v___y_1025_ = v_suppressElabErrors_1034_;
v___y_1026_ = v___y_1029_;
v___y_1027_ = v___x_1041_;
goto v___jp_1020_;
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref(v_msgData_926_);
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_1046_, lean_object* v_msgData_1047_, lean_object* v_severity_1048_, lean_object* v_isSilent_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v_severity_boxed_1055_; uint8_t v_isSilent_boxed_1056_; lean_object* v_res_1057_; 
v_severity_boxed_1055_ = lean_unbox(v_severity_1048_);
v_isSilent_boxed_1056_ = lean_unbox(v_isSilent_1049_);
v_res_1057_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1046_, v_msgData_1047_, v_severity_boxed_1055_, v_isSilent_boxed_1056_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v_ref_1046_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(lean_object* v_msgData_1058_, uint8_t v_severity_1059_, uint8_t v_isSilent_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_ref_1066_; lean_object* v___x_1067_; 
v_ref_1066_ = lean_ctor_get(v___y_1063_, 5);
v___x_1067_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1066_, v_msgData_1058_, v_severity_1059_, v_isSilent_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object* v_msgData_1068_, lean_object* v_severity_1069_, lean_object* v_isSilent_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v_severity_boxed_1076_; uint8_t v_isSilent_boxed_1077_; lean_object* v_res_1078_; 
v_severity_boxed_1076_ = lean_unbox(v_severity_1069_);
v_isSilent_boxed_1077_ = lean_unbox(v_isSilent_1070_);
v_res_1078_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1068_, v_severity_boxed_1076_, v_isSilent_boxed_1077_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(lean_object* v_msgData_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = 1;
v___x_1086_ = 0;
v___x_1087_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1079_, v___x_1085_, v___x_1086_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1___boxed(lean_object* v_msgData_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(v_msgData_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1094_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__0));
v___x_1097_ = l_Lean_stringToMessageData(v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(lean_object* v_a_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v_tk_1109_, lean_object* v_a_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___y_1121_; lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1112_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(v_a_1134_, v_a_1104_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1135_);
if (lean_obj_tag(v_a_1136_) == 0)
{
lean_object* v_ref_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec_ref(v_a_1110_);
v_ref_1137_ = lean_ctor_get(v___y_1117_, 5);
v___x_1138_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1);
v___x_1139_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(v___x_1138_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1161_; 
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v___x_1139_, 0);
lean_dec(v_unused_1162_);
v___x_1141_ = v___x_1139_;
v_isShared_1142_ = v_isSharedCheck_1161_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v___x_1139_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1161_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1143_ = 0;
v___x_1144_ = l_Lean_SourceInfo_fromRef(v_ref_1137_, v___x_1143_);
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__2));
lean_inc(v___x_1144_);
v___x_1146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__4));
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__5));
v___x_1149_ = l_Lean_Name_mkStr4(v___x_1105_, v___x_1106_, v___x_1107_, v___x_1148_);
v___x_1150_ = l_Lean_Syntax_node2(v___x_1144_, v___x_1149_, v___x_1146_, v___x_1108_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1147_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
lean_ctor_set(v___x_1153_, 2, v___x_1152_);
lean_ctor_set(v___x_1153_, 3, v___x_1152_);
lean_ctor_set(v___x_1153_, 4, v___x_1152_);
lean_ctor_set(v___x_1153_, 5, v___x_1152_);
lean_inc(v_ref_1137_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
lean_ctor_set(v___x_1141_, 0, v_ref_1137_);
v___x_1155_ = v___x_1141_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_ref_1137_);
v___x_1155_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__6));
v___x_1157_ = 4;
v___x_1158_ = l_Lean_MessageData_nil;
v___x_1159_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1109_, v___x_1153_, v___x_1155_, v___x_1156_, v___x_1152_, v___x_1157_, v___x_1158_, v___y_1117_, v___y_1118_);
v___y_1121_ = v___x_1159_;
goto v___jp_1120_;
}
}
}
else
{
lean_dec(v_tk_1109_);
lean_dec(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
v___y_1121_ = v___x_1139_;
goto v___jp_1120_;
}
}
else
{
lean_object* v_val_1163_; lean_object* v___x_1164_; 
lean_dec(v_tk_1109_);
lean_dec(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
v_val_1163_ = lean_ctor_get(v_a_1136_, 0);
lean_inc(v_val_1163_);
lean_dec_ref(v_a_1136_);
v___x_1164_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(v_val_1163_, v_a_1110_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
v___y_1121_ = v___x_1164_;
goto v___jp_1120_;
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v_a_1110_);
lean_dec(v_tk_1109_);
lean_dec(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
v_a_1165_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1135_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1135_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_a_1110_);
lean_dec(v_tk_1109_);
lean_dec(v___x_1108_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v___x_1106_);
lean_dec_ref(v___x_1105_);
v_a_1173_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1133_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1133_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
v___jp_1120_:
{
if (lean_obj_tag(v___y_1121_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v___y_1121_);
v___x_1122_ = lean_box(0);
v___x_1123_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1122_, v___y_1112_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1131_; 
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v___x_1123_, 0);
lean_dec(v_unused_1132_);
v___x_1125_ = v___x_1123_;
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v___x_1123_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_box(0);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
else
{
return v___x_1123_;
}
}
else
{
return v___y_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed(lean_object* v_a_1181_, lean_object* v___x_1182_, lean_object* v___x_1183_, lean_object* v___x_1184_, lean_object* v___x_1185_, lean_object* v_tk_1186_, lean_object* v_a_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(v_a_1181_, v___x_1182_, v___x_1183_, v___x_1184_, v___x_1185_, v_tk_1186_, v_a_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v_a_1181_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(lean_object* v_x_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1225_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0));
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1));
v___x_1227_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2));
v___x_1228_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3));
lean_inc(v_x_1215_);
v___x_1229_ = l_Lean_Syntax_isOfKind(v_x_1215_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
lean_dec(v_x_1215_);
v___x_1230_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = l_Lean_Syntax_getArg(v_x_1215_, v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5));
lean_inc(v___x_1232_);
v___x_1234_ = l_Lean_Syntax_isOfKind(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v___x_1232_);
lean_dec(v_x_1215_);
v___x_1235_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v_path_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1236_ = lean_unsigned_to_nat(2u);
v_path_1237_ = l_Lean_Syntax_getArg(v_x_1215_, v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__7));
lean_inc(v_path_1237_);
v___x_1239_ = l_Lean_Syntax_isOfKind(v_path_1237_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec(v_path_1237_);
lean_dec(v___x_1232_);
lean_dec(v_x_1215_);
v___x_1240_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; 
lean_inc(v___x_1232_);
v___x_1241_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v___x_1232_, v_a_1216_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_n(v_a_1242_, 2);
lean_dec_ref(v___x_1241_);
v___x_1243_ = l_Lean_TSyntax_getString(v_path_1237_);
lean_dec(v_path_1237_);
v___x_1244_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(v___x_1243_, v_a_1242_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v_tk_1247_; lean_object* v___f_1248_; lean_object* v___x_1249_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = lean_unsigned_to_nat(0u);
v_tk_1247_ = l_Lean_Syntax_getArg(v_x_1215_, v___x_1246_);
lean_dec(v_x_1215_);
v___f_1248_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1248_, 0, v_a_1242_);
lean_closure_set(v___f_1248_, 1, v___x_1225_);
lean_closure_set(v___f_1248_, 2, v___x_1226_);
lean_closure_set(v___f_1248_, 3, v___x_1227_);
lean_closure_set(v___f_1248_, 4, v___x_1232_);
lean_closure_set(v___f_1248_, 5, v_tk_1247_);
lean_closure_set(v___f_1248_, 6, v_a_1245_);
v___x_1249_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1248_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_a_1242_);
lean_dec(v___x_1232_);
lean_dec(v_x_1215_);
v_a_1250_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1244_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1244_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_path_1237_);
lean_dec(v___x_1232_);
lean_dec(v_x_1215_);
v_a_1258_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1241_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1241_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed(lean_object* v_x_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(v_x_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1290_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1291_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3));
v___x_1292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4));
v___x_1293_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed), 10, 0);
v___x_1294_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1290_, v___x_1291_, v___x_1292_, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___boxed(lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_0__Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1();
return v_res_1296_;
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
