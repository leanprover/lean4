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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Preparing LRAT reflection term"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvCheck"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(184, 210, 190, 202, 6, 52, 139, 149)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value_aux_5),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(215, 212, 31, 122, 239, 8, 183, 192)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___boxed(lean_object*);
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
lean_inc(v_macroStack_118_);
lean_dec_ref(v___y_108_);
lean_inc(v_macroStack_118_);
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
lean_dec_ref(v_a_149_);
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
lean_inc_ref(v_a_145_);
v___x_168_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0___redArg(v___x_167_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec_ref(v_a_149_);
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
lean_inc_ref(v___y_179_);
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
lean_inc_ref(v_a_223_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(lean_object* v_cls_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_options_283_; uint8_t v_hasTrace_284_; 
v_options_283_ = lean_ctor_get(v___y_281_, 2);
v_hasTrace_284_ = lean_ctor_get_uint8(v_options_283_, sizeof(void*)*1);
if (v_hasTrace_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_cls_280_);
v___x_285_ = lean_box(v_hasTrace_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v_inheritedTraceOptions_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_inheritedTraceOptions_287_ = lean_ctor_get(v___y_281_, 13);
v___x_288_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__1));
v___x_289_ = l_Lean_Name_append(v___x_288_, v_cls_280_);
v___x_290_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_287_, v_options_283_, v___x_289_);
lean_dec(v___x_289_);
v___x_291_ = lean_box(v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___boxed(lean_object* v_cls_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v_cls_293_, v___y_294_);
lean_dec_ref(v___y_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0(lean_object* v_cls_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v_cls_297_, v___y_300_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___boxed(lean_object* v_cls_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0(v_cls_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_310_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_unsigned_to_nat(32u);
v___x_312_ = lean_mk_empty_array_with_capacity(v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_314_ = ((size_t)5ULL);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_unsigned_to_nat(32u);
v___x_317_ = lean_mk_empty_array_with_capacity(v___x_316_);
v___x_318_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__0);
v___x_319_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_315_);
lean_ctor_set(v___x_319_, 3, v___x_315_);
lean_ctor_set_usize(v___x_319_, 4, v___x_314_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg(lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; lean_object* v_traceState_323_; lean_object* v_traces_324_; lean_object* v___x_325_; lean_object* v_traceState_326_; lean_object* v_env_327_; lean_object* v_nextMacroScope_328_; lean_object* v_ngen_329_; lean_object* v_auxDeclNGen_330_; lean_object* v_cache_331_; lean_object* v_messages_332_; lean_object* v_infoState_333_; lean_object* v_snapshotTasks_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_353_; 
v___x_322_ = lean_st_ref_get(v___y_320_);
v_traceState_323_ = lean_ctor_get(v___x_322_, 4);
lean_inc_ref(v_traceState_323_);
lean_dec(v___x_322_);
v_traces_324_ = lean_ctor_get(v_traceState_323_, 0);
lean_inc_ref(v_traces_324_);
lean_dec_ref(v_traceState_323_);
v___x_325_ = lean_st_ref_take(v___y_320_);
v_traceState_326_ = lean_ctor_get(v___x_325_, 4);
v_env_327_ = lean_ctor_get(v___x_325_, 0);
v_nextMacroScope_328_ = lean_ctor_get(v___x_325_, 1);
v_ngen_329_ = lean_ctor_get(v___x_325_, 2);
v_auxDeclNGen_330_ = lean_ctor_get(v___x_325_, 3);
v_cache_331_ = lean_ctor_get(v___x_325_, 5);
v_messages_332_ = lean_ctor_get(v___x_325_, 6);
v_infoState_333_ = lean_ctor_get(v___x_325_, 7);
v_snapshotTasks_334_ = lean_ctor_get(v___x_325_, 8);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_353_ == 0)
{
v___x_336_ = v___x_325_;
v_isShared_337_ = v_isSharedCheck_353_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snapshotTasks_334_);
lean_inc(v_infoState_333_);
lean_inc(v_messages_332_);
lean_inc(v_cache_331_);
lean_inc(v_traceState_326_);
lean_inc(v_auxDeclNGen_330_);
lean_inc(v_ngen_329_);
lean_inc(v_nextMacroScope_328_);
lean_inc(v_env_327_);
lean_dec(v___x_325_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_353_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint64_t v_tid_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_351_; 
v_tid_338_ = lean_ctor_get_uint64(v_traceState_326_, sizeof(void*)*1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_traceState_326_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; 
v_unused_352_ = lean_ctor_get(v_traceState_326_, 0);
lean_dec(v_unused_352_);
v___x_340_ = v_traceState_326_;
v_isShared_341_ = v_isSharedCheck_351_;
goto v_resetjp_339_;
}
else
{
lean_dec(v_traceState_326_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_351_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___closed__1);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_342_);
lean_ctor_set_uint64(v_reuseFailAlloc_350_, sizeof(void*)*1, v_tid_338_);
v___x_344_ = v_reuseFailAlloc_350_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 4, v___x_344_);
v___x_346_ = v___x_336_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_env_327_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_nextMacroScope_328_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_ngen_329_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_auxDeclNGen_330_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_349_, 5, v_cache_331_);
lean_ctor_set(v_reuseFailAlloc_349_, 6, v_messages_332_);
lean_ctor_set(v_reuseFailAlloc_349_, 7, v_infoState_333_);
lean_ctor_set(v_reuseFailAlloc_349_, 8, v_snapshotTasks_334_);
v___x_346_ = v_reuseFailAlloc_349_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_st_ref_set(v___y_320_, v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_traces_324_);
return v___x_348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg___boxed(lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg(v___y_354_);
lean_dec(v___y_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg(v___y_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___boxed(lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1(v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_368_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__1));
v___x_373_ = l_Lean_MessageData_ofFormat(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0(lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___closed__2);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0___boxed(lean_object* v_x_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__0(v_x_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec_ref(v_x_382_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3_spec__4(size_t v_sz_389_, size_t v_i_390_, lean_object* v_bs_391_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_lt(v_i_390_, v_sz_389_);
if (v___x_392_ == 0)
{
return v_bs_391_;
}
else
{
lean_object* v_v_393_; lean_object* v_msg_394_; lean_object* v___x_395_; lean_object* v_bs_x27_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v_v_393_ = lean_array_uget_borrowed(v_bs_391_, v_i_390_);
v_msg_394_ = lean_ctor_get(v_v_393_, 1);
lean_inc_ref(v_msg_394_);
v___x_395_ = lean_unsigned_to_nat(0u);
v_bs_x27_396_ = lean_array_uset(v_bs_391_, v_i_390_, v___x_395_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_390_, v___x_397_);
v___x_399_ = lean_array_uset(v_bs_x27_396_, v_i_390_, v_msg_394_);
v_i_390_ = v___x_398_;
v_bs_391_ = v___x_399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_401_, lean_object* v_i_402_, lean_object* v_bs_403_){
_start:
{
size_t v_sz_boxed_404_; size_t v_i_boxed_405_; lean_object* v_res_406_; 
v_sz_boxed_404_ = lean_unbox_usize(v_sz_401_);
lean_dec(v_sz_401_);
v_i_boxed_405_ = lean_unbox_usize(v_i_402_);
lean_dec(v_i_402_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3_spec__4(v_sz_boxed_404_, v_i_boxed_405_, v_bs_403_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3(lean_object* v_oldTraces_407_, lean_object* v_data_408_, lean_object* v_ref_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_fileName_416_; lean_object* v_fileMap_417_; lean_object* v_options_418_; lean_object* v_currRecDepth_419_; lean_object* v_maxRecDepth_420_; lean_object* v_ref_421_; lean_object* v_currNamespace_422_; lean_object* v_openDecls_423_; lean_object* v_initHeartbeats_424_; lean_object* v_maxHeartbeats_425_; lean_object* v_quotContext_426_; lean_object* v_currMacroScope_427_; uint8_t v_diag_428_; lean_object* v_cancelTk_x3f_429_; uint8_t v_suppressElabErrors_430_; lean_object* v_inheritedTraceOptions_431_; lean_object* v___x_432_; lean_object* v_traceState_433_; lean_object* v_traces_434_; lean_object* v_ref_435_; lean_object* v___x_436_; lean_object* v___x_437_; size_t v_sz_438_; size_t v___x_439_; lean_object* v___x_440_; lean_object* v_msg_441_; lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_480_; 
v_fileName_416_ = lean_ctor_get(v___y_413_, 0);
v_fileMap_417_ = lean_ctor_get(v___y_413_, 1);
v_options_418_ = lean_ctor_get(v___y_413_, 2);
v_currRecDepth_419_ = lean_ctor_get(v___y_413_, 3);
v_maxRecDepth_420_ = lean_ctor_get(v___y_413_, 4);
v_ref_421_ = lean_ctor_get(v___y_413_, 5);
v_currNamespace_422_ = lean_ctor_get(v___y_413_, 6);
v_openDecls_423_ = lean_ctor_get(v___y_413_, 7);
v_initHeartbeats_424_ = lean_ctor_get(v___y_413_, 8);
v_maxHeartbeats_425_ = lean_ctor_get(v___y_413_, 9);
v_quotContext_426_ = lean_ctor_get(v___y_413_, 10);
v_currMacroScope_427_ = lean_ctor_get(v___y_413_, 11);
v_diag_428_ = lean_ctor_get_uint8(v___y_413_, sizeof(void*)*14);
v_cancelTk_x3f_429_ = lean_ctor_get(v___y_413_, 12);
v_suppressElabErrors_430_ = lean_ctor_get_uint8(v___y_413_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_431_ = lean_ctor_get(v___y_413_, 13);
v___x_432_ = lean_st_ref_get(v___y_414_);
v_traceState_433_ = lean_ctor_get(v___x_432_, 4);
lean_inc_ref(v_traceState_433_);
lean_dec(v___x_432_);
v_traces_434_ = lean_ctor_get(v_traceState_433_, 0);
lean_inc_ref(v_traces_434_);
lean_dec_ref(v_traceState_433_);
v_ref_435_ = l_Lean_replaceRef(v_ref_409_, v_ref_421_);
lean_inc_ref(v_inheritedTraceOptions_431_);
lean_inc(v_cancelTk_x3f_429_);
lean_inc(v_currMacroScope_427_);
lean_inc(v_quotContext_426_);
lean_inc(v_maxHeartbeats_425_);
lean_inc(v_initHeartbeats_424_);
lean_inc(v_openDecls_423_);
lean_inc(v_currNamespace_422_);
lean_inc(v_maxRecDepth_420_);
lean_inc(v_currRecDepth_419_);
lean_inc_ref(v_options_418_);
lean_inc_ref(v_fileMap_417_);
lean_inc_ref(v_fileName_416_);
v___x_436_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_436_, 0, v_fileName_416_);
lean_ctor_set(v___x_436_, 1, v_fileMap_417_);
lean_ctor_set(v___x_436_, 2, v_options_418_);
lean_ctor_set(v___x_436_, 3, v_currRecDepth_419_);
lean_ctor_set(v___x_436_, 4, v_maxRecDepth_420_);
lean_ctor_set(v___x_436_, 5, v_ref_435_);
lean_ctor_set(v___x_436_, 6, v_currNamespace_422_);
lean_ctor_set(v___x_436_, 7, v_openDecls_423_);
lean_ctor_set(v___x_436_, 8, v_initHeartbeats_424_);
lean_ctor_set(v___x_436_, 9, v_maxHeartbeats_425_);
lean_ctor_set(v___x_436_, 10, v_quotContext_426_);
lean_ctor_set(v___x_436_, 11, v_currMacroScope_427_);
lean_ctor_set(v___x_436_, 12, v_cancelTk_x3f_429_);
lean_ctor_set(v___x_436_, 13, v_inheritedTraceOptions_431_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*14, v_diag_428_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*14 + 1, v_suppressElabErrors_430_);
v___x_437_ = l_Lean_PersistentArray_toArray___redArg(v_traces_434_);
lean_dec_ref(v_traces_434_);
v_sz_438_ = lean_array_size(v___x_437_);
v___x_439_ = ((size_t)0ULL);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3_spec__4(v_sz_438_, v___x_439_, v___x_437_);
v_msg_441_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_441_, 0, v_data_408_);
lean_ctor_set(v_msg_441_, 1, v_msg_410_);
lean_ctor_set(v_msg_441_, 2, v___x_440_);
v___x_442_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v_msg_441_, v___y_411_, v___y_412_, v___x_436_, v___y_414_);
lean_dec_ref(v___x_436_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_480_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_480_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_480_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v_traceState_448_; lean_object* v_env_449_; lean_object* v_nextMacroScope_450_; lean_object* v_ngen_451_; lean_object* v_auxDeclNGen_452_; lean_object* v_cache_453_; lean_object* v_messages_454_; lean_object* v_infoState_455_; lean_object* v_snapshotTasks_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_479_; 
v___x_447_ = lean_st_ref_take(v___y_414_);
v_traceState_448_ = lean_ctor_get(v___x_447_, 4);
v_env_449_ = lean_ctor_get(v___x_447_, 0);
v_nextMacroScope_450_ = lean_ctor_get(v___x_447_, 1);
v_ngen_451_ = lean_ctor_get(v___x_447_, 2);
v_auxDeclNGen_452_ = lean_ctor_get(v___x_447_, 3);
v_cache_453_ = lean_ctor_get(v___x_447_, 5);
v_messages_454_ = lean_ctor_get(v___x_447_, 6);
v_infoState_455_ = lean_ctor_get(v___x_447_, 7);
v_snapshotTasks_456_ = lean_ctor_get(v___x_447_, 8);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_479_ == 0)
{
v___x_458_ = v___x_447_;
v_isShared_459_ = v_isSharedCheck_479_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_snapshotTasks_456_);
lean_inc(v_infoState_455_);
lean_inc(v_messages_454_);
lean_inc(v_cache_453_);
lean_inc(v_traceState_448_);
lean_inc(v_auxDeclNGen_452_);
lean_inc(v_ngen_451_);
lean_inc(v_nextMacroScope_450_);
lean_inc(v_env_449_);
lean_dec(v___x_447_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_479_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
uint64_t v_tid_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_477_; 
v_tid_460_ = lean_ctor_get_uint64(v_traceState_448_, sizeof(void*)*1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_traceState_448_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_traceState_448_, 0);
lean_dec(v_unused_478_);
v___x_462_ = v_traceState_448_;
v_isShared_463_ = v_isSharedCheck_477_;
goto v_resetjp_461_;
}
else
{
lean_dec(v_traceState_448_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_477_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_ref_409_);
lean_ctor_set(v___x_464_, 1, v_a_443_);
v___x_465_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_407_, v___x_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_465_);
lean_ctor_set_uint64(v_reuseFailAlloc_476_, sizeof(void*)*1, v_tid_460_);
v___x_467_ = v_reuseFailAlloc_476_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v___x_467_);
v___x_469_ = v___x_458_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_env_449_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_nextMacroScope_450_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_ngen_451_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_auxDeclNGen_452_);
lean_ctor_set(v_reuseFailAlloc_475_, 4, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_475_, 5, v_cache_453_);
lean_ctor_set(v_reuseFailAlloc_475_, 6, v_messages_454_);
lean_ctor_set(v_reuseFailAlloc_475_, 7, v_infoState_455_);
lean_ctor_set(v_reuseFailAlloc_475_, 8, v_snapshotTasks_456_);
v___x_469_ = v_reuseFailAlloc_475_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_st_ref_set(v___y_414_, v___x_469_);
v___x_471_ = lean_box(0);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_471_);
v___x_473_ = v___x_445_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3___boxed(lean_object* v_oldTraces_481_, lean_object* v_data_482_, lean_object* v_ref_483_, lean_object* v_msg_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3(v_oldTraces_481_, v_data_482_, v_ref_483_, v_msg_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2(lean_object* v_e_491_){
_start:
{
if (lean_obj_tag(v_e_491_) == 0)
{
uint8_t v___x_492_; 
v___x_492_ = 2;
return v___x_492_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = 0;
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2___boxed(lean_object* v_e_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2(v_e_494_);
lean_dec_ref(v_e_494_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_a_499_ = lean_ctor_get(v_x_497_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_x_497_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v_x_497_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v_x_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 1);
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_a_507_ = lean_ctor_get(v_x_497_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_497_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v_x_497_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v_x_497_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 0);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg___boxed(lean_object* v_x_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(v_x_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(lean_object* v_opts_518_, lean_object* v_opt_519_){
_start:
{
lean_object* v_name_520_; lean_object* v_defValue_521_; lean_object* v_map_522_; lean_object* v___x_523_; 
v_name_520_ = lean_ctor_get(v_opt_519_, 0);
v_defValue_521_ = lean_ctor_get(v_opt_519_, 1);
v_map_522_ = lean_ctor_get(v_opts_518_, 0);
v___x_523_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_522_, v_name_520_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_inc(v_defValue_521_);
return v_defValue_521_;
}
else
{
lean_object* v_val_524_; 
v_val_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_val_524_);
lean_dec_ref(v___x_523_);
if (lean_obj_tag(v_val_524_) == 3)
{
lean_object* v_v_525_; 
v_v_525_ = lean_ctor_get(v_val_524_, 0);
lean_inc(v_v_525_);
lean_dec_ref(v_val_524_);
return v_v_525_;
}
else
{
lean_dec(v_val_524_);
lean_inc(v_defValue_521_);
return v_defValue_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5___boxed(lean_object* v_opts_526_, lean_object* v_opt_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(v_opts_526_, v_opt_527_);
lean_dec_ref(v_opt_527_);
lean_dec_ref(v_opts_526_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__0));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2(void){
_start:
{
lean_object* v___x_532_; double v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_float_of_nat(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__3));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5(void){
_start:
{
lean_object* v___x_537_; double v___x_538_; 
v___x_537_ = lean_unsigned_to_nat(1000u);
v___x_538_ = lean_float_of_nat(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(lean_object* v_cls_539_, uint8_t v_collapsed_540_, lean_object* v_tag_541_, lean_object* v_opts_542_, uint8_t v_clsEnabled_543_, lean_object* v_oldTraces_544_, lean_object* v_msg_545_, lean_object* v_resStartStop_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_fst_552_; lean_object* v_snd_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_651_; 
v_fst_552_ = lean_ctor_get(v_resStartStop_546_, 0);
v_snd_553_ = lean_ctor_get(v_resStartStop_546_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_resStartStop_546_);
if (v_isSharedCheck_651_ == 0)
{
v___x_555_ = v_resStartStop_546_;
v_isShared_556_ = v_isSharedCheck_651_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_snd_553_);
lean_inc(v_fst_552_);
lean_dec(v_resStartStop_546_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_651_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v_data_560_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_650_; 
v_fst_571_ = lean_ctor_get(v_snd_553_, 0);
v_snd_572_ = lean_ctor_get(v_snd_553_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_snd_553_);
if (v_isSharedCheck_650_ == 0)
{
v___x_574_ = v_snd_553_;
v_isShared_575_ = v_isSharedCheck_650_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_snd_572_);
lean_inc(v_fst_571_);
lean_dec(v_snd_553_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_650_;
goto v_resetjp_573_;
}
v___jp_557_:
{
lean_object* v___x_561_; 
lean_inc(v___y_558_);
v___x_561_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3(v_oldTraces_544_, v_data_560_, v___y_558_, v___y_559_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; 
lean_dec_ref(v___x_561_);
v___x_562_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(v_fst_552_);
return v___x_562_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_fst_552_);
v_a_563_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_561_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
v_resetjp_573_:
{
lean_object* v___x_576_; uint8_t v___x_577_; lean_object* v___y_579_; lean_object* v_a_580_; uint8_t v___y_604_; double v___y_635_; 
v___x_576_ = l_Lean_trace_profiler;
v___x_577_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_542_, v___x_576_);
if (v___x_577_ == 0)
{
v___y_604_ = v___x_577_;
goto v___jp_603_;
}
else
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = l_Lean_trace_profiler_useHeartbeats;
v___x_641_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_542_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; double v___x_644_; double v___x_645_; double v___x_646_; 
v___x_642_ = l_Lean_trace_profiler_threshold;
v___x_643_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(v_opts_542_, v___x_642_);
v___x_644_ = lean_float_of_nat(v___x_643_);
v___x_645_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5);
v___x_646_ = lean_float_div(v___x_644_, v___x_645_);
v___y_635_ = v___x_646_;
goto v___jp_634_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; double v___x_649_; 
v___x_647_ = l_Lean_trace_profiler_threshold;
v___x_648_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(v_opts_542_, v___x_647_);
v___x_649_ = lean_float_of_nat(v___x_648_);
v___y_635_ = v___x_649_;
goto v___jp_634_;
}
}
v___jp_578_:
{
uint8_t v_result_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_result_581_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2(v_fst_552_);
v___x_582_ = l_Lean_TraceResult_toEmoji(v_result_581_);
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
v___x_584_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 7);
lean_ctor_set(v___x_574_, 1, v___x_584_);
lean_ctor_set(v___x_574_, 0, v___x_583_);
v___x_586_ = v___x_574_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_597_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v_m_588_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set_tag(v___x_555_, 7);
lean_ctor_set(v___x_555_, 1, v_a_580_);
lean_ctor_set(v___x_555_, 0, v___x_586_);
v_m_588_ = v___x_555_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_a_580_);
v_m_588_ = v_reuseFailAlloc_596_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; double v___x_591_; lean_object* v_data_592_; 
v___x_589_ = lean_box(v_result_581_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
v___x_591_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2);
lean_inc_ref(v_tag_541_);
lean_inc_ref(v___x_590_);
lean_inc(v_cls_539_);
v_data_592_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_592_, 0, v_cls_539_);
lean_ctor_set(v_data_592_, 1, v___x_590_);
lean_ctor_set(v_data_592_, 2, v_tag_541_);
lean_ctor_set_float(v_data_592_, sizeof(void*)*3, v___x_591_);
lean_ctor_set_float(v_data_592_, sizeof(void*)*3 + 8, v___x_591_);
lean_ctor_set_uint8(v_data_592_, sizeof(void*)*3 + 16, v_collapsed_540_);
if (v___x_577_ == 0)
{
lean_dec_ref(v___x_590_);
lean_dec(v_snd_572_);
lean_dec(v_fst_571_);
lean_dec_ref(v_tag_541_);
lean_dec(v_cls_539_);
v___y_558_ = v___y_579_;
v___y_559_ = v_m_588_;
v_data_560_ = v_data_592_;
goto v___jp_557_;
}
else
{
lean_object* v_data_593_; double v___x_594_; double v___x_595_; 
lean_dec_ref(v_data_592_);
v_data_593_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_593_, 0, v_cls_539_);
lean_ctor_set(v_data_593_, 1, v___x_590_);
lean_ctor_set(v_data_593_, 2, v_tag_541_);
v___x_594_ = lean_unbox_float(v_fst_571_);
lean_dec(v_fst_571_);
lean_ctor_set_float(v_data_593_, sizeof(void*)*3, v___x_594_);
v___x_595_ = lean_unbox_float(v_snd_572_);
lean_dec(v_snd_572_);
lean_ctor_set_float(v_data_593_, sizeof(void*)*3 + 8, v___x_595_);
lean_ctor_set_uint8(v_data_593_, sizeof(void*)*3 + 16, v_collapsed_540_);
v___y_558_ = v___y_579_;
v___y_559_ = v_m_588_;
v_data_560_ = v_data_593_;
goto v___jp_557_;
}
}
}
}
v___jp_598_:
{
lean_object* v_ref_599_; lean_object* v___x_600_; 
v_ref_599_ = lean_ctor_get(v___y_549_, 5);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc(v_fst_552_);
v___x_600_ = lean_apply_6(v_msg_545_, v_fst_552_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, lean_box(0));
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref(v___x_600_);
v___y_579_ = v_ref_599_;
v_a_580_ = v_a_601_;
goto v___jp_578_;
}
else
{
lean_object* v___x_602_; 
lean_dec_ref(v___x_600_);
v___x_602_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4);
v___y_579_ = v_ref_599_;
v_a_580_ = v___x_602_;
goto v___jp_578_;
}
}
v___jp_603_:
{
if (v_clsEnabled_543_ == 0)
{
if (v___y_604_ == 0)
{
lean_object* v___x_605_; lean_object* v_traceState_606_; lean_object* v_env_607_; lean_object* v_nextMacroScope_608_; lean_object* v_ngen_609_; lean_object* v_auxDeclNGen_610_; lean_object* v_cache_611_; lean_object* v_messages_612_; lean_object* v_infoState_613_; lean_object* v_snapshotTasks_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_633_; 
lean_del_object(v___x_574_);
lean_dec(v_snd_572_);
lean_dec(v_fst_571_);
lean_del_object(v___x_555_);
lean_dec_ref(v_msg_545_);
lean_dec_ref(v_tag_541_);
lean_dec(v_cls_539_);
v___x_605_ = lean_st_ref_take(v___y_550_);
v_traceState_606_ = lean_ctor_get(v___x_605_, 4);
v_env_607_ = lean_ctor_get(v___x_605_, 0);
v_nextMacroScope_608_ = lean_ctor_get(v___x_605_, 1);
v_ngen_609_ = lean_ctor_get(v___x_605_, 2);
v_auxDeclNGen_610_ = lean_ctor_get(v___x_605_, 3);
v_cache_611_ = lean_ctor_get(v___x_605_, 5);
v_messages_612_ = lean_ctor_get(v___x_605_, 6);
v_infoState_613_ = lean_ctor_get(v___x_605_, 7);
v_snapshotTasks_614_ = lean_ctor_get(v___x_605_, 8);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_633_ == 0)
{
v___x_616_ = v___x_605_;
v_isShared_617_ = v_isSharedCheck_633_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snapshotTasks_614_);
lean_inc(v_infoState_613_);
lean_inc(v_messages_612_);
lean_inc(v_cache_611_);
lean_inc(v_traceState_606_);
lean_inc(v_auxDeclNGen_610_);
lean_inc(v_ngen_609_);
lean_inc(v_nextMacroScope_608_);
lean_inc(v_env_607_);
lean_dec(v___x_605_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_633_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint64_t v_tid_618_; lean_object* v_traces_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_632_; 
v_tid_618_ = lean_ctor_get_uint64(v_traceState_606_, sizeof(void*)*1);
v_traces_619_ = lean_ctor_get(v_traceState_606_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_traceState_606_);
if (v_isSharedCheck_632_ == 0)
{
v___x_621_ = v_traceState_606_;
v_isShared_622_ = v_isSharedCheck_632_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_traces_619_);
lean_dec(v_traceState_606_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_632_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_544_, v_traces_619_);
lean_dec_ref(v_traces_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_623_);
lean_ctor_set_uint64(v_reuseFailAlloc_631_, sizeof(void*)*1, v_tid_618_);
v___x_625_ = v_reuseFailAlloc_631_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_625_);
v___x_627_ = v___x_616_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_env_607_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_nextMacroScope_608_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_ngen_609_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v_auxDeclNGen_610_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_630_, 5, v_cache_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 6, v_messages_612_);
lean_ctor_set(v_reuseFailAlloc_630_, 7, v_infoState_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 8, v_snapshotTasks_614_);
v___x_627_ = v_reuseFailAlloc_630_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_st_ref_set(v___y_550_, v___x_627_);
v___x_629_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(v_fst_552_);
return v___x_629_;
}
}
}
}
}
else
{
goto v___jp_598_;
}
}
else
{
goto v___jp_598_;
}
}
v___jp_634_:
{
double v___x_636_; double v___x_637_; double v___x_638_; uint8_t v___x_639_; 
v___x_636_ = lean_unbox_float(v_snd_572_);
v___x_637_ = lean_unbox_float(v_fst_571_);
v___x_638_ = lean_float_sub(v___x_636_, v___x_637_);
v___x_639_ = lean_float_decLt(v___y_635_, v___x_638_);
v___y_604_ = v___x_639_;
goto v___jp_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___boxed(lean_object* v_cls_652_, lean_object* v_collapsed_653_, lean_object* v_tag_654_, lean_object* v_opts_655_, lean_object* v_clsEnabled_656_, lean_object* v_oldTraces_657_, lean_object* v_msg_658_, lean_object* v_resStartStop_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
uint8_t v_collapsed_boxed_665_; uint8_t v_clsEnabled_boxed_666_; lean_object* v_res_667_; 
v_collapsed_boxed_665_ = lean_unbox(v_collapsed_653_);
v_clsEnabled_boxed_666_ = lean_unbox(v_clsEnabled_656_);
v_res_667_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(v_cls_652_, v_collapsed_boxed_665_, v_tag_654_, v_opts_655_, v_clsEnabled_boxed_666_, v_oldTraces_657_, v_msg_658_, v_resStartStop_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v_opts_655_);
return v_res_667_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5(void){
_start:
{
lean_object* v___x_676_; double v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(1000000000u);
v___x_677_ = lean_float_of_nat(v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(lean_object* v_ctx_678_, lean_object* v___f_679_, lean_object* v_x_680_, lean_object* v_reflectionResult_681_, lean_object* v_x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_options_688_; uint8_t v_hasTrace_689_; 
v_options_688_ = lean_ctor_get(v___y_685_, 2);
v_hasTrace_689_ = lean_ctor_get_uint8(v_options_688_, sizeof(void*)*1);
if (v_hasTrace_689_ == 0)
{
lean_object* v___x_690_; 
lean_dec_ref(v___f_679_);
v___x_690_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_678_, v_reflectionResult_681_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_701_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_701_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_695_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v_a_691_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_697_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_a_702_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_690_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_690_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_823_; 
v___x_710_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4));
v___x_711_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v___x_710_, v___y_685_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_823_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_823_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_823_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v_a_720_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v_a_736_; uint8_t v___x_799_; 
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
v___x_799_ = lean_unbox(v_a_712_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = l_Lean_trace_profiler;
v___x_801_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_688_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v_a_712_);
lean_dec_ref(v___f_679_);
v___x_802_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_678_, v_reflectionResult_681_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_814_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_814_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_814_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_814_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_a_803_);
lean_ctor_set(v___x_807_, 1, v___x_716_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 1);
lean_ctor_set(v___x_714_, 0, v___x_807_);
v___x_809_ = v___x_714_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_809_);
v___x_811_ = v___x_805_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_del_object(v___x_714_);
v_a_815_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_802_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_802_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_del_object(v___x_714_);
goto v___jp_746_;
}
}
else
{
lean_del_object(v___x_714_);
goto v___jp_746_;
}
v___jp_717_:
{
lean_object* v___x_721_; double v___x_722_; double v___x_723_; double v___x_724_; double v___x_725_; double v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; 
v___x_721_ = lean_io_mono_nanos_now();
v___x_722_ = lean_float_of_nat(v___y_718_);
v___x_723_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5);
v___x_724_ = lean_float_div(v___x_722_, v___x_723_);
v___x_725_ = lean_float_of_nat(v___x_721_);
v___x_726_ = lean_float_div(v___x_725_, v___x_723_);
v___x_727_ = lean_box_float(v___x_724_);
v___x_728_ = lean_box_float(v___x_726_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_a_720_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_unbox(v_a_712_);
lean_dec(v_a_712_);
v___x_732_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(v___x_710_, v_hasTrace_689_, v___x_716_, v_options_688_, v___x_731_, v___y_719_, v___f_679_, v___x_730_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_732_;
}
v___jp_733_:
{
lean_object* v___x_737_; double v___x_738_; double v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; 
v___x_737_ = lean_io_get_num_heartbeats();
v___x_738_ = lean_float_of_nat(v___y_734_);
v___x_739_ = lean_float_of_nat(v___x_737_);
v___x_740_ = lean_box_float(v___x_738_);
v___x_741_ = lean_box_float(v___x_739_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_a_736_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_unbox(v_a_712_);
lean_dec(v_a_712_);
v___x_745_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(v___x_710_, v_hasTrace_689_, v___x_716_, v_options_688_, v___x_744_, v___y_735_, v___f_679_, v___x_743_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_745_;
}
v___jp_746_:
{
lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_798_; 
v___x_747_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg(v___y_686_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_798_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_798_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_798_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = l_Lean_trace_profiler_useHeartbeats;
v___x_753_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_688_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_io_mono_nanos_now();
v___x_755_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_678_, v_reflectionResult_681_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_767_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_767_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_767_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_767_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_a_756_);
lean_ctor_set(v___x_760_, 1, v___x_716_);
if (v_isShared_759_ == 0)
{
lean_ctor_set_tag(v___x_758_, 1);
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
lean_ctor_set(v___x_750_, 0, v___x_762_);
v___x_764_ = v___x_750_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
v___y_718_ = v___x_754_;
v___y_719_ = v_a_748_;
v_a_720_ = v___x_764_;
goto v___jp_717_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_del_object(v___x_750_);
v_a_768_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_755_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_755_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 0);
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
v___y_718_ = v___x_754_;
v___y_719_ = v_a_748_;
v_a_720_ = v___x_773_;
goto v___jp_717_;
}
}
}
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_io_get_num_heartbeats();
v___x_777_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_678_, v_reflectionResult_681_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_789_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_789_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_a_778_);
lean_ctor_set(v___x_782_, 1, v___x_716_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 1);
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
lean_ctor_set(v___x_750_, 0, v___x_784_);
v___x_786_ = v___x_750_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v___y_734_ = v___x_776_;
v___y_735_ = v_a_748_;
v_a_736_ = v___x_786_;
goto v___jp_733_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_del_object(v___x_750_);
v_a_790_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_777_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_777_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 0);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v___y_734_ = v___x_776_;
v___y_735_ = v_a_748_;
v_a_736_ = v___x_795_;
goto v___jp_733_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed(lean_object* v_ctx_824_, lean_object* v___f_825_, lean_object* v_x_826_, lean_object* v_reflectionResult_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(v_ctx_824_, v___f_825_, v_x_826_, v_reflectionResult_827_, v_x_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec_ref(v_x_828_);
lean_dec(v_x_826_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object* v_g_836_, lean_object* v_ctx_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___f_843_; lean_object* v_unsatProver_844_; lean_object* v___x_845_; 
v___f_843_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0));
v_unsatProver_844_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed), 10, 2);
lean_closure_set(v_unsatProver_844_, 0, v_ctx_837_);
lean_closure_set(v_unsatProver_844_, 1, v___f_843_);
v___x_845_ = l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(v_g_836_, v_unsatProver_844_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_854_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_box(0);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_845_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_845_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___boxed(lean_object* v_g_863_, lean_object* v_ctx_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(v_g_863_, v_ctx_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4(lean_object* v_00_u03b1_871_, lean_object* v_x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(v_x_872_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___boxed(lean_object* v_00_u03b1_879_, lean_object* v_x_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4(v_00_u03b1_879_, v_x_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_box(0);
v___x_888_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0);
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(lean_object* v_00_u03b1_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___boxed(lean_object* v_00_u03b1_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(v_00_u03b1_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_916_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_923_, uint8_t v_suppressElabErrors_924_, lean_object* v_x_925_){
_start:
{
if (lean_obj_tag(v_x_925_) == 1)
{
lean_object* v_pre_926_; 
v_pre_926_ = lean_ctor_get(v_x_925_, 0);
switch(lean_obj_tag(v_pre_926_))
{
case 1:
{
lean_object* v_pre_927_; 
v_pre_927_ = lean_ctor_get(v_pre_926_, 0);
switch(lean_obj_tag(v_pre_927_))
{
case 0:
{
lean_object* v_str_928_; lean_object* v_str_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_str_928_ = lean_ctor_get(v_x_925_, 1);
v_str_929_ = lean_ctor_get(v_pre_926_, 1);
v___x_930_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_931_ = lean_string_dec_eq(v_str_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2));
v___x_933_ = lean_string_dec_eq(v_str_929_, v___x_932_);
if (v___x_933_ == 0)
{
return v___y_923_;
}
else
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_935_ = lean_string_dec_eq(v_str_928_, v___x_934_);
if (v___x_935_ == 0)
{
return v___y_923_;
}
else
{
return v_suppressElabErrors_924_;
}
}
}
else
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_937_ = lean_string_dec_eq(v_str_928_, v___x_936_);
if (v___x_937_ == 0)
{
return v___y_923_;
}
else
{
return v_suppressElabErrors_924_;
}
}
}
case 1:
{
lean_object* v_pre_938_; 
v_pre_938_ = lean_ctor_get(v_pre_927_, 0);
if (lean_obj_tag(v_pre_938_) == 0)
{
lean_object* v_str_939_; lean_object* v_str_940_; lean_object* v_str_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_str_939_ = lean_ctor_get(v_x_925_, 1);
v_str_940_ = lean_ctor_get(v_pre_926_, 1);
v_str_941_ = lean_ctor_get(v_pre_927_, 1);
v___x_942_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_943_ = lean_string_dec_eq(v_str_941_, v___x_942_);
if (v___x_943_ == 0)
{
return v___y_923_;
}
else
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_945_ = lean_string_dec_eq(v_str_940_, v___x_944_);
if (v___x_945_ == 0)
{
return v___y_923_;
}
else
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_947_ = lean_string_dec_eq(v_str_939_, v___x_946_);
if (v___x_947_ == 0)
{
return v___y_923_;
}
else
{
return v_suppressElabErrors_924_;
}
}
}
}
else
{
return v___y_923_;
}
}
default: 
{
return v___y_923_;
}
}
}
case 0:
{
lean_object* v_str_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_str_948_ = lean_ctor_get(v_x_925_, 1);
v___x_949_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0));
v___x_950_ = lean_string_dec_eq(v_str_948_, v___x_949_);
if (v___x_950_ == 0)
{
return v___y_923_;
}
else
{
return v_suppressElabErrors_924_;
}
}
default: 
{
return v___y_923_;
}
}
}
else
{
return v___y_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_951_, lean_object* v_suppressElabErrors_952_, lean_object* v_x_953_){
_start:
{
uint8_t v___y_6476__boxed_954_; uint8_t v_suppressElabErrors_boxed_955_; uint8_t v_res_956_; lean_object* v_r_957_; 
v___y_6476__boxed_954_ = lean_unbox(v___y_951_);
v_suppressElabErrors_boxed_955_ = lean_unbox(v_suppressElabErrors_952_);
v_res_956_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(v___y_6476__boxed_954_, v_suppressElabErrors_boxed_955_, v_x_953_);
lean_dec(v_x_953_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object* v_ref_958_, lean_object* v_msgData_959_, uint8_t v_severity_960_, uint8_t v_isSilent_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; uint8_t v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; uint8_t v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1007_; uint8_t v___y_1008_; uint8_t v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1029_; lean_object* v___y_1030_; uint8_t v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; uint8_t v___y_1034_; uint8_t v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; uint8_t v___y_1045_; uint8_t v___y_1046_; uint8_t v___x_1051_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; uint8_t v___y_1058_; uint8_t v___y_1059_; uint8_t v___y_1061_; uint8_t v___x_1076_; 
v___x_1051_ = 2;
v___x_1076_ = l_Lean_instBEqMessageSeverity_beq(v_severity_960_, v___x_1051_);
if (v___x_1076_ == 0)
{
v___y_1061_ = v___x_1076_;
goto v___jp_1060_;
}
else
{
uint8_t v___x_1077_; 
lean_inc_ref(v_msgData_959_);
v___x_1077_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_959_);
v___y_1061_ = v___x_1077_;
goto v___jp_1060_;
}
v___jp_967_:
{
lean_object* v___x_977_; lean_object* v_currNamespace_978_; lean_object* v_openDecls_979_; lean_object* v_env_980_; lean_object* v_nextMacroScope_981_; lean_object* v_ngen_982_; lean_object* v_auxDeclNGen_983_; lean_object* v_traceState_984_; lean_object* v_cache_985_; lean_object* v_messages_986_; lean_object* v_infoState_987_; lean_object* v_snapshotTasks_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1002_; 
v___x_977_ = lean_st_ref_take(v___y_976_);
v_currNamespace_978_ = lean_ctor_get(v___y_975_, 6);
v_openDecls_979_ = lean_ctor_get(v___y_975_, 7);
v_env_980_ = lean_ctor_get(v___x_977_, 0);
v_nextMacroScope_981_ = lean_ctor_get(v___x_977_, 1);
v_ngen_982_ = lean_ctor_get(v___x_977_, 2);
v_auxDeclNGen_983_ = lean_ctor_get(v___x_977_, 3);
v_traceState_984_ = lean_ctor_get(v___x_977_, 4);
v_cache_985_ = lean_ctor_get(v___x_977_, 5);
v_messages_986_ = lean_ctor_get(v___x_977_, 6);
v_infoState_987_ = lean_ctor_get(v___x_977_, 7);
v_snapshotTasks_988_ = lean_ctor_get(v___x_977_, 8);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_990_ = v___x_977_;
v_isShared_991_ = v_isSharedCheck_1002_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_snapshotTasks_988_);
lean_inc(v_infoState_987_);
lean_inc(v_messages_986_);
lean_inc(v_cache_985_);
lean_inc(v_traceState_984_);
lean_inc(v_auxDeclNGen_983_);
lean_inc(v_ngen_982_);
lean_inc(v_nextMacroScope_981_);
lean_inc(v_env_980_);
lean_dec(v___x_977_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1002_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
lean_inc(v_openDecls_979_);
lean_inc(v_currNamespace_978_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_currNamespace_978_);
lean_ctor_set(v___x_992_, 1, v_openDecls_979_);
v___x_993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___y_972_);
lean_inc_ref(v___y_970_);
v___x_994_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_994_, 0, v___y_970_);
lean_ctor_set(v___x_994_, 1, v___y_973_);
lean_ctor_set(v___x_994_, 2, v___y_969_);
lean_ctor_set(v___x_994_, 3, v___y_968_);
lean_ctor_set(v___x_994_, 4, v___x_993_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5, v___y_974_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5 + 1, v___y_971_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5 + 2, v_isSilent_961_);
v___x_995_ = l_Lean_MessageLog_add(v___x_994_, v_messages_986_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 6, v___x_995_);
v___x_997_ = v___x_990_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_env_980_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_nextMacroScope_981_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_ngen_982_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_auxDeclNGen_983_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_traceState_984_);
lean_ctor_set(v_reuseFailAlloc_1001_, 5, v_cache_985_);
lean_ctor_set(v_reuseFailAlloc_1001_, 6, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 7, v_infoState_987_);
lean_ctor_set(v_reuseFailAlloc_1001_, 8, v_snapshotTasks_988_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_st_ref_set(v___y_976_, v___x_997_);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
v___jp_1003_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1027_; 
v___x_1012_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_959_);
v___x_1013_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v___x_1012_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_inc_ref(v___y_1007_);
v___x_1018_ = l_Lean_FileMap_toPosition(v___y_1007_, v___y_1010_);
lean_dec(v___y_1010_);
lean_inc_ref(v___y_1007_);
v___x_1019_ = l_Lean_FileMap_toPosition(v___y_1007_, v___y_1011_);
lean_dec(v___y_1011_);
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
if (v___y_1008_ == 0)
{
lean_del_object(v___x_1016_);
lean_dec_ref(v___y_1004_);
v___y_968_ = v___x_1021_;
v___y_969_ = v___x_1020_;
v___y_970_ = v___y_1005_;
v___y_971_ = v___y_1006_;
v___y_972_ = v_a_1014_;
v___y_973_ = v___x_1018_;
v___y_974_ = v___y_1009_;
v___y_975_ = v___y_964_;
v___y_976_ = v___y_965_;
goto v___jp_967_;
}
else
{
uint8_t v___x_1022_; 
lean_inc(v_a_1014_);
v___x_1022_ = l_Lean_MessageData_hasTag(v___y_1004_, v_a_1014_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec_ref(v___x_1020_);
lean_dec_ref(v___x_1018_);
lean_dec(v_a_1014_);
v___x_1023_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1023_);
v___x_1025_ = v___x_1016_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
else
{
lean_del_object(v___x_1016_);
v___y_968_ = v___x_1021_;
v___y_969_ = v___x_1020_;
v___y_970_ = v___y_1005_;
v___y_971_ = v___y_1006_;
v___y_972_ = v_a_1014_;
v___y_973_ = v___x_1018_;
v___y_974_ = v___y_1009_;
v___y_975_ = v___y_964_;
v___y_976_ = v___y_965_;
goto v___jp_967_;
}
}
}
}
v___jp_1028_:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Syntax_getTailPos_x3f(v___y_1032_, v___y_1035_);
lean_dec(v___y_1032_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_inc(v___y_1036_);
v___y_1004_ = v___y_1029_;
v___y_1005_ = v___y_1030_;
v___y_1006_ = v___y_1031_;
v___y_1007_ = v___y_1033_;
v___y_1008_ = v___y_1034_;
v___y_1009_ = v___y_1035_;
v___y_1010_ = v___y_1036_;
v___y_1011_ = v___y_1036_;
goto v___jp_1003_;
}
else
{
lean_object* v_val_1038_; 
v_val_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref(v___x_1037_);
v___y_1004_ = v___y_1029_;
v___y_1005_ = v___y_1030_;
v___y_1006_ = v___y_1031_;
v___y_1007_ = v___y_1033_;
v___y_1008_ = v___y_1034_;
v___y_1009_ = v___y_1035_;
v___y_1010_ = v___y_1036_;
v___y_1011_ = v_val_1038_;
goto v___jp_1003_;
}
}
v___jp_1039_:
{
lean_object* v_ref_1047_; lean_object* v___x_1048_; 
v_ref_1047_ = l_Lean_replaceRef(v_ref_958_, v___y_1043_);
v___x_1048_ = l_Lean_Syntax_getPos_x3f(v_ref_1047_, v___y_1045_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v___y_1029_ = v___y_1040_;
v___y_1030_ = v___y_1041_;
v___y_1031_ = v___y_1046_;
v___y_1032_ = v_ref_1047_;
v___y_1033_ = v___y_1042_;
v___y_1034_ = v___y_1044_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v___x_1049_;
goto v___jp_1028_;
}
else
{
lean_object* v_val_1050_; 
v_val_1050_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_val_1050_);
lean_dec_ref(v___x_1048_);
v___y_1029_ = v___y_1040_;
v___y_1030_ = v___y_1041_;
v___y_1031_ = v___y_1046_;
v___y_1032_ = v_ref_1047_;
v___y_1033_ = v___y_1042_;
v___y_1034_ = v___y_1044_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v_val_1050_;
goto v___jp_1028_;
}
}
v___jp_1052_:
{
if (v___y_1059_ == 0)
{
v___y_1040_ = v___y_1056_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v___y_1054_;
v___y_1043_ = v___y_1055_;
v___y_1044_ = v___y_1057_;
v___y_1045_ = v___y_1058_;
v___y_1046_ = v_severity_960_;
goto v___jp_1039_;
}
else
{
v___y_1040_ = v___y_1056_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v___y_1054_;
v___y_1043_ = v___y_1055_;
v___y_1044_ = v___y_1057_;
v___y_1045_ = v___y_1058_;
v___y_1046_ = v___x_1051_;
goto v___jp_1039_;
}
}
v___jp_1060_:
{
if (v___y_1061_ == 0)
{
lean_object* v_fileName_1062_; lean_object* v_fileMap_1063_; lean_object* v_options_1064_; lean_object* v_ref_1065_; uint8_t v_suppressElabErrors_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; uint8_t v___x_1070_; uint8_t v___x_1071_; 
v_fileName_1062_ = lean_ctor_get(v___y_964_, 0);
v_fileMap_1063_ = lean_ctor_get(v___y_964_, 1);
v_options_1064_ = lean_ctor_get(v___y_964_, 2);
v_ref_1065_ = lean_ctor_get(v___y_964_, 5);
v_suppressElabErrors_1066_ = lean_ctor_get_uint8(v___y_964_, sizeof(void*)*14 + 1);
v___x_1067_ = lean_box(v___y_1061_);
v___x_1068_ = lean_box(v_suppressElabErrors_1066_);
v___f_1069_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1069_, 0, v___x_1067_);
lean_closure_set(v___f_1069_, 1, v___x_1068_);
v___x_1070_ = 1;
v___x_1071_ = l_Lean_instBEqMessageSeverity_beq(v_severity_960_, v___x_1070_);
if (v___x_1071_ == 0)
{
v___y_1053_ = v_fileName_1062_;
v___y_1054_ = v_fileMap_1063_;
v___y_1055_ = v_ref_1065_;
v___y_1056_ = v___f_1069_;
v___y_1057_ = v_suppressElabErrors_1066_;
v___y_1058_ = v___y_1061_;
v___y_1059_ = v___x_1071_;
goto v___jp_1052_;
}
else
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = l_Lean_warningAsError;
v___x_1073_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1064_, v___x_1072_);
v___y_1053_ = v_fileName_1062_;
v___y_1054_ = v_fileMap_1063_;
v___y_1055_ = v_ref_1065_;
v___y_1056_ = v___f_1069_;
v___y_1057_ = v_suppressElabErrors_1066_;
v___y_1058_ = v___y_1061_;
v___y_1059_ = v___x_1073_;
goto v___jp_1052_;
}
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec_ref(v_msgData_959_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_1078_, lean_object* v_msgData_1079_, lean_object* v_severity_1080_, lean_object* v_isSilent_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
uint8_t v_severity_boxed_1087_; uint8_t v_isSilent_boxed_1088_; lean_object* v_res_1089_; 
v_severity_boxed_1087_ = lean_unbox(v_severity_1080_);
v_isSilent_boxed_1088_ = lean_unbox(v_isSilent_1081_);
v_res_1089_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1078_, v_msgData_1079_, v_severity_boxed_1087_, v_isSilent_boxed_1088_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_ref_1078_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(lean_object* v_msgData_1090_, uint8_t v_severity_1091_, uint8_t v_isSilent_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_ref_1098_; lean_object* v___x_1099_; 
v_ref_1098_ = lean_ctor_get(v___y_1095_, 5);
v___x_1099_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1098_, v_msgData_1090_, v_severity_1091_, v_isSilent_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object* v_msgData_1100_, lean_object* v_severity_1101_, lean_object* v_isSilent_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v_severity_boxed_1108_; uint8_t v_isSilent_boxed_1109_; lean_object* v_res_1110_; 
v_severity_boxed_1108_ = lean_unbox(v_severity_1101_);
v_isSilent_boxed_1109_ = lean_unbox(v_isSilent_1102_);
v_res_1110_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1100_, v_severity_boxed_1108_, v_isSilent_boxed_1109_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(lean_object* v_msgData_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
uint8_t v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = 1;
v___x_1118_ = 0;
v___x_1119_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1111_, v___x_1117_, v___x_1118_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1___boxed(lean_object* v_msgData_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(v_msgData_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1126_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__0));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(lean_object* v_a_1136_, lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v___x_1139_, lean_object* v___x_1140_, lean_object* v_tk_1141_, lean_object* v_a_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___y_1153_; lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1144_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(v_a_1166_, v_a_1136_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref(v___x_1167_);
if (lean_obj_tag(v_a_1168_) == 0)
{
lean_object* v_ref_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec_ref(v_a_1142_);
v_ref_1169_ = lean_ctor_get(v___y_1149_, 5);
v___x_1170_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1);
v___x_1171_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(v___x_1170_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1192_; 
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v___x_1171_, 0);
lean_dec(v_unused_1193_);
v___x_1173_ = v___x_1171_;
v_isShared_1174_ = v_isSharedCheck_1192_;
goto v_resetjp_1172_;
}
else
{
lean_dec(v___x_1171_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1192_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1175_ = 0;
v___x_1176_ = l_Lean_SourceInfo_fromRef(v_ref_1169_, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__2));
lean_inc(v___x_1176_);
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__4));
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__5));
v___x_1181_ = l_Lean_Name_mkStr4(v___x_1137_, v___x_1138_, v___x_1139_, v___x_1180_);
v___x_1182_ = l_Lean_Syntax_node2(v___x_1176_, v___x_1181_, v___x_1178_, v___x_1140_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1179_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
lean_ctor_set(v___x_1185_, 2, v___x_1184_);
lean_ctor_set(v___x_1185_, 3, v___x_1184_);
lean_ctor_set(v___x_1185_, 4, v___x_1184_);
lean_ctor_set(v___x_1185_, 5, v___x_1184_);
lean_inc(v_ref_1169_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 1);
lean_ctor_set(v___x_1173_, 0, v_ref_1169_);
v___x_1187_ = v___x_1173_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_ref_1169_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__6));
v___x_1189_ = 4;
v___x_1190_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1141_, v___x_1185_, v___x_1187_, v___x_1188_, v___x_1184_, v___x_1189_, v___y_1149_, v___y_1150_);
v___y_1153_ = v___x_1190_;
goto v___jp_1152_;
}
}
}
else
{
lean_dec(v_tk_1141_);
lean_dec(v___x_1140_);
lean_dec_ref(v___x_1139_);
lean_dec_ref(v___x_1138_);
lean_dec_ref(v___x_1137_);
v___y_1153_ = v___x_1171_;
goto v___jp_1152_;
}
}
else
{
lean_object* v_val_1194_; lean_object* v___x_1195_; 
lean_dec(v_tk_1141_);
lean_dec(v___x_1140_);
lean_dec_ref(v___x_1139_);
lean_dec_ref(v___x_1138_);
lean_dec_ref(v___x_1137_);
v_val_1194_ = lean_ctor_get(v_a_1168_, 0);
lean_inc(v_val_1194_);
lean_dec_ref(v_a_1168_);
v___x_1195_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(v_val_1194_, v_a_1142_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
v___y_1153_ = v___x_1195_;
goto v___jp_1152_;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_a_1142_);
lean_dec(v_tk_1141_);
lean_dec(v___x_1140_);
lean_dec_ref(v___x_1139_);
lean_dec_ref(v___x_1138_);
lean_dec_ref(v___x_1137_);
v_a_1196_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1167_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1167_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_a_1142_);
lean_dec(v_tk_1141_);
lean_dec(v___x_1140_);
lean_dec_ref(v___x_1139_);
lean_dec_ref(v___x_1138_);
lean_dec_ref(v___x_1137_);
v_a_1204_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1165_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1165_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
v___jp_1152_:
{
if (lean_obj_tag(v___y_1153_) == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v___y_1153_);
v___x_1154_ = lean_box(0);
v___x_1155_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1154_, v___y_1144_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v___x_1155_, 0);
lean_dec(v_unused_1164_);
v___x_1157_ = v___x_1155_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_dec(v___x_1155_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_box(0);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
return v___x_1155_;
}
}
else
{
return v___y_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed(lean_object* v_a_1212_, lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v_tk_1217_, lean_object* v_a_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(v_a_1212_, v___x_1213_, v___x_1214_, v___x_1215_, v___x_1216_, v_tk_1217_, v_a_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_a_1212_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(lean_object* v_x_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0));
v___x_1257_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1));
v___x_1258_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2));
v___x_1259_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3));
lean_inc(v_x_1246_);
v___x_1260_ = l_Lean_Syntax_isOfKind(v_x_1246_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
lean_dec(v_x_1246_);
v___x_1261_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = l_Lean_Syntax_getArg(v_x_1246_, v___x_1262_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5));
lean_inc(v___x_1263_);
v___x_1265_ = l_Lean_Syntax_isOfKind(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_dec(v___x_1263_);
lean_dec(v_x_1246_);
v___x_1266_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; lean_object* v_path_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1267_ = lean_unsigned_to_nat(2u);
v_path_1268_ = l_Lean_Syntax_getArg(v_x_1246_, v___x_1267_);
v___x_1269_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__7));
lean_inc(v_path_1268_);
v___x_1270_ = l_Lean_Syntax_isOfKind(v_path_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_dec(v_path_1268_);
lean_dec(v___x_1263_);
lean_dec(v_x_1246_);
v___x_1271_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; 
lean_inc(v___x_1263_);
v___x_1272_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v___x_1263_, v_a_1247_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = l_Lean_TSyntax_getString(v_path_1268_);
lean_dec(v_path_1268_);
lean_inc(v_a_1273_);
v___x_1275_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(v___x_1274_, v_a_1273_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; lean_object* v_tk_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = lean_unsigned_to_nat(0u);
v_tk_1278_ = l_Lean_Syntax_getArg(v_x_1246_, v___x_1277_);
lean_dec(v_x_1246_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1279_, 0, v_a_1273_);
lean_closure_set(v___f_1279_, 1, v___x_1256_);
lean_closure_set(v___f_1279_, 2, v___x_1257_);
lean_closure_set(v___f_1279_, 3, v___x_1258_);
lean_closure_set(v___f_1279_, 4, v___x_1263_);
lean_closure_set(v___f_1279_, 5, v_tk_1278_);
lean_closure_set(v___f_1279_, 6, v_a_1276_);
v___x_1280_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1279_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_a_1273_);
lean_dec(v___x_1263_);
lean_dec(v_x_1246_);
v_a_1281_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1275_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1275_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_path_1268_);
lean_dec(v___x_1263_);
lean_dec(v_x_1246_);
v_a_1289_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1272_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1272_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed(lean_object* v_x_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(v_x_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1321_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3));
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4));
v___x_1324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed), 10, 0);
v___x_1325_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1321_, v___x_1322_, v___x_1323_, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___boxed(lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1();
return v_res_1327_;
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
res = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1();
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
