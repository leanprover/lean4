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
lean_dec_ref(v_a_145_);
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
lean_inc_ref(v_a_219_);
v___x_226_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v___x_228_ = l_System_FilePath_join(v_a_227_, v_lratPath_217_);
v___x_229_ = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(v___x_228_, v_cfg_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec_ref(v_a_219_);
return v___x_229_;
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v_a_223_);
lean_dec_ref(v_a_219_);
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
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
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
lean_inc(v_a_253_);
lean_inc_ref(v_a_252_);
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
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
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
lean_object* v_fileName_416_; lean_object* v_fileMap_417_; lean_object* v_options_418_; lean_object* v_currRecDepth_419_; lean_object* v_maxRecDepth_420_; lean_object* v_ref_421_; lean_object* v_currNamespace_422_; lean_object* v_openDecls_423_; lean_object* v_initHeartbeats_424_; lean_object* v_maxHeartbeats_425_; lean_object* v_quotContext_426_; lean_object* v_currMacroScope_427_; uint8_t v_diag_428_; lean_object* v_cancelTk_x3f_429_; uint8_t v_suppressElabErrors_430_; lean_object* v_inheritedTraceOptions_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_486_; 
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
v_isSharedCheck_486_ = !lean_is_exclusive(v___y_413_);
if (v_isSharedCheck_486_ == 0)
{
v___x_433_ = v___y_413_;
v_isShared_434_ = v_isSharedCheck_486_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_inheritedTraceOptions_431_);
lean_inc(v_cancelTk_x3f_429_);
lean_inc(v_currMacroScope_427_);
lean_inc(v_quotContext_426_);
lean_inc(v_maxHeartbeats_425_);
lean_inc(v_initHeartbeats_424_);
lean_inc(v_openDecls_423_);
lean_inc(v_currNamespace_422_);
lean_inc(v_ref_421_);
lean_inc(v_maxRecDepth_420_);
lean_inc(v_currRecDepth_419_);
lean_inc(v_options_418_);
lean_inc(v_fileMap_417_);
lean_inc(v_fileName_416_);
lean_dec(v___y_413_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_486_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v_traceState_436_; lean_object* v_traces_437_; lean_object* v_ref_438_; lean_object* v___x_440_; 
v___x_435_ = lean_st_ref_get(v___y_414_);
v_traceState_436_ = lean_ctor_get(v___x_435_, 4);
lean_inc_ref(v_traceState_436_);
lean_dec(v___x_435_);
v_traces_437_ = lean_ctor_get(v_traceState_436_, 0);
lean_inc_ref(v_traces_437_);
lean_dec_ref(v_traceState_436_);
v_ref_438_ = l_Lean_replaceRef(v_ref_409_, v_ref_421_);
lean_dec(v_ref_421_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 5, v_ref_438_);
v___x_440_ = v___x_433_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_fileName_416_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_fileMap_417_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_options_418_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_currRecDepth_419_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_maxRecDepth_420_);
lean_ctor_set(v_reuseFailAlloc_485_, 5, v_ref_438_);
lean_ctor_set(v_reuseFailAlloc_485_, 6, v_currNamespace_422_);
lean_ctor_set(v_reuseFailAlloc_485_, 7, v_openDecls_423_);
lean_ctor_set(v_reuseFailAlloc_485_, 8, v_initHeartbeats_424_);
lean_ctor_set(v_reuseFailAlloc_485_, 9, v_maxHeartbeats_425_);
lean_ctor_set(v_reuseFailAlloc_485_, 10, v_quotContext_426_);
lean_ctor_set(v_reuseFailAlloc_485_, 11, v_currMacroScope_427_);
lean_ctor_set(v_reuseFailAlloc_485_, 12, v_cancelTk_x3f_429_);
lean_ctor_set(v_reuseFailAlloc_485_, 13, v_inheritedTraceOptions_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*14, v_diag_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_485_, sizeof(void*)*14 + 1, v_suppressElabErrors_430_);
v___x_440_ = v_reuseFailAlloc_485_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; size_t v_sz_442_; size_t v___x_443_; lean_object* v___x_444_; lean_object* v_msg_445_; lean_object* v___x_446_; lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_484_; 
v___x_441_ = l_Lean_PersistentArray_toArray___redArg(v_traces_437_);
lean_dec_ref(v_traces_437_);
v_sz_442_ = lean_array_size(v___x_441_);
v___x_443_ = ((size_t)0ULL);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3_spec__4(v_sz_442_, v___x_443_, v___x_441_);
v_msg_445_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_445_, 0, v_data_408_);
lean_ctor_set(v_msg_445_, 1, v_msg_410_);
lean_ctor_set(v_msg_445_, 2, v___x_444_);
v___x_446_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v_msg_445_, v___y_411_, v___y_412_, v___x_440_, v___y_414_);
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
v___x_451_ = lean_st_ref_take(v___y_414_);
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
lean_ctor_set(v___x_468_, 0, v_ref_409_);
lean_ctor_set(v___x_468_, 1, v_a_447_);
v___x_469_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_407_, v___x_468_);
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
v___x_474_ = lean_st_ref_set(v___y_414_, v___x_473_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3___boxed(lean_object* v_oldTraces_487_, lean_object* v_data_488_, lean_object* v_ref_489_, lean_object* v_msg_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3(v_oldTraces_487_, v_data_488_, v_ref_489_, v_msg_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_496_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2(lean_object* v_e_497_){
_start:
{
if (lean_obj_tag(v_e_497_) == 0)
{
uint8_t v___x_498_; 
v___x_498_ = 2;
return v___x_498_;
}
else
{
uint8_t v___x_499_; 
v___x_499_ = 0;
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2___boxed(lean_object* v_e_500_){
_start:
{
uint8_t v_res_501_; lean_object* v_r_502_; 
v_res_501_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2(v_e_500_);
lean_dec_ref(v_e_500_);
v_r_502_ = lean_box(v_res_501_);
return v_r_502_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v_x_503_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_503_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v_x_503_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v_x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 1);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v_x_503_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_503_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v_x_503_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v_x_503_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 0);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg___boxed(lean_object* v_x_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(v_x_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(lean_object* v_opts_524_, lean_object* v_opt_525_){
_start:
{
lean_object* v_name_526_; lean_object* v_defValue_527_; lean_object* v_map_528_; lean_object* v___x_529_; 
v_name_526_ = lean_ctor_get(v_opt_525_, 0);
v_defValue_527_ = lean_ctor_get(v_opt_525_, 1);
v_map_528_ = lean_ctor_get(v_opts_524_, 0);
v___x_529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_528_, v_name_526_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_inc(v_defValue_527_);
return v_defValue_527_;
}
else
{
lean_object* v_val_530_; 
v_val_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_val_530_);
lean_dec_ref(v___x_529_);
if (lean_obj_tag(v_val_530_) == 3)
{
lean_object* v_v_531_; 
v_v_531_ = lean_ctor_get(v_val_530_, 0);
lean_inc(v_v_531_);
lean_dec_ref(v_val_530_);
return v_v_531_;
}
else
{
lean_dec(v_val_530_);
lean_inc(v_defValue_527_);
return v_defValue_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5___boxed(lean_object* v_opts_532_, lean_object* v_opt_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(v_opts_532_, v_opt_533_);
lean_dec_ref(v_opt_533_);
lean_dec_ref(v_opts_532_);
return v_res_534_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__0));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2(void){
_start:
{
lean_object* v___x_538_; double v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_float_of_nat(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__3));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5(void){
_start:
{
lean_object* v___x_543_; double v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(1000u);
v___x_544_ = lean_float_of_nat(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(lean_object* v_cls_545_, uint8_t v_collapsed_546_, lean_object* v_tag_547_, lean_object* v_opts_548_, uint8_t v_clsEnabled_549_, lean_object* v_oldTraces_550_, lean_object* v_msg_551_, lean_object* v_resStartStop_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_657_; 
v_fst_558_ = lean_ctor_get(v_resStartStop_552_, 0);
v_snd_559_ = lean_ctor_get(v_resStartStop_552_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v_resStartStop_552_);
if (v_isSharedCheck_657_ == 0)
{
v___x_561_ = v_resStartStop_552_;
v_isShared_562_ = v_isSharedCheck_657_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_snd_559_);
lean_inc(v_fst_558_);
lean_dec(v_resStartStop_552_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_657_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v_data_566_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_656_; 
v_fst_577_ = lean_ctor_get(v_snd_559_, 0);
v_snd_578_ = lean_ctor_get(v_snd_559_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_snd_559_);
if (v_isSharedCheck_656_ == 0)
{
v___x_580_ = v_snd_559_;
v_isShared_581_ = v_isSharedCheck_656_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snd_578_);
lean_inc(v_fst_577_);
lean_dec(v_snd_559_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_656_;
goto v_resetjp_579_;
}
v___jp_563_:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__3(v_oldTraces_550_, v_data_566_, v___y_564_, v___y_565_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v___x_568_; 
lean_dec_ref(v___x_567_);
v___x_568_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(v_fst_558_);
return v___x_568_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_fst_558_);
v_a_569_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
v_resetjp_579_:
{
lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___y_585_; lean_object* v_a_586_; uint8_t v___y_610_; double v___y_641_; 
v___x_582_ = l_Lean_trace_profiler;
v___x_583_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_548_, v___x_582_);
if (v___x_583_ == 0)
{
v___y_610_ = v___x_583_;
goto v___jp_609_;
}
else
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = l_Lean_trace_profiler_useHeartbeats;
v___x_647_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_548_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; double v___x_650_; double v___x_651_; double v___x_652_; 
v___x_648_ = l_Lean_trace_profiler_threshold;
v___x_649_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(v_opts_548_, v___x_648_);
v___x_650_ = lean_float_of_nat(v___x_649_);
v___x_651_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__5);
v___x_652_ = lean_float_div(v___x_650_, v___x_651_);
v___y_641_ = v___x_652_;
goto v___jp_640_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; double v___x_655_; 
v___x_653_ = l_Lean_trace_profiler_threshold;
v___x_654_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__5(v_opts_548_, v___x_653_);
v___x_655_ = lean_float_of_nat(v___x_654_);
v___y_641_ = v___x_655_;
goto v___jp_640_;
}
}
v___jp_584_:
{
uint8_t v_result_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v_result_587_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__2(v_fst_558_);
v___x_588_ = l_Lean_TraceResult_toEmoji(v_result_587_);
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
v___x_590_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__1);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 7);
lean_ctor_set(v___x_580_, 1, v___x_590_);
lean_ctor_set(v___x_580_, 0, v___x_589_);
v___x_592_ = v___x_580_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_603_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v_m_594_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 7);
lean_ctor_set(v___x_561_, 1, v_a_586_);
lean_ctor_set(v___x_561_, 0, v___x_592_);
v_m_594_ = v___x_561_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_a_586_);
v_m_594_ = v_reuseFailAlloc_602_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; double v___x_597_; lean_object* v_data_598_; 
v___x_595_ = lean_box(v_result_587_);
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
v___x_597_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__2);
lean_inc_ref(v_tag_547_);
lean_inc_ref(v___x_596_);
lean_inc(v_cls_545_);
v_data_598_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_598_, 0, v_cls_545_);
lean_ctor_set(v_data_598_, 1, v___x_596_);
lean_ctor_set(v_data_598_, 2, v_tag_547_);
lean_ctor_set_float(v_data_598_, sizeof(void*)*3, v___x_597_);
lean_ctor_set_float(v_data_598_, sizeof(void*)*3 + 8, v___x_597_);
lean_ctor_set_uint8(v_data_598_, sizeof(void*)*3 + 16, v_collapsed_546_);
if (v___x_583_ == 0)
{
lean_dec_ref(v___x_596_);
lean_dec(v_snd_578_);
lean_dec(v_fst_577_);
lean_dec_ref(v_tag_547_);
lean_dec(v_cls_545_);
v___y_564_ = v___y_585_;
v___y_565_ = v_m_594_;
v_data_566_ = v_data_598_;
goto v___jp_563_;
}
else
{
lean_object* v_data_599_; double v___x_600_; double v___x_601_; 
lean_dec_ref(v_data_598_);
v_data_599_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_599_, 0, v_cls_545_);
lean_ctor_set(v_data_599_, 1, v___x_596_);
lean_ctor_set(v_data_599_, 2, v_tag_547_);
v___x_600_ = lean_unbox_float(v_fst_577_);
lean_dec(v_fst_577_);
lean_ctor_set_float(v_data_599_, sizeof(void*)*3, v___x_600_);
v___x_601_ = lean_unbox_float(v_snd_578_);
lean_dec(v_snd_578_);
lean_ctor_set_float(v_data_599_, sizeof(void*)*3 + 8, v___x_601_);
lean_ctor_set_uint8(v_data_599_, sizeof(void*)*3 + 16, v_collapsed_546_);
v___y_564_ = v___y_585_;
v___y_565_ = v_m_594_;
v_data_566_ = v_data_599_;
goto v___jp_563_;
}
}
}
}
v___jp_604_:
{
lean_object* v_ref_605_; lean_object* v___x_606_; 
v_ref_605_ = lean_ctor_get(v___y_555_, 5);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v_fst_558_);
v___x_606_ = lean_apply_6(v_msg_551_, v_fst_558_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, lean_box(0));
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
lean_inc(v_ref_605_);
v___y_585_ = v_ref_605_;
v_a_586_ = v_a_607_;
goto v___jp_584_;
}
else
{
lean_object* v___x_608_; 
lean_dec_ref(v___x_606_);
v___x_608_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___closed__4);
lean_inc(v_ref_605_);
v___y_585_ = v_ref_605_;
v_a_586_ = v___x_608_;
goto v___jp_584_;
}
}
v___jp_609_:
{
if (v_clsEnabled_549_ == 0)
{
if (v___y_610_ == 0)
{
lean_object* v___x_611_; lean_object* v_traceState_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_cache_617_; lean_object* v_messages_618_; lean_object* v_infoState_619_; lean_object* v_snapshotTasks_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_639_; 
lean_del_object(v___x_580_);
lean_dec(v_snd_578_);
lean_dec(v_fst_577_);
lean_del_object(v___x_561_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec_ref(v_msg_551_);
lean_dec_ref(v_tag_547_);
lean_dec(v_cls_545_);
v___x_611_ = lean_st_ref_take(v___y_556_);
v_traceState_612_ = lean_ctor_get(v___x_611_, 4);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_611_, 1);
v_ngen_615_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_611_, 3);
v_cache_617_ = lean_ctor_get(v___x_611_, 5);
v_messages_618_ = lean_ctor_get(v___x_611_, 6);
v_infoState_619_ = lean_ctor_get(v___x_611_, 7);
v_snapshotTasks_620_ = lean_ctor_get(v___x_611_, 8);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_639_ == 0)
{
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_639_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snapshotTasks_620_);
lean_inc(v_infoState_619_);
lean_inc(v_messages_618_);
lean_inc(v_cache_617_);
lean_inc(v_traceState_612_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_639_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint64_t v_tid_624_; lean_object* v_traces_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_638_; 
v_tid_624_ = lean_ctor_get_uint64(v_traceState_612_, sizeof(void*)*1);
v_traces_625_ = lean_ctor_get(v_traceState_612_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v_traceState_612_);
if (v_isSharedCheck_638_ == 0)
{
v___x_627_ = v_traceState_612_;
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_traces_625_);
lean_dec(v_traceState_612_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_550_, v_traces_625_);
lean_dec_ref(v_traces_625_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_629_);
lean_ctor_set_uint64(v_reuseFailAlloc_637_, sizeof(void*)*1, v_tid_624_);
v___x_631_ = v_reuseFailAlloc_637_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v___x_631_);
v___x_633_ = v___x_622_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_env_613_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_636_, 5, v_cache_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 6, v_messages_618_);
lean_ctor_set(v_reuseFailAlloc_636_, 7, v_infoState_619_);
lean_ctor_set(v_reuseFailAlloc_636_, 8, v_snapshotTasks_620_);
v___x_633_ = v_reuseFailAlloc_636_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_st_ref_set(v___y_556_, v___x_633_);
lean_dec(v___y_556_);
v___x_635_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(v_fst_558_);
return v___x_635_;
}
}
}
}
}
else
{
goto v___jp_604_;
}
}
else
{
goto v___jp_604_;
}
}
v___jp_640_:
{
double v___x_642_; double v___x_643_; double v___x_644_; uint8_t v___x_645_; 
v___x_642_ = lean_unbox_float(v_snd_578_);
v___x_643_ = lean_unbox_float(v_fst_577_);
v___x_644_ = lean_float_sub(v___x_642_, v___x_643_);
v___x_645_ = lean_float_decLt(v___y_641_, v___x_644_);
v___y_610_ = v___x_645_;
goto v___jp_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2___boxed(lean_object* v_cls_658_, lean_object* v_collapsed_659_, lean_object* v_tag_660_, lean_object* v_opts_661_, lean_object* v_clsEnabled_662_, lean_object* v_oldTraces_663_, lean_object* v_msg_664_, lean_object* v_resStartStop_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v_collapsed_boxed_671_; uint8_t v_clsEnabled_boxed_672_; lean_object* v_res_673_; 
v_collapsed_boxed_671_ = lean_unbox(v_collapsed_659_);
v_clsEnabled_boxed_672_ = lean_unbox(v_clsEnabled_662_);
v_res_673_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(v_cls_658_, v_collapsed_boxed_671_, v_tag_660_, v_opts_661_, v_clsEnabled_boxed_672_, v_oldTraces_663_, v_msg_664_, v_resStartStop_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec_ref(v_opts_661_);
return v_res_673_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5(void){
_start:
{
lean_object* v___x_682_; double v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(1000000000u);
v___x_683_ = lean_float_of_nat(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(lean_object* v_ctx_684_, lean_object* v___f_685_, lean_object* v_x_686_, lean_object* v_reflectionResult_687_, lean_object* v_x_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_options_694_; uint8_t v_hasTrace_695_; 
v_options_694_ = lean_ctor_get(v___y_691_, 2);
v_hasTrace_695_ = lean_ctor_get_uint8(v_options_694_, sizeof(void*)*1);
if (v_hasTrace_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec_ref(v___f_685_);
v___x_696_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_684_, v_reflectionResult_687_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_707_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_707_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_701_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_a_697_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_703_);
v___x_705_ = v___x_699_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v_a_708_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_696_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_696_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_829_; 
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__4));
v___x_717_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg(v___x_716_, v___y_691_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_829_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_829_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_829_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v_a_726_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v_a_742_; uint8_t v___x_805_; 
v___x_722_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
v___x_805_ = lean_unbox(v_a_718_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = l_Lean_trace_profiler;
v___x_807_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_694_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec(v_a_718_);
lean_dec_ref(v___f_685_);
v___x_808_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_684_, v_reflectionResult_687_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_820_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_820_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_820_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_820_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v_a_809_);
lean_ctor_set(v___x_813_, 1, v___x_722_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 1);
lean_ctor_set(v___x_720_, 0, v___x_813_);
v___x_815_ = v___x_720_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_del_object(v___x_720_);
v_a_821_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_808_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_808_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_inc_ref(v_options_694_);
lean_del_object(v___x_720_);
goto v___jp_752_;
}
}
else
{
lean_inc_ref(v_options_694_);
lean_del_object(v___x_720_);
goto v___jp_752_;
}
v___jp_723_:
{
lean_object* v___x_727_; double v___x_728_; double v___x_729_; double v___x_730_; double v___x_731_; double v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; 
v___x_727_ = lean_io_mono_nanos_now();
v___x_728_ = lean_float_of_nat(v___y_725_);
v___x_729_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__5);
v___x_730_ = lean_float_div(v___x_728_, v___x_729_);
v___x_731_ = lean_float_of_nat(v___x_727_);
v___x_732_ = lean_float_div(v___x_731_, v___x_729_);
v___x_733_ = lean_box_float(v___x_730_);
v___x_734_ = lean_box_float(v___x_732_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_a_726_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_unbox(v_a_718_);
lean_dec(v_a_718_);
v___x_738_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(v___x_716_, v_hasTrace_695_, v___x_722_, v_options_694_, v___x_737_, v___y_724_, v___f_685_, v___x_736_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec_ref(v_options_694_);
return v___x_738_;
}
v___jp_739_:
{
lean_object* v___x_743_; double v___x_744_; double v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; lean_object* v___x_751_; 
v___x_743_ = lean_io_get_num_heartbeats();
v___x_744_ = lean_float_of_nat(v___y_741_);
v___x_745_ = lean_float_of_nat(v___x_743_);
v___x_746_ = lean_box_float(v___x_744_);
v___x_747_ = lean_box_float(v___x_745_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v_a_742_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_unbox(v_a_718_);
lean_dec(v_a_718_);
v___x_751_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2(v___x_716_, v_hasTrace_695_, v___x_722_, v_options_694_, v___x_750_, v___y_740_, v___f_685_, v___x_749_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec_ref(v_options_694_);
return v___x_751_;
}
v___jp_752_:
{
lean_object* v___x_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_804_; 
v___x_753_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__1___redArg(v___y_692_);
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_804_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_804_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_804_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = l_Lean_trace_profiler_useHeartbeats;
v___x_759_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_694_, v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_io_mono_nanos_now();
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
v___x_761_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_684_, v_reflectionResult_687_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_773_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_773_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_a_762_);
lean_ctor_set(v___x_766_, 1, v___x_722_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 1);
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 1);
lean_ctor_set(v___x_756_, 0, v___x_768_);
v___x_770_ = v___x_756_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v___y_724_ = v_a_754_;
v___y_725_ = v___x_760_;
v_a_726_ = v___x_770_;
goto v___jp_723_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_del_object(v___x_756_);
v_a_774_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_761_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_761_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 0);
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
v___y_724_ = v_a_754_;
v___y_725_ = v___x_760_;
v_a_726_ = v___x_779_;
goto v___jp_723_;
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_io_get_num_heartbeats();
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
v___x_783_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(v_ctx_684_, v_reflectionResult_687_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_795_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_795_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_784_);
lean_ctor_set(v___x_788_, 1, v___x_722_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 1);
lean_ctor_set(v___x_786_, 0, v___x_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 1);
lean_ctor_set(v___x_756_, 0, v___x_790_);
v___x_792_ = v___x_756_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v___y_740_ = v_a_754_;
v___y_741_ = v___x_782_;
v_a_742_ = v___x_792_;
goto v___jp_739_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_del_object(v___x_756_);
v_a_796_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_783_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_783_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 0);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
v___y_740_ = v_a_754_;
v___y_741_ = v___x_782_;
v_a_742_ = v___x_801_;
goto v___jp_739_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed(lean_object* v_ctx_830_, lean_object* v___f_831_, lean_object* v_x_832_, lean_object* v_reflectionResult_833_, lean_object* v_x_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1(v_ctx_830_, v___f_831_, v_x_832_, v_reflectionResult_833_, v_x_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec_ref(v_x_834_);
lean_dec(v_x_832_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object* v_g_842_, lean_object* v_ctx_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___f_849_; lean_object* v_unsatProver_850_; lean_object* v___x_851_; 
v___f_849_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___closed__0));
v_unsatProver_850_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___boxed), 10, 2);
lean_closure_set(v_unsatProver_850_, 0, v_ctx_843_);
lean_closure_set(v_unsatProver_850_, 1, v___f_849_);
v___x_851_ = l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(v_g_842_, v_unsatProver_850_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v___x_851_, 0);
lean_dec(v_unused_860_);
v___x_853_ = v___x_851_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_dec(v___x_851_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_box(0);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_851_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_851_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___boxed(lean_object* v_g_869_, lean_object* v_ctx_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(v_g_869_, v_ctx_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4(lean_object* v_00_u03b1_877_, lean_object* v_x_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___redArg(v_x_878_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4___boxed(lean_object* v_00_u03b1_885_, lean_object* v_x_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__2_spec__4(v_00_u03b1_885_, v_x_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
return v_res_892_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(0);
v___x_894_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg(){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___closed__0);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg___boxed(lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(lean_object* v_00_u03b1_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___boxed(lean_object* v_00_u03b1_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0(v_00_u03b1_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_922_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_929_, uint8_t v_suppressElabErrors_930_, lean_object* v_x_931_){
_start:
{
if (lean_obj_tag(v_x_931_) == 1)
{
lean_object* v_pre_932_; 
v_pre_932_ = lean_ctor_get(v_x_931_, 0);
switch(lean_obj_tag(v_pre_932_))
{
case 1:
{
lean_object* v_pre_933_; 
v_pre_933_ = lean_ctor_get(v_pre_932_, 0);
switch(lean_obj_tag(v_pre_933_))
{
case 0:
{
lean_object* v_str_934_; lean_object* v_str_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_str_934_ = lean_ctor_get(v_x_931_, 1);
v_str_935_ = lean_ctor_get(v_pre_932_, 1);
v___x_936_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_937_ = lean_string_dec_eq(v_str_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2));
v___x_939_ = lean_string_dec_eq(v_str_935_, v___x_938_);
if (v___x_939_ == 0)
{
return v___y_929_;
}
else
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_941_ = lean_string_dec_eq(v_str_934_, v___x_940_);
if (v___x_941_ == 0)
{
return v___y_929_;
}
else
{
return v_suppressElabErrors_930_;
}
}
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_943_ = lean_string_dec_eq(v_str_934_, v___x_942_);
if (v___x_943_ == 0)
{
return v___y_929_;
}
else
{
return v_suppressElabErrors_930_;
}
}
}
case 1:
{
lean_object* v_pre_944_; 
v_pre_944_ = lean_ctor_get(v_pre_933_, 0);
if (lean_obj_tag(v_pre_944_) == 0)
{
lean_object* v_str_945_; lean_object* v_str_946_; lean_object* v_str_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_str_945_ = lean_ctor_get(v_x_931_, 1);
v_str_946_ = lean_ctor_get(v_pre_932_, 1);
v_str_947_ = lean_ctor_get(v_pre_933_, 1);
v___x_948_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_949_ = lean_string_dec_eq(v_str_947_, v___x_948_);
if (v___x_949_ == 0)
{
return v___y_929_;
}
else
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_951_ = lean_string_dec_eq(v_str_946_, v___x_950_);
if (v___x_951_ == 0)
{
return v___y_929_;
}
else
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_953_ = lean_string_dec_eq(v_str_945_, v___x_952_);
if (v___x_953_ == 0)
{
return v___y_929_;
}
else
{
return v_suppressElabErrors_930_;
}
}
}
}
else
{
return v___y_929_;
}
}
default: 
{
return v___y_929_;
}
}
}
case 0:
{
lean_object* v_str_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_str_954_ = lean_ctor_get(v_x_931_, 1);
v___x_955_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck_spec__0___redArg___closed__0));
v___x_956_ = lean_string_dec_eq(v_str_954_, v___x_955_);
if (v___x_956_ == 0)
{
return v___y_929_;
}
else
{
return v_suppressElabErrors_930_;
}
}
default: 
{
return v___y_929_;
}
}
}
else
{
return v___y_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_957_, lean_object* v_suppressElabErrors_958_, lean_object* v_x_959_){
_start:
{
uint8_t v___y_6513__boxed_960_; uint8_t v_suppressElabErrors_boxed_961_; uint8_t v_res_962_; lean_object* v_r_963_; 
v___y_6513__boxed_960_ = lean_unbox(v___y_957_);
v_suppressElabErrors_boxed_961_ = lean_unbox(v_suppressElabErrors_958_);
v_res_962_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(v___y_6513__boxed_960_, v_suppressElabErrors_boxed_961_, v_x_959_);
lean_dec(v_x_959_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(lean_object* v_ref_964_, lean_object* v_msgData_965_, uint8_t v_severity_966_, uint8_t v_isSilent_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v___y_976_; uint8_t v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; uint8_t v___y_1013_; uint8_t v___y_1014_; uint8_t v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; uint8_t v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; uint8_t v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; uint8_t v___y_1050_; uint8_t v___y_1051_; uint8_t v___y_1052_; uint8_t v___x_1057_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; uint8_t v___y_1064_; uint8_t v___y_1065_; uint8_t v___y_1067_; uint8_t v___x_1082_; 
v___x_1057_ = 2;
v___x_1082_ = l_Lean_instBEqMessageSeverity_beq(v_severity_966_, v___x_1057_);
if (v___x_1082_ == 0)
{
v___y_1067_ = v___x_1082_;
goto v___jp_1066_;
}
else
{
uint8_t v___x_1083_; 
lean_inc_ref(v_msgData_965_);
v___x_1083_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_965_);
v___y_1067_ = v___x_1083_;
goto v___jp_1066_;
}
v___jp_973_:
{
lean_object* v___x_983_; lean_object* v_currNamespace_984_; lean_object* v_openDecls_985_; lean_object* v_env_986_; lean_object* v_nextMacroScope_987_; lean_object* v_ngen_988_; lean_object* v_auxDeclNGen_989_; lean_object* v_traceState_990_; lean_object* v_cache_991_; lean_object* v_messages_992_; lean_object* v_infoState_993_; lean_object* v_snapshotTasks_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1008_; 
v___x_983_ = lean_st_ref_take(v___y_982_);
v_currNamespace_984_ = lean_ctor_get(v___y_981_, 6);
lean_inc(v_currNamespace_984_);
v_openDecls_985_ = lean_ctor_get(v___y_981_, 7);
lean_inc(v_openDecls_985_);
lean_dec_ref(v___y_981_);
v_env_986_ = lean_ctor_get(v___x_983_, 0);
v_nextMacroScope_987_ = lean_ctor_get(v___x_983_, 1);
v_ngen_988_ = lean_ctor_get(v___x_983_, 2);
v_auxDeclNGen_989_ = lean_ctor_get(v___x_983_, 3);
v_traceState_990_ = lean_ctor_get(v___x_983_, 4);
v_cache_991_ = lean_ctor_get(v___x_983_, 5);
v_messages_992_ = lean_ctor_get(v___x_983_, 6);
v_infoState_993_ = lean_ctor_get(v___x_983_, 7);
v_snapshotTasks_994_ = lean_ctor_get(v___x_983_, 8);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_996_ = v___x_983_;
v_isShared_997_ = v_isSharedCheck_1008_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_snapshotTasks_994_);
lean_inc(v_infoState_993_);
lean_inc(v_messages_992_);
lean_inc(v_cache_991_);
lean_inc(v_traceState_990_);
lean_inc(v_auxDeclNGen_989_);
lean_inc(v_ngen_988_);
lean_inc(v_nextMacroScope_987_);
lean_inc(v_env_986_);
lean_dec(v___x_983_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1008_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v_currNamespace_984_);
lean_ctor_set(v___x_998_, 1, v_openDecls_985_);
v___x_999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___y_975_);
v___x_1000_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1000_, 0, v___y_974_);
lean_ctor_set(v___x_1000_, 1, v___y_978_);
lean_ctor_set(v___x_1000_, 2, v___y_980_);
lean_ctor_set(v___x_1000_, 3, v___y_979_);
lean_ctor_set(v___x_1000_, 4, v___x_999_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*5, v___y_977_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*5 + 1, v___y_976_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*5 + 2, v_isSilent_967_);
v___x_1001_ = l_Lean_MessageLog_add(v___x_1000_, v_messages_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 6, v___x_1001_);
v___x_1003_ = v___x_996_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_env_986_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_nextMacroScope_987_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_ngen_988_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_auxDeclNGen_989_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_traceState_990_);
lean_ctor_set(v_reuseFailAlloc_1007_, 5, v_cache_991_);
lean_ctor_set(v_reuseFailAlloc_1007_, 6, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1007_, 7, v_infoState_993_);
lean_ctor_set(v_reuseFailAlloc_1007_, 8, v_snapshotTasks_994_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_st_ref_set(v___y_982_, v___x_1003_);
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
}
v___jp_1009_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1033_; 
v___x_1018_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_965_);
v___x_1019_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__0(v___x_1018_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1033_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1033_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_inc_ref(v___y_1012_);
v___x_1024_ = l_Lean_FileMap_toPosition(v___y_1012_, v___y_1016_);
lean_dec(v___y_1016_);
v___x_1025_ = l_Lean_FileMap_toPosition(v___y_1012_, v___y_1017_);
lean_dec(v___y_1017_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__0));
if (v___y_1014_ == 0)
{
lean_del_object(v___x_1022_);
lean_dec_ref(v___y_1010_);
v___y_974_ = v___y_1011_;
v___y_975_ = v_a_1020_;
v___y_976_ = v___y_1013_;
v___y_977_ = v___y_1015_;
v___y_978_ = v___x_1024_;
v___y_979_ = v___x_1027_;
v___y_980_ = v___x_1026_;
v___y_981_ = v___y_970_;
v___y_982_ = v___y_971_;
goto v___jp_973_;
}
else
{
uint8_t v___x_1028_; 
lean_inc(v_a_1020_);
v___x_1028_ = l_Lean_MessageData_hasTag(v___y_1010_, v_a_1020_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_dec_ref(v___x_1026_);
lean_dec_ref(v___x_1024_);
lean_dec(v_a_1020_);
lean_dec_ref(v___y_1011_);
lean_dec_ref(v___y_970_);
v___x_1029_ = lean_box(0);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1029_);
v___x_1031_ = v___x_1022_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_del_object(v___x_1022_);
v___y_974_ = v___y_1011_;
v___y_975_ = v_a_1020_;
v___y_976_ = v___y_1013_;
v___y_977_ = v___y_1015_;
v___y_978_ = v___x_1024_;
v___y_979_ = v___x_1027_;
v___y_980_ = v___x_1026_;
v___y_981_ = v___y_970_;
v___y_982_ = v___y_971_;
goto v___jp_973_;
}
}
}
}
v___jp_1034_:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Syntax_getTailPos_x3f(v___y_1039_, v___y_1040_);
lean_dec(v___y_1039_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_inc(v___y_1042_);
v___y_1010_ = v___y_1035_;
v___y_1011_ = v___y_1036_;
v___y_1012_ = v___y_1037_;
v___y_1013_ = v___y_1038_;
v___y_1014_ = v___y_1041_;
v___y_1015_ = v___y_1040_;
v___y_1016_ = v___y_1042_;
v___y_1017_ = v___y_1042_;
goto v___jp_1009_;
}
else
{
lean_object* v_val_1044_; 
v_val_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_val_1044_);
lean_dec_ref(v___x_1043_);
v___y_1010_ = v___y_1035_;
v___y_1011_ = v___y_1036_;
v___y_1012_ = v___y_1037_;
v___y_1013_ = v___y_1038_;
v___y_1014_ = v___y_1041_;
v___y_1015_ = v___y_1040_;
v___y_1016_ = v___y_1042_;
v___y_1017_ = v_val_1044_;
goto v___jp_1009_;
}
}
v___jp_1045_:
{
lean_object* v_ref_1053_; lean_object* v___x_1054_; 
v_ref_1053_ = l_Lean_replaceRef(v_ref_964_, v___y_1048_);
lean_dec(v___y_1048_);
v___x_1054_ = l_Lean_Syntax_getPos_x3f(v_ref_1053_, v___y_1051_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___y_1035_ = v___y_1046_;
v___y_1036_ = v___y_1047_;
v___y_1037_ = v___y_1049_;
v___y_1038_ = v___y_1052_;
v___y_1039_ = v_ref_1053_;
v___y_1040_ = v___y_1051_;
v___y_1041_ = v___y_1050_;
v___y_1042_ = v___x_1055_;
goto v___jp_1034_;
}
else
{
lean_object* v_val_1056_; 
v_val_1056_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_val_1056_);
lean_dec_ref(v___x_1054_);
v___y_1035_ = v___y_1046_;
v___y_1036_ = v___y_1047_;
v___y_1037_ = v___y_1049_;
v___y_1038_ = v___y_1052_;
v___y_1039_ = v_ref_1053_;
v___y_1040_ = v___y_1051_;
v___y_1041_ = v___y_1050_;
v___y_1042_ = v_val_1056_;
goto v___jp_1034_;
}
}
v___jp_1058_:
{
if (v___y_1065_ == 0)
{
v___y_1046_ = v___y_1062_;
v___y_1047_ = v___y_1060_;
v___y_1048_ = v___y_1059_;
v___y_1049_ = v___y_1061_;
v___y_1050_ = v___y_1063_;
v___y_1051_ = v___y_1064_;
v___y_1052_ = v_severity_966_;
goto v___jp_1045_;
}
else
{
v___y_1046_ = v___y_1062_;
v___y_1047_ = v___y_1060_;
v___y_1048_ = v___y_1059_;
v___y_1049_ = v___y_1061_;
v___y_1050_ = v___y_1063_;
v___y_1051_ = v___y_1064_;
v___y_1052_ = v___x_1057_;
goto v___jp_1045_;
}
}
v___jp_1066_:
{
if (v___y_1067_ == 0)
{
lean_object* v_fileName_1068_; lean_object* v_fileMap_1069_; lean_object* v_options_1070_; lean_object* v_ref_1071_; uint8_t v_suppressElabErrors_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___f_1075_; uint8_t v___x_1076_; uint8_t v___x_1077_; 
v_fileName_1068_ = lean_ctor_get(v___y_970_, 0);
v_fileMap_1069_ = lean_ctor_get(v___y_970_, 1);
v_options_1070_ = lean_ctor_get(v___y_970_, 2);
v_ref_1071_ = lean_ctor_get(v___y_970_, 5);
v_suppressElabErrors_1072_ = lean_ctor_get_uint8(v___y_970_, sizeof(void*)*14 + 1);
v___x_1073_ = lean_box(v___y_1067_);
v___x_1074_ = lean_box(v_suppressElabErrors_1072_);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1075_, 0, v___x_1073_);
lean_closure_set(v___f_1075_, 1, v___x_1074_);
v___x_1076_ = 1;
v___x_1077_ = l_Lean_instBEqMessageSeverity_beq(v_severity_966_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_inc_ref(v_fileMap_1069_);
lean_inc_ref(v_fileName_1068_);
lean_inc(v_ref_1071_);
v___y_1059_ = v_ref_1071_;
v___y_1060_ = v_fileName_1068_;
v___y_1061_ = v_fileMap_1069_;
v___y_1062_ = v___f_1075_;
v___y_1063_ = v_suppressElabErrors_1072_;
v___y_1064_ = v___y_1067_;
v___y_1065_ = v___x_1077_;
goto v___jp_1058_;
}
else
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = l_Lean_warningAsError;
v___x_1079_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1070_, v___x_1078_);
lean_inc_ref(v_fileMap_1069_);
lean_inc_ref(v_fileName_1068_);
lean_inc(v_ref_1071_);
v___y_1059_ = v_ref_1071_;
v___y_1060_ = v_fileName_1068_;
v___y_1061_ = v_fileMap_1069_;
v___y_1062_ = v___f_1075_;
v___y_1063_ = v_suppressElabErrors_1072_;
v___y_1064_ = v___y_1067_;
v___y_1065_ = v___x_1079_;
goto v___jp_1058_;
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v___y_970_);
lean_dec_ref(v_msgData_965_);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_1084_, lean_object* v_msgData_1085_, lean_object* v_severity_1086_, lean_object* v_isSilent_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
uint8_t v_severity_boxed_1093_; uint8_t v_isSilent_boxed_1094_; lean_object* v_res_1095_; 
v_severity_boxed_1093_ = lean_unbox(v_severity_1086_);
v_isSilent_boxed_1094_ = lean_unbox(v_isSilent_1087_);
v_res_1095_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1084_, v_msgData_1085_, v_severity_boxed_1093_, v_isSilent_boxed_1094_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v_ref_1084_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(lean_object* v_msgData_1096_, uint8_t v_severity_1097_, uint8_t v_isSilent_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_ref_1104_; lean_object* v___x_1105_; 
v_ref_1104_ = lean_ctor_get(v___y_1101_, 5);
lean_inc(v_ref_1104_);
v___x_1105_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1104_, v_msgData_1096_, v_severity_1097_, v_isSilent_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v_ref_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1___boxed(lean_object* v_msgData_1106_, lean_object* v_severity_1107_, lean_object* v_isSilent_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v_severity_boxed_1114_; uint8_t v_isSilent_boxed_1115_; lean_object* v_res_1116_; 
v_severity_boxed_1114_ = lean_unbox(v_severity_1107_);
v_isSilent_boxed_1115_ = lean_unbox(v_isSilent_1108_);
v_res_1116_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1106_, v_severity_boxed_1114_, v_isSilent_boxed_1115_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(lean_object* v_msgData_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
uint8_t v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = 1;
v___x_1124_ = 0;
v___x_1125_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1117_, v___x_1123_, v___x_1124_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1___boxed(lean_object* v_msgData_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(v_msgData_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1132_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__0));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(lean_object* v_a_1142_, lean_object* v___x_1143_, lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v___x_1146_, lean_object* v_tk_1147_, lean_object* v_a_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___y_1159_; lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1150_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1173_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
v___x_1173_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(v_a_1172_, v_a_1142_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v___x_1173_);
if (lean_obj_tag(v_a_1174_) == 0)
{
lean_object* v_ref_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec_ref(v_a_1148_);
v_ref_1175_ = lean_ctor_get(v___y_1155_, 5);
v___x_1176_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__1);
lean_inc_ref(v___y_1155_);
v___x_1177_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__1(v___x_1176_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1198_; 
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v___x_1177_, 0);
lean_dec(v_unused_1199_);
v___x_1179_ = v___x_1177_;
v_isShared_1180_ = v_isSharedCheck_1198_;
goto v_resetjp_1178_;
}
else
{
lean_dec(v___x_1177_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1198_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1181_ = 0;
v___x_1182_ = l_Lean_SourceInfo_fromRef(v_ref_1175_, v___x_1181_);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__2));
lean_inc(v___x_1182_);
v___x_1184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__4));
v___x_1186_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__5));
v___x_1187_ = l_Lean_Name_mkStr4(v___x_1143_, v___x_1144_, v___x_1145_, v___x_1186_);
v___x_1188_ = l_Lean_Syntax_node2(v___x_1182_, v___x_1187_, v___x_1184_, v___x_1146_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1185_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
lean_ctor_set(v___x_1191_, 3, v___x_1190_);
lean_ctor_set(v___x_1191_, 4, v___x_1190_);
lean_ctor_set(v___x_1191_, 5, v___x_1190_);
lean_inc(v_ref_1175_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 1);
lean_ctor_set(v___x_1179_, 0, v_ref_1175_);
v___x_1193_ = v___x_1179_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_ref_1175_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___closed__6));
v___x_1195_ = 4;
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
v___x_1196_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1147_, v___x_1191_, v___x_1193_, v___x_1194_, v___x_1190_, v___x_1195_, v___y_1155_, v___y_1156_);
v___y_1159_ = v___x_1196_;
goto v___jp_1158_;
}
}
}
else
{
lean_dec(v_tk_1147_);
lean_dec(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
v___y_1159_ = v___x_1177_;
goto v___jp_1158_;
}
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1201_; 
lean_dec(v_tk_1147_);
lean_dec(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
v_val_1200_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_val_1200_);
lean_dec_ref(v_a_1174_);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
v___x_1201_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(v_val_1200_, v_a_1148_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
v___y_1159_ = v___x_1201_;
goto v___jp_1158_;
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec_ref(v_a_1148_);
lean_dec(v_tk_1147_);
lean_dec(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
v_a_1202_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1173_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1173_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec_ref(v_a_1148_);
lean_dec(v_tk_1147_);
lean_dec(v___x_1146_);
lean_dec_ref(v___x_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___x_1143_);
lean_dec_ref(v_a_1142_);
v_a_1210_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1171_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1171_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
v___jp_1158_:
{
if (lean_obj_tag(v___y_1159_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec_ref(v___y_1159_);
v___x_1160_ = lean_box(0);
v___x_1161_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1160_, v___y_1150_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1169_; 
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v___x_1161_, 0);
lean_dec(v_unused_1170_);
v___x_1163_ = v___x_1161_;
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
else
{
lean_dec(v___x_1161_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
return v___x_1161_;
}
}
else
{
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v___y_1159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed(lean_object* v_a_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v_tk_1223_, lean_object* v_a_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0(v_a_1218_, v___x_1219_, v___x_1220_, v___x_1221_, v___x_1222_, v_tk_1223_, v_a_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(lean_object* v_x_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1262_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__0));
v___x_1263_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1));
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lam__1___closed__2));
v___x_1265_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3));
lean_inc(v_x_1252_);
v___x_1266_ = l_Lean_Syntax_isOfKind(v_x_1252_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_x_1252_);
v___x_1267_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = l_Lean_Syntax_getArg(v_x_1252_, v___x_1268_);
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5));
lean_inc(v___x_1269_);
v___x_1271_ = l_Lean_Syntax_isOfKind(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_dec(v___x_1269_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_x_1252_);
v___x_1272_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v_path_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1273_ = lean_unsigned_to_nat(2u);
v_path_1274_ = l_Lean_Syntax_getArg(v_x_1252_, v___x_1273_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__7));
lean_inc(v_path_1274_);
v___x_1276_ = l_Lean_Syntax_isOfKind(v_path_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; 
lean_dec(v_path_1274_);
lean_dec(v___x_1269_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_x_1252_);
v___x_1277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck_spec__0___redArg();
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; 
lean_inc(v_a_1260_);
lean_inc_ref(v_a_1259_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v___x_1269_);
v___x_1278_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v___x_1269_, v_a_1253_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = l_Lean_TSyntax_getString(v_path_1274_);
lean_dec(v_path_1274_);
lean_inc_ref(v_a_1259_);
lean_inc_ref(v_a_1255_);
lean_inc(v_a_1279_);
v___x_1281_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(v___x_1280_, v_a_1279_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1283_; lean_object* v_tk_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = lean_unsigned_to_nat(0u);
v_tk_1284_ = l_Lean_Syntax_getArg(v_x_1252_, v___x_1283_);
lean_dec(v_x_1252_);
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1285_, 0, v_a_1279_);
lean_closure_set(v___f_1285_, 1, v___x_1262_);
lean_closure_set(v___f_1285_, 2, v___x_1263_);
lean_closure_set(v___f_1285_, 3, v___x_1264_);
lean_closure_set(v___f_1285_, 4, v___x_1269_);
lean_closure_set(v___f_1285_, 5, v_tk_1284_);
lean_closure_set(v___f_1285_, 6, v_a_1282_);
v___x_1286_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1285_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
return v___x_1286_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_a_1279_);
lean_dec(v___x_1269_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_x_1252_);
v_a_1287_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1281_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1281_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_path_1274_);
lean_dec(v___x_1269_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_x_1252_);
v_a_1295_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1278_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1278_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed(lean_object* v_x_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(v_x_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1327_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3));
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4));
v___x_1330_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___boxed), 10, 0);
v___x_1331_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1327_, v___x_1328_, v___x_1329_, v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___boxed(lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1();
return v_res_1333_;
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
