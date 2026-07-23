// Lean compiler output
// Module: Lean.PostprocessTraces.Basic
// Imports: public meta import Lean.Elab.Command public meta import Lean.Meta.Eval import Lean.CoreM
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLe(double, double);
double lean_float_add(double, double);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toArray(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTraceTree;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor = (const lean_object*)&l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f___boxed(lean_object*);
static const lean_array_object l_Lean_PostprocessTraces_TraceTree_children___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PostprocessTraces_TraceTree_children___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_TraceTree_children___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_withChildren(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_modifyData(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0;
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_elapsed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_elapsed___boxed(lean_object*);
LEAN_EXPORT double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(lean_object*, size_t, size_t, double);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_selfElapsed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_selfElapsed___boxed(lean_object*);
static const lean_string_object l_Lean_PostprocessTraces_TraceTree_headText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_PostprocessTraces_TraceTree_headText___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_TraceTree_headText___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__0_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_traceContainer_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0;
static lean_once_cell_t l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1;
static lean_once_cell_t l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2;
static const lean_array_object l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value_aux_2),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3_value),LEAN_SCALAR_PTR_LITERAL(77, 46, 79, 112, 232, 100, 17, 35)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value_aux_2),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__6_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__8 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__8_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.PostprocessTraces"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "PostprocessTraces"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__14 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__14_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__17 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__17_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value_aux_2),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__17_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__19 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__19_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value_aux_2),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__19_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__22_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12_value),LEAN_SCALAR_PTR_LITERAL(131, 135, 26, 65, 16, 127, 78, 49)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__27_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__28 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__28_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__26_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__29_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__30 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__30_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__30_value),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__31 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__31_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__28_value),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__31_value)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "TracePostprocessor"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34_value),LEAN_SCALAR_PTR_LITERAL(251, 174, 159, 176, 196, 77, 180, 200)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value_aux_0),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__12_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value_aux_1),((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34_value),LEAN_SCALAR_PTR_LITERAL(33, 98, 63, 149, 37, 148, 219, 124)}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38_value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39_value;
static const lean_string_object l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40 = (const lean_object*)&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40_value;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41;
static lean_once_cell_t l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42;
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_PostprocessTraces_TraceTree_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_data_8_; lean_object* v_msg_9_; lean_object* v_children_10_; lean_object* v_wrap_11_; lean_object* v___x_12_; 
v_data_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_data_8_);
v_msg_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_msg_9_);
v_children_10_ = lean_ctor_get(v_t_6_, 2);
lean_inc_ref(v_children_10_);
v_wrap_11_ = lean_ctor_get(v_t_6_, 3);
lean_inc_ref(v_wrap_11_);
lean_dec_ref_known(v_t_6_, 4);
v___x_12_ = lean_apply_4(v_k_7_, v_data_8_, v_msg_9_, v_children_10_, v_wrap_11_);
return v___x_12_;
}
else
{
lean_object* v_msg_13_; lean_object* v___x_14_; 
v_msg_13_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_msg_13_);
lean_dec_ref_known(v_t_6_, 1);
v___x_14_ = lean_apply_1(v_k_7_, v_msg_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim(lean_object* v_motive__1_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___boxed(lean_object* v_motive__1_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_PostprocessTraces_TraceTree_ctorElim(v_motive__1_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim___redArg(lean_object* v_t_27_, lean_object* v_node_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_27_, v_node_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim(lean_object* v_motive__1_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_node_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_31_, v_node_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim___redArg(lean_object* v_t_35_, lean_object* v_leaf_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_35_, v_leaf_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim(lean_object* v_motive__1_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_leaf_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_39_, v_leaf_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = l_Lean_MessageData_nil;
v___x_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_instInhabitedTraceTree(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0, &l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0_once, _init_l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0(lean_object* v_a_46_, lean_object* v_wrap_47_, lean_object* v_m_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_49_, 0, v_a_46_);
lean_ctor_set(v___x_49_, 1, v_m_48_);
v___x_50_ = lean_apply_1(v_wrap_47_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1(lean_object* v_a_51_, lean_object* v_wrap_52_, lean_object* v_m_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_54_, 0, v_a_51_);
lean_ctor_set(v___x_54_, 1, v_m_53_);
v___x_55_ = lean_apply_1(v_wrap_52_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0(lean_object* v___y_56_){
_start:
{
lean_inc_ref(v___y_56_);
return v___y_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0___boxed(lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0(v___y_57_);
lean_dec_ref(v___y_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(lean_object* v_wrap_60_, lean_object* v_a_61_){
_start:
{
switch(lean_obj_tag(v_a_61_))
{
case 3:
{
lean_object* v_a_62_; lean_object* v_a_63_; lean_object* v___f_64_; 
v_a_62_ = lean_ctor_get(v_a_61_, 0);
lean_inc_ref(v_a_62_);
v_a_63_ = lean_ctor_get(v_a_61_, 1);
lean_inc_ref(v_a_63_);
lean_dec_ref_known(v_a_61_, 2);
v___f_64_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0), 3, 2);
lean_closure_set(v___f_64_, 0, v_a_62_);
lean_closure_set(v___f_64_, 1, v_wrap_60_);
v_wrap_60_ = v___f_64_;
v_a_61_ = v_a_63_;
goto _start;
}
case 4:
{
lean_object* v_a_66_; lean_object* v_a_67_; lean_object* v___f_68_; 
v_a_66_ = lean_ctor_get(v_a_61_, 0);
lean_inc_ref(v_a_66_);
v_a_67_ = lean_ctor_get(v_a_61_, 1);
lean_inc_ref(v_a_67_);
lean_dec_ref_known(v_a_61_, 2);
v___f_68_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1), 3, 2);
lean_closure_set(v___f_68_, 0, v_a_66_);
lean_closure_set(v___f_68_, 1, v_wrap_60_);
v_wrap_60_ = v___f_68_;
v_a_61_ = v_a_67_;
goto _start;
}
case 9:
{
lean_object* v_data_70_; lean_object* v_msg_71_; lean_object* v_children_72_; size_t v_sz_73_; size_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_data_70_ = lean_ctor_get(v_a_61_, 0);
lean_inc_ref(v_data_70_);
v_msg_71_ = lean_ctor_get(v_a_61_, 1);
lean_inc_ref(v_msg_71_);
v_children_72_ = lean_ctor_get(v_a_61_, 2);
lean_inc_ref(v_children_72_);
lean_dec_ref_known(v_a_61_, 3);
v_sz_73_ = lean_array_size(v_children_72_);
v___x_74_ = ((size_t)0ULL);
v___x_75_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(v_sz_73_, v___x_74_, v_children_72_);
v___x_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_76_, 0, v_data_70_);
lean_ctor_set(v___x_76_, 1, v_msg_71_);
lean_ctor_set(v___x_76_, 2, v___x_75_);
lean_ctor_set(v___x_76_, 3, v_wrap_60_);
return v___x_76_;
}
default: 
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_apply_1(v_wrap_60_, v_a_61_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(size_t v_sz_79_, size_t v_i_80_, lean_object* v_bs_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = lean_usize_dec_lt(v_i_80_, v_sz_79_);
if (v___x_82_ == 0)
{
return v_bs_81_;
}
else
{
lean_object* v___f_83_; lean_object* v_v_84_; lean_object* v___x_85_; lean_object* v_bs_x27_86_; lean_object* v___x_87_; size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
v___f_83_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0));
v_v_84_ = lean_array_uget(v_bs_81_, v_i_80_);
v___x_85_ = lean_unsigned_to_nat(0u);
v_bs_x27_86_ = lean_array_uset(v_bs_81_, v_i_80_, v___x_85_);
v___x_87_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(v___f_83_, v_v_84_);
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_add(v_i_80_, v___x_88_);
v___x_90_ = lean_array_uset(v_bs_x27_86_, v_i_80_, v___x_87_);
v_i_80_ = v___x_89_;
v_bs_81_ = v___x_90_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___boxed(lean_object* v_sz_92_, lean_object* v_i_93_, lean_object* v_bs_94_){
_start:
{
size_t v_sz_boxed_95_; size_t v_i_boxed_96_; lean_object* v_res_97_; 
v_sz_boxed_95_ = lean_unbox_usize(v_sz_92_);
lean_dec(v_sz_92_);
v_i_boxed_96_ = lean_unbox_usize(v_i_93_);
lean_dec(v_i_93_);
v_res_97_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(v_sz_boxed_95_, v_i_boxed_96_, v_bs_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0(lean_object* v___y_98_){
_start:
{
lean_inc_ref(v___y_98_);
return v___y_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0___boxed(lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0(v___y_99_);
lean_dec_ref(v___y_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData(lean_object* v_msg_102_){
_start:
{
lean_object* v___f_103_; lean_object* v___x_104_; 
v___f_103_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0));
v___x_104_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(v___f_103_, v_msg_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(size_t v_sz_105_, size_t v_i_106_, lean_object* v_bs_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_usize_dec_lt(v_i_106_, v_sz_105_);
if (v___x_108_ == 0)
{
return v_bs_107_;
}
else
{
lean_object* v_v_109_; lean_object* v___x_110_; lean_object* v_bs_x27_111_; lean_object* v___x_112_; size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; 
v_v_109_ = lean_array_uget(v_bs_107_, v_i_106_);
v___x_110_ = lean_unsigned_to_nat(0u);
v_bs_x27_111_ = lean_array_uset(v_bs_107_, v_i_106_, v___x_110_);
v___x_112_ = l_Lean_PostprocessTraces_TraceTree_toMessageData(v_v_109_);
v___x_113_ = ((size_t)1ULL);
v___x_114_ = lean_usize_add(v_i_106_, v___x_113_);
v___x_115_ = lean_array_uset(v_bs_x27_111_, v_i_106_, v___x_112_);
v_i_106_ = v___x_114_;
v_bs_107_ = v___x_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_toMessageData(lean_object* v_x_117_){
_start:
{
if (lean_obj_tag(v_x_117_) == 0)
{
lean_object* v_data_118_; lean_object* v_msg_119_; lean_object* v_children_120_; lean_object* v_wrap_121_; size_t v_sz_122_; size_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_data_118_ = lean_ctor_get(v_x_117_, 0);
lean_inc_ref(v_data_118_);
v_msg_119_ = lean_ctor_get(v_x_117_, 1);
lean_inc_ref(v_msg_119_);
v_children_120_ = lean_ctor_get(v_x_117_, 2);
lean_inc_ref(v_children_120_);
v_wrap_121_ = lean_ctor_get(v_x_117_, 3);
lean_inc_ref(v_wrap_121_);
lean_dec_ref_known(v_x_117_, 4);
v_sz_122_ = lean_array_size(v_children_120_);
v___x_123_ = ((size_t)0ULL);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_122_, v___x_123_, v_children_120_);
v___x_125_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_125_, 0, v_data_118_);
lean_ctor_set(v___x_125_, 1, v_msg_119_);
lean_ctor_set(v___x_125_, 2, v___x_124_);
v___x_126_ = lean_apply_1(v_wrap_121_, v___x_125_);
return v___x_126_;
}
else
{
lean_object* v_msg_127_; 
v_msg_127_ = lean_ctor_get(v_x_117_, 0);
lean_inc_ref(v_msg_127_);
lean_dec_ref_known(v_x_117_, 1);
return v_msg_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0___boxed(lean_object* v_sz_128_, lean_object* v_i_129_, lean_object* v_bs_130_){
_start:
{
size_t v_sz_boxed_131_; size_t v_i_boxed_132_; lean_object* v_res_133_; 
v_sz_boxed_131_ = lean_unbox_usize(v_sz_128_);
lean_dec(v_sz_128_);
v_i_boxed_132_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_boxed_131_, v_i_boxed_132_, v_bs_130_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(lean_object* v_roots_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_roots_134_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0___boxed(lean_object* v_roots_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(v_roots_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f(lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v_data_147_; lean_object* v___x_148_; 
v_data_147_ = lean_ctor_get(v_x_146_, 0);
lean_inc_ref(v_data_147_);
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v_data_147_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_box(0);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f___boxed(lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_x_150_);
lean_dec_ref(v_x_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f(lean_object* v_t_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_152_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_163_; 
v_val_155_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_163_ == 0)
{
v___x_157_ = v___x_153_;
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_val_155_);
lean_dec(v___x_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v_cls_159_; lean_object* v___x_161_; 
v_cls_159_ = lean_ctor_get(v_val_155_, 0);
lean_inc(v_cls_159_);
lean_dec(v_val_155_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v_cls_159_);
v___x_161_ = v___x_157_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_cls_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f___boxed(lean_object* v_t_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_164_);
lean_dec_ref(v_t_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children(lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v_children_169_; 
v_children_169_ = lean_ctor_get(v_x_168_, 2);
lean_inc_ref(v_children_169_);
return v_children_169_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children___boxed(lean_object* v_x_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_PostprocessTraces_TraceTree_children(v_x_171_);
lean_dec_ref(v_x_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_withChildren(lean_object* v_t_173_, lean_object* v_children_174_){
_start:
{
if (lean_obj_tag(v_t_173_) == 0)
{
lean_object* v_data_175_; lean_object* v_msg_176_; lean_object* v_wrap_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_data_175_ = lean_ctor_get(v_t_173_, 0);
v_msg_176_ = lean_ctor_get(v_t_173_, 1);
v_wrap_177_ = lean_ctor_get(v_t_173_, 3);
v_isSharedCheck_184_ = !lean_is_exclusive(v_t_173_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v_t_173_, 2);
lean_dec(v_unused_185_);
v___x_179_ = v_t_173_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_wrap_177_);
lean_inc(v_msg_176_);
lean_inc(v_data_175_);
lean_dec(v_t_173_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 2, v_children_174_);
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_data_175_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_msg_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_children_174_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v_wrap_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_dec_ref(v_children_174_);
return v_t_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_modifyData(lean_object* v_t_186_, lean_object* v_f_187_){
_start:
{
if (lean_obj_tag(v_t_186_) == 0)
{
lean_object* v_data_188_; lean_object* v_msg_189_; lean_object* v_children_190_; lean_object* v_wrap_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_199_; 
v_data_188_ = lean_ctor_get(v_t_186_, 0);
v_msg_189_ = lean_ctor_get(v_t_186_, 1);
v_children_190_ = lean_ctor_get(v_t_186_, 2);
v_wrap_191_ = lean_ctor_get(v_t_186_, 3);
v_isSharedCheck_199_ = !lean_is_exclusive(v_t_186_);
if (v_isSharedCheck_199_ == 0)
{
v___x_193_ = v_t_186_;
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_wrap_191_);
lean_inc(v_children_190_);
lean_inc(v_msg_189_);
lean_inc(v_data_188_);
lean_dec(v_t_186_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_199_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_apply_1(v_f_187_, v_data_188_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_msg_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v_children_190_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v_wrap_191_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_dec_ref(v_f_187_);
return v_t_186_;
}
}
}
static double _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0(void){
_start:
{
lean_object* v___x_200_; double v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_float_of_nat(v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_elapsed(lean_object* v_t_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
double v___x_204_; 
v___x_204_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
return v___x_204_;
}
else
{
lean_object* v_val_205_; double v_startTime_206_; double v_stopTime_207_; double v___x_208_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v___x_203_, 1);
v_startTime_206_ = lean_ctor_get_float(v_val_205_, sizeof(void*)*3);
v_stopTime_207_ = lean_ctor_get_float(v_val_205_, sizeof(void*)*3 + 8);
lean_dec(v_val_205_);
v___x_208_ = lean_float_sub(v_stopTime_207_, v_startTime_206_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_elapsed___boxed(lean_object* v_t_209_){
_start:
{
double v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_209_);
lean_dec_ref(v_t_209_);
v_r_211_ = lean_box_float(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(lean_object* v_as_212_, size_t v_i_213_, size_t v_stop_214_, double v_b_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_eq(v_i_213_, v_stop_214_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; double v___x_218_; double v___x_219_; size_t v___x_220_; size_t v___x_221_; 
v___x_217_ = lean_array_uget_borrowed(v_as_212_, v_i_213_);
v___x_218_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v___x_217_);
v___x_219_ = lean_float_add(v_b_215_, v___x_218_);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_add(v_i_213_, v___x_220_);
v_i_213_ = v___x_221_;
v_b_215_ = v___x_219_;
goto _start;
}
else
{
return v_b_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0___boxed(lean_object* v_as_223_, lean_object* v_i_224_, lean_object* v_stop_225_, lean_object* v_b_226_){
_start:
{
size_t v_i_boxed_227_; size_t v_stop_boxed_228_; double v_b_boxed_229_; double v_res_230_; lean_object* v_r_231_; 
v_i_boxed_227_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_stop_boxed_228_ = lean_unbox_usize(v_stop_225_);
lean_dec(v_stop_225_);
v_b_boxed_229_ = lean_unbox_float(v_b_226_);
lean_dec_ref(v_b_226_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v_as_223_, v_i_boxed_227_, v_stop_boxed_228_, v_b_boxed_229_);
lean_dec_ref(v_as_223_);
v_r_231_ = lean_box_float(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_selfElapsed(lean_object* v_t_232_){
_start:
{
lean_object* v___x_233_; double v___x_234_; double v___x_235_; double v___y_237_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
v___x_235_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_232_);
v___x_240_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_232_);
v___x_241_ = lean_array_get_size(v___x_240_);
v___x_242_ = lean_nat_dec_lt(v___x_233_, v___x_241_);
if (v___x_242_ == 0)
{
lean_dec_ref(v___x_240_);
v___y_237_ = v___x_234_;
goto v___jp_236_;
}
else
{
uint8_t v___x_243_; 
v___x_243_ = lean_nat_dec_le(v___x_241_, v___x_241_);
if (v___x_243_ == 0)
{
if (v___x_242_ == 0)
{
lean_dec_ref(v___x_240_);
v___y_237_ = v___x_234_;
goto v___jp_236_;
}
else
{
size_t v___x_244_; size_t v___x_245_; double v___x_246_; 
v___x_244_ = ((size_t)0ULL);
v___x_245_ = lean_usize_of_nat(v___x_241_);
v___x_246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_240_, v___x_244_, v___x_245_, v___x_234_);
lean_dec_ref(v___x_240_);
v___y_237_ = v___x_246_;
goto v___jp_236_;
}
}
else
{
size_t v___x_247_; size_t v___x_248_; double v___x_249_; 
v___x_247_ = ((size_t)0ULL);
v___x_248_ = lean_usize_of_nat(v___x_241_);
v___x_249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_240_, v___x_247_, v___x_248_, v___x_234_);
lean_dec_ref(v___x_240_);
v___y_237_ = v___x_249_;
goto v___jp_236_;
}
}
v___jp_236_:
{
double v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_float_sub(v___x_235_, v___y_237_);
v___x_239_ = lean_float_decLe(v___x_234_, v___x_238_);
if (v___x_239_ == 0)
{
return v___x_234_;
}
else
{
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_selfElapsed___boxed(lean_object* v_t_250_){
_start:
{
double v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_250_);
lean_dec_ref(v_t_250_);
v_r_252_ = lean_box_float(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText(lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v_data_256_; lean_object* v_msg_257_; lean_object* v_wrap_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_result_x3f_261_; 
v_data_256_ = lean_ctor_get(v_x_254_, 0);
lean_inc_ref(v_data_256_);
v_msg_257_ = lean_ctor_get(v_x_254_, 1);
lean_inc_ref(v_msg_257_);
v_wrap_258_ = lean_ctor_get(v_x_254_, 3);
lean_inc_ref(v_wrap_258_);
lean_dec_ref_known(v_x_254_, 4);
v___x_259_ = lean_apply_1(v_wrap_258_, v_msg_257_);
v___x_260_ = l_Lean_MessageData_toString(v___x_259_);
v_result_x3f_261_ = lean_ctor_get(v_data_256_, 1);
lean_inc(v_result_x3f_261_);
lean_dec_ref(v_data_256_);
if (lean_obj_tag(v_result_x3f_261_) == 0)
{
return v___x_260_;
}
else
{
lean_object* v_val_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_val_262_ = lean_ctor_get(v_result_x3f_261_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v_result_x3f_261_, 1);
v___x_263_ = lean_unbox(v_val_262_);
lean_dec(v_val_262_);
v___x_264_ = l_Lean_TraceResult_toEmoji(v___x_263_);
v___x_265_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_headText___closed__0));
v___x_266_ = lean_string_append(v___x_264_, v___x_265_);
v___x_267_ = lean_string_append(v___x_266_, v___x_260_);
lean_dec_ref(v___x_260_);
return v___x_267_;
}
}
else
{
lean_object* v_msg_268_; lean_object* v___x_269_; 
v_msg_268_ = lean_ctor_get(v_x_254_, 0);
lean_inc_ref(v_msg_268_);
lean_dec_ref_known(v_x_254_, 1);
v___x_269_ = l_Lean_MessageData_toString(v_msg_268_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText___boxed(lean_object* v_x_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_PostprocessTraces_TraceTree_headText(v_x_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f(lean_object* v_t_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_box(0);
return v___x_275_;
}
else
{
lean_object* v_val_276_; lean_object* v_result_x3f_277_; 
v_val_276_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_val_276_);
lean_dec_ref_known(v___x_274_, 1);
v_result_x3f_277_ = lean_ctor_get(v_val_276_, 1);
lean_inc(v_result_x3f_277_);
lean_dec(v_val_276_);
return v_result_x3f_277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f___boxed(lean_object* v_t_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_278_);
lean_dec_ref(v_t_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees(lean_object* v_p_280_, lean_object* v_t_281_, lean_object* v_acc_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; 
lean_inc_ref(v_p_280_);
lean_inc(v_a_284_);
lean_inc_ref(v_a_283_);
lean_inc_ref(v_t_281_);
v___x_286_ = lean_apply_4(v_p_280_, v_t_281_, v_a_283_, v_a_284_, lean_box(0));
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_313_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_313_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_313_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_313_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
uint8_t v___x_291_; 
v___x_291_ = lean_unbox(v_a_287_);
lean_dec(v_a_287_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_292_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_281_);
lean_dec_ref(v_t_281_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_array_get_size(v___x_292_);
v___x_295_ = lean_nat_dec_lt(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref(v___x_292_);
lean_dec_ref(v_p_280_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_acc_282_);
v___x_297_ = v___x_289_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_acc_282_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
uint8_t v___x_299_; 
v___x_299_ = lean_nat_dec_le(v___x_294_, v___x_294_);
if (v___x_299_ == 0)
{
if (v___x_295_ == 0)
{
lean_object* v___x_301_; 
lean_dec_ref(v___x_292_);
lean_dec_ref(v_p_280_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_acc_282_);
v___x_301_ = v___x_289_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_acc_282_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
else
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
lean_del_object(v___x_289_);
v___x_303_ = ((size_t)0ULL);
v___x_304_ = lean_usize_of_nat(v___x_294_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_280_, v___x_292_, v___x_303_, v___x_304_, v_acc_282_, v_a_283_, v_a_284_);
lean_dec_ref(v___x_292_);
return v___x_305_;
}
}
else
{
size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
lean_del_object(v___x_289_);
v___x_306_ = ((size_t)0ULL);
v___x_307_ = lean_usize_of_nat(v___x_294_);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_280_, v___x_292_, v___x_306_, v___x_307_, v_acc_282_, v_a_283_, v_a_284_);
lean_dec_ref(v___x_292_);
return v___x_308_;
}
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_311_; 
lean_dec_ref(v_p_280_);
v___x_309_ = lean_array_push(v_acc_282_, v_t_281_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_309_);
v___x_311_ = v___x_289_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_acc_282_);
lean_dec_ref(v_t_281_);
lean_dec_ref(v_p_280_);
v_a_314_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_286_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_286_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(lean_object* v_p_322_, lean_object* v_as_323_, size_t v_i_324_, size_t v_stop_325_, lean_object* v_b_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_eq(v_i_324_, v_stop_325_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_array_uget_borrowed(v_as_323_, v_i_324_);
lean_inc(v___x_331_);
lean_inc_ref(v_p_322_);
v___x_332_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_322_, v___x_331_, v_b_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; size_t v___x_334_; size_t v___x_335_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_332_, 1);
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_324_, v___x_334_);
v_i_324_ = v___x_335_;
v_b_326_ = v_a_333_;
goto _start;
}
else
{
lean_dec_ref(v_p_322_);
return v___x_332_;
}
}
else
{
lean_object* v___x_337_; 
lean_dec_ref(v_p_322_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v_b_326_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0___boxed(lean_object* v_p_338_, lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_stop_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
size_t v_i_boxed_346_; size_t v_stop_boxed_347_; lean_object* v_res_348_; 
v_i_boxed_346_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_stop_boxed_347_ = lean_unbox_usize(v_stop_341_);
lean_dec(v_stop_341_);
v_res_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_338_, v_as_339_, v_i_boxed_346_, v_stop_boxed_347_, v_b_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec_ref(v_as_339_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees___boxed(lean_object* v_p_349_, lean_object* v_t_350_, lean_object* v_acc_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_349_, v_t_350_, v_acc_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(lean_object* v_p_356_, lean_object* v_as_357_, lean_object* v_start_358_, lean_object* v_stop_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
v___x_364_ = lean_nat_dec_lt(v_start_358_, v_stop_359_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec_ref(v_p_356_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_array_get_size(v_as_357_);
v___x_367_ = lean_nat_dec_le(v_stop_359_, v___x_366_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
v___x_368_ = lean_nat_dec_lt(v_start_358_, v___x_366_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec_ref(v_p_356_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_363_);
return v___x_369_;
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_usize_of_nat(v_start_358_);
v___x_371_ = lean_usize_of_nat(v___x_366_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_356_, v_as_357_, v___x_370_, v___x_371_, v___x_363_, v___y_360_, v___y_361_);
return v___x_372_;
}
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_usize_of_nat(v_start_358_);
v___x_374_ = lean_usize_of_nat(v_stop_359_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_356_, v_as_357_, v___x_373_, v___x_374_, v___x_363_, v___y_360_, v___y_361_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees(lean_object* v_p_376_, lean_object* v_t_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
lean_inc_ref(v_p_376_);
lean_inc(v_a_379_);
lean_inc_ref(v_a_378_);
lean_inc_ref(v_t_377_);
v___x_381_ = lean_apply_4(v_p_376_, v_t_377_, v_a_378_, v_a_379_, lean_box(0));
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_419_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_419_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_419_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_419_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint8_t v___x_386_; 
v___x_386_ = lean_unbox(v_a_382_);
lean_dec(v_a_382_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
lean_del_object(v___x_384_);
v___x_387_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_377_);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_array_get_size(v___x_387_);
v___x_390_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_376_, v___x_387_, v___x_388_, v___x_389_, v_a_378_, v_a_379_);
lean_dec_ref(v___x_387_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_406_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_406_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_406_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_406_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_array_get_size(v_a_391_);
v___x_396_ = lean_nat_dec_eq(v___x_395_, v___x_388_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_377_, v_a_391_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_398_);
v___x_400_ = v___x_393_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec(v_a_391_);
lean_dec_ref(v_t_377_);
v___x_402_ = lean_box(0);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_402_);
v___x_404_ = v___x_393_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v_t_377_);
v_a_407_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_390_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_390_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec_ref(v_p_376_);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v_t_377_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_415_);
v___x_417_ = v___x_384_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec_ref(v_t_377_);
lean_dec_ref(v_p_376_);
v_a_420_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_381_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_381_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(lean_object* v_p_428_, lean_object* v_as_429_, size_t v_i_430_, size_t v_stop_431_, lean_object* v_b_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_eq(v_i_430_, v_stop_431_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_array_uget_borrowed(v_as_429_, v_i_430_);
lean_inc(v___x_437_);
lean_inc_ref(v_p_428_);
v___x_438_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_428_, v___x_437_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v_a_441_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
if (lean_obj_tag(v_a_439_) == 0)
{
v_a_441_ = v_b_432_;
goto v___jp_440_;
}
else
{
lean_object* v_val_445_; lean_object* v___x_446_; 
v_val_445_ = lean_ctor_get(v_a_439_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v_a_439_, 1);
v___x_446_ = lean_array_push(v_b_432_, v_val_445_);
v_a_441_ = v___x_446_;
goto v___jp_440_;
}
v___jp_440_:
{
size_t v___x_442_; size_t v___x_443_; 
v___x_442_ = ((size_t)1ULL);
v___x_443_ = lean_usize_add(v_i_430_, v___x_442_);
v_i_430_ = v___x_443_;
v_b_432_ = v_a_441_;
goto _start;
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v_b_432_);
lean_dec_ref(v_p_428_);
v_a_447_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_438_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_438_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v___x_455_; 
lean_dec_ref(v_p_428_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v_b_432_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0___boxed(lean_object* v_p_456_, lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_stop_459_, lean_object* v_b_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
size_t v_i_boxed_464_; size_t v_stop_boxed_465_; lean_object* v_res_466_; 
v_i_boxed_464_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_stop_boxed_465_ = lean_unbox_usize(v_stop_459_);
lean_dec(v_stop_459_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_456_, v_as_457_, v_i_boxed_464_, v_stop_boxed_465_, v_b_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec_ref(v_as_457_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0___boxed(lean_object* v_p_467_, lean_object* v_as_468_, lean_object* v_start_469_, lean_object* v_stop_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_467_, v_as_468_, v_start_469_, v_stop_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v_stop_470_);
lean_dec(v_start_469_);
lean_dec_ref(v_as_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees___boxed(lean_object* v_p_475_, lean_object* v_t_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_475_, v_t_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2(lean_object* v_data_481_, lean_object* v_msg_482_, lean_object* v_a_483_, lean_object* v_wrap_484_, lean_object* v_children_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_486_, 0, v_data_481_);
lean_ctor_set(v___x_486_, 1, v_msg_482_);
lean_ctor_set(v___x_486_, 2, v_children_485_);
v___x_487_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_487_, 0, v_a_483_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_apply_1(v_wrap_484_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(lean_object* v_wrap_492_, lean_object* v_a_493_){
_start:
{
switch(lean_obj_tag(v_a_493_))
{
case 3:
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v___f_496_; 
v_a_494_ = lean_ctor_get(v_a_493_, 0);
lean_inc_ref(v_a_494_);
v_a_495_ = lean_ctor_get(v_a_493_, 1);
lean_inc_ref(v_a_495_);
lean_dec_ref_known(v_a_493_, 2);
v___f_496_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0), 3, 2);
lean_closure_set(v___f_496_, 0, v_a_494_);
lean_closure_set(v___f_496_, 1, v_wrap_492_);
v_wrap_492_ = v___f_496_;
v_a_493_ = v_a_495_;
goto _start;
}
case 4:
{
lean_object* v_a_498_; lean_object* v_a_499_; lean_object* v___f_500_; 
v_a_498_ = lean_ctor_get(v_a_493_, 0);
lean_inc_ref(v_a_498_);
v_a_499_ = lean_ctor_get(v_a_493_, 1);
lean_inc_ref(v_a_499_);
lean_dec_ref_known(v_a_493_, 2);
v___f_500_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1), 3, 2);
lean_closure_set(v___f_500_, 0, v_a_498_);
lean_closure_set(v___f_500_, 1, v_wrap_492_);
v_wrap_492_ = v___f_500_;
v_a_493_ = v_a_499_;
goto _start;
}
case 8:
{
lean_object* v_a_502_; 
v_a_502_ = lean_ctor_get(v_a_493_, 1);
lean_inc_ref(v_a_502_);
if (lean_obj_tag(v_a_502_) == 9)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_518_; 
v_a_503_ = lean_ctor_get(v_a_493_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_a_493_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_a_493_, 1);
lean_dec(v_unused_519_);
v___x_505_ = v_a_493_;
v_isShared_506_ = v_isSharedCheck_518_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v_a_493_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_518_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_data_507_; lean_object* v_msg_508_; lean_object* v_children_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_data_507_ = lean_ctor_get(v_a_502_, 0);
lean_inc_ref(v_data_507_);
v_msg_508_ = lean_ctor_get(v_a_502_, 1);
lean_inc_ref(v_msg_508_);
v_children_509_ = lean_ctor_get(v_a_502_, 2);
lean_inc_ref(v_children_509_);
lean_dec_ref_known(v_a_502_, 3);
v___x_510_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__1));
v___x_511_ = lean_name_eq(v_a_503_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
lean_dec_ref(v_children_509_);
lean_dec_ref(v_msg_508_);
lean_dec_ref(v_data_507_);
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec_ref(v_wrap_492_);
v___x_512_ = lean_box(0);
return v___x_512_;
}
else
{
lean_object* v___f_513_; lean_object* v___x_515_; 
v___f_513_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2), 5, 4);
lean_closure_set(v___f_513_, 0, v_data_507_);
lean_closure_set(v___f_513_, 1, v_msg_508_);
lean_closure_set(v___f_513_, 2, v_a_503_);
lean_closure_set(v___f_513_, 3, v_wrap_492_);
if (v_isShared_506_ == 0)
{
lean_ctor_set_tag(v___x_505_, 0);
lean_ctor_set(v___x_505_, 1, v_children_509_);
lean_ctor_set(v___x_505_, 0, v___f_513_);
v___x_515_ = v___x_505_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___f_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_children_509_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
}
else
{
lean_object* v___x_520_; 
lean_dec_ref_known(v_a_493_, 2);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_wrap_492_);
v___x_520_ = lean_box(0);
return v___x_520_;
}
}
default: 
{
lean_object* v___x_521_; 
lean_dec_ref(v_a_493_);
lean_dec_ref(v_wrap_492_);
v___x_521_ = lean_box(0);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_traceContainer_x3f(lean_object* v_data_522_){
_start:
{
lean_object* v___f_523_; lean_object* v___x_524_; 
v___f_523_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0));
v___x_524_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(v___f_523_, v_data_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(size_t v_sz_525_, size_t v_i_526_, lean_object* v_bs_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_lt(v_i_526_, v_sz_525_);
if (v___x_528_ == 0)
{
return v_bs_527_;
}
else
{
lean_object* v_v_529_; lean_object* v___x_530_; lean_object* v_bs_x27_531_; lean_object* v___x_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v_v_529_ = lean_array_uget(v_bs_527_, v_i_526_);
v___x_530_ = lean_unsigned_to_nat(0u);
v_bs_x27_531_ = lean_array_uset(v_bs_527_, v_i_526_, v___x_530_);
v___x_532_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData(v_v_529_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_add(v_i_526_, v___x_533_);
v___x_535_ = lean_array_uset(v_bs_x27_531_, v_i_526_, v___x_532_);
v_i_526_ = v___x_534_;
v_bs_527_ = v___x_535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0___boxed(lean_object* v_sz_537_, lean_object* v_i_538_, lean_object* v_bs_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_537_);
lean_dec(v_sz_537_);
v_i_boxed_541_ = lean_unbox_usize(v_i_538_);
lean_dec(v_i_538_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_boxed_540_, v_i_boxed_541_, v_bs_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage(lean_object* v_post_543_, lean_object* v_msg_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_fileName_548_; lean_object* v_pos_549_; lean_object* v_endPos_550_; uint8_t v_keepFullRange_551_; uint8_t v_severity_552_; uint8_t v_isSilent_553_; lean_object* v_caption_554_; lean_object* v_data_555_; lean_object* v___x_556_; 
v_fileName_548_ = lean_ctor_get(v_msg_544_, 0);
v_pos_549_ = lean_ctor_get(v_msg_544_, 1);
v_endPos_550_ = lean_ctor_get(v_msg_544_, 2);
v_keepFullRange_551_ = lean_ctor_get_uint8(v_msg_544_, sizeof(void*)*5);
v_severity_552_ = lean_ctor_get_uint8(v_msg_544_, sizeof(void*)*5 + 1);
v_isSilent_553_ = lean_ctor_get_uint8(v_msg_544_, sizeof(void*)*5 + 2);
v_caption_554_ = lean_ctor_get(v_msg_544_, 3);
v_data_555_ = lean_ctor_get(v_msg_544_, 4);
lean_inc(v_data_555_);
v___x_556_ = l_Lean_Elab_PostprocessTraces_traceContainer_x3f(v_data_555_);
if (lean_obj_tag(v___x_556_) == 1)
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_603_; 
lean_inc_ref(v_caption_554_);
lean_inc(v_endPos_550_);
lean_inc_ref(v_pos_549_);
lean_inc_ref(v_fileName_548_);
v_isSharedCheck_603_ = !lean_is_exclusive(v_msg_544_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; lean_object* v_unused_605_; lean_object* v_unused_606_; lean_object* v_unused_607_; lean_object* v_unused_608_; 
v_unused_604_ = lean_ctor_get(v_msg_544_, 4);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_msg_544_, 3);
lean_dec(v_unused_605_);
v_unused_606_ = lean_ctor_get(v_msg_544_, 2);
lean_dec(v_unused_606_);
v_unused_607_ = lean_ctor_get(v_msg_544_, 1);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_msg_544_, 0);
lean_dec(v_unused_608_);
v___x_558_ = v_msg_544_;
v_isShared_559_ = v_isSharedCheck_603_;
goto v_resetjp_557_;
}
else
{
lean_dec(v_msg_544_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_603_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_602_; 
v_val_560_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_602_ == 0)
{
v___x_562_ = v___x_556_;
v_isShared_563_ = v_isSharedCheck_602_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v___x_556_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_602_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_fst_564_; lean_object* v_snd_565_; size_t v_sz_566_; size_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_fst_564_ = lean_ctor_get(v_val_560_, 0);
lean_inc(v_fst_564_);
v_snd_565_ = lean_ctor_get(v_val_560_, 1);
lean_inc(v_snd_565_);
lean_dec(v_val_560_);
v_sz_566_ = lean_array_size(v_snd_565_);
v___x_567_ = ((size_t)0ULL);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_566_, v___x_567_, v_snd_565_);
lean_inc(v_a_546_);
lean_inc_ref(v_a_545_);
v___x_569_ = lean_apply_4(v_post_543_, v___x_568_, v_a_545_, v_a_546_, lean_box(0));
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_593_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_593_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_593_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_593_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_array_get_size(v_a_570_);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_nat_dec_eq(v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
size_t v_sz_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v_sz_577_ = lean_array_size(v_a_570_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_577_, v___x_567_, v_a_570_);
v___x_579_ = lean_apply_1(v_fst_564_, v___x_578_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 4, v___x_579_);
v___x_581_ = v___x_558_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fileName_548_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_pos_549_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_endPos_550_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_caption_554_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v___x_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*5, v_keepFullRange_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*5 + 1, v_severity_552_);
lean_ctor_set_uint8(v_reuseFailAlloc_588_, sizeof(void*)*5 + 2, v_isSilent_553_);
v___x_581_ = v_reuseFailAlloc_588_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_581_);
v___x_583_ = v___x_562_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_587_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_583_);
v___x_585_ = v___x_572_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_591_; 
lean_dec(v_a_570_);
lean_dec(v_fst_564_);
lean_del_object(v___x_562_);
lean_del_object(v___x_558_);
lean_dec_ref(v_caption_554_);
lean_dec(v_endPos_550_);
lean_dec_ref(v_pos_549_);
lean_dec_ref(v_fileName_548_);
v___x_589_ = lean_box(0);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_589_);
v___x_591_ = v___x_572_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_fst_564_);
lean_del_object(v___x_562_);
lean_del_object(v___x_558_);
lean_dec_ref(v_caption_554_);
lean_dec(v_endPos_550_);
lean_dec_ref(v_pos_549_);
lean_dec_ref(v_fileName_548_);
v_a_594_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_569_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_569_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v___x_556_);
lean_dec_ref(v_post_543_);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v_msg_544_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed(lean_object* v_post_611_, lean_object* v_msg_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Elab_PostprocessTraces_postprocessMessage(v_post_611_, v_msg_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(lean_object* v_a_617_, lean_object* v_messages_618_, lean_object* v_trees_619_, lean_object* v_a_x3f_620_){
_start:
{
lean_object* v___x_622_; lean_object* v_infoState_623_; lean_object* v_env_624_; lean_object* v_messages_625_; lean_object* v_scopes_626_; lean_object* v_usedQuotCtxts_627_; lean_object* v_nextMacroScope_628_; lean_object* v_maxRecDepth_629_; lean_object* v_ngen_630_; lean_object* v_auxDeclNGen_631_; lean_object* v_traceState_632_; lean_object* v_snapshotTasks_633_; lean_object* v_prevLinterStates_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_657_; 
v___x_622_ = lean_st_ref_take(v_a_617_);
v_infoState_623_ = lean_ctor_get(v___x_622_, 8);
v_env_624_ = lean_ctor_get(v___x_622_, 0);
v_messages_625_ = lean_ctor_get(v___x_622_, 1);
v_scopes_626_ = lean_ctor_get(v___x_622_, 2);
v_usedQuotCtxts_627_ = lean_ctor_get(v___x_622_, 3);
v_nextMacroScope_628_ = lean_ctor_get(v___x_622_, 4);
v_maxRecDepth_629_ = lean_ctor_get(v___x_622_, 5);
v_ngen_630_ = lean_ctor_get(v___x_622_, 6);
v_auxDeclNGen_631_ = lean_ctor_get(v___x_622_, 7);
v_traceState_632_ = lean_ctor_get(v___x_622_, 9);
v_snapshotTasks_633_ = lean_ctor_get(v___x_622_, 10);
v_prevLinterStates_634_ = lean_ctor_get(v___x_622_, 11);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_657_ == 0)
{
v___x_636_ = v___x_622_;
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_prevLinterStates_634_);
lean_inc(v_snapshotTasks_633_);
lean_inc(v_traceState_632_);
lean_inc(v_infoState_623_);
lean_inc(v_auxDeclNGen_631_);
lean_inc(v_ngen_630_);
lean_inc(v_maxRecDepth_629_);
lean_inc(v_nextMacroScope_628_);
lean_inc(v_usedQuotCtxts_627_);
lean_inc(v_scopes_626_);
lean_inc(v_messages_625_);
lean_inc(v_env_624_);
lean_dec(v___x_622_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
uint8_t v_enabled_638_; lean_object* v_assignment_639_; lean_object* v_lazyAssignment_640_; lean_object* v_trees_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_656_; 
v_enabled_638_ = lean_ctor_get_uint8(v_infoState_623_, sizeof(void*)*3);
v_assignment_639_ = lean_ctor_get(v_infoState_623_, 0);
v_lazyAssignment_640_ = lean_ctor_get(v_infoState_623_, 1);
v_trees_641_ = lean_ctor_get(v_infoState_623_, 2);
v_isSharedCheck_656_ = !lean_is_exclusive(v_infoState_623_);
if (v_isSharedCheck_656_ == 0)
{
v___x_643_ = v_infoState_623_;
v_isShared_644_ = v_isSharedCheck_656_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_trees_641_);
lean_inc(v_lazyAssignment_640_);
lean_inc(v_assignment_639_);
lean_dec(v_infoState_623_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_656_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_645_ = l_Lean_MessageLog_append(v_messages_618_, v_messages_625_);
v___x_646_ = l_Lean_PersistentArray_append___redArg(v_trees_619_, v_trees_641_);
lean_dec_ref(v_trees_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 2, v___x_646_);
v___x_648_ = v___x_643_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_assignment_639_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_lazyAssignment_640_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v___x_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*3, v_enabled_638_);
v___x_648_ = v_reuseFailAlloc_655_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 8, v___x_648_);
lean_ctor_set(v___x_636_, 1, v___x_645_);
v___x_650_ = v___x_636_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_env_624_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_scopes_626_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_usedQuotCtxts_627_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v_nextMacroScope_628_);
lean_ctor_set(v_reuseFailAlloc_654_, 5, v_maxRecDepth_629_);
lean_ctor_set(v_reuseFailAlloc_654_, 6, v_ngen_630_);
lean_ctor_set(v_reuseFailAlloc_654_, 7, v_auxDeclNGen_631_);
lean_ctor_set(v_reuseFailAlloc_654_, 8, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_654_, 9, v_traceState_632_);
lean_ctor_set(v_reuseFailAlloc_654_, 10, v_snapshotTasks_633_);
lean_ctor_set(v_reuseFailAlloc_654_, 11, v_prevLinterStates_634_);
v___x_650_ = v_reuseFailAlloc_654_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_st_ref_set(v_a_617_, v___x_650_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0___boxed(lean_object* v_a_658_, lean_object* v_messages_659_, lean_object* v_trees_660_, lean_object* v_a_x3f_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_658_, v_messages_659_, v_trees_660_, v_a_x3f_661_);
lean_dec(v_a_x3f_661_);
lean_dec(v_a_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(lean_object* v_as_664_, size_t v_i_665_, size_t v_stop_666_, lean_object* v_b_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = lean_usize_dec_eq(v_i_665_, v_stop_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v_diagnostics_670_; lean_object* v_msgLog_671_; lean_object* v___x_672_; size_t v___x_673_; size_t v___x_674_; 
v___x_669_ = lean_array_uget_borrowed(v_as_664_, v_i_665_);
v_diagnostics_670_ = lean_ctor_get(v___x_669_, 1);
v_msgLog_671_ = lean_ctor_get(v_diagnostics_670_, 0);
lean_inc_ref(v_msgLog_671_);
v___x_672_ = l_Lean_MessageLog_append(v_b_667_, v_msgLog_671_);
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_665_, v___x_673_);
v_i_665_ = v___x_674_;
v_b_667_ = v___x_672_;
goto _start;
}
else
{
return v_b_667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0___boxed(lean_object* v_as_676_, lean_object* v_i_677_, lean_object* v_stop_678_, lean_object* v_b_679_){
_start:
{
size_t v_i_boxed_680_; size_t v_stop_boxed_681_; lean_object* v_res_682_; 
v_i_boxed_680_ = lean_unbox_usize(v_i_677_);
lean_dec(v_i_677_);
v_stop_boxed_681_ = lean_unbox_usize(v_stop_678_);
lean_dec(v_stop_678_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v_as_676_, v_i_boxed_680_, v_stop_boxed_681_, v_b_679_);
lean_dec_ref(v_as_676_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(lean_object* v_as_683_, size_t v_i_684_, size_t v_stop_685_, lean_object* v_b_686_){
_start:
{
lean_object* v___y_688_; uint8_t v___x_692_; 
v___x_692_ = lean_usize_dec_eq(v_i_684_, v_stop_685_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_693_ = lean_array_uget_borrowed(v_as_683_, v_i_684_);
v___x_694_ = l_Lean_MessageLog_empty;
lean_inc(v___x_693_);
v___x_695_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_693_);
v___x_696_ = l_Lean_Language_SnapshotTree_getAll(v___x_695_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_array_get_size(v___x_696_);
v___x_699_ = lean_nat_dec_lt(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec_ref(v___x_696_);
v___x_700_ = l_Lean_MessageLog_append(v_b_686_, v___x_694_);
v___y_688_ = v___x_700_;
goto v___jp_687_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = lean_nat_dec_le(v___x_698_, v___x_698_);
if (v___x_701_ == 0)
{
if (v___x_699_ == 0)
{
lean_object* v___x_702_; 
lean_dec_ref(v___x_696_);
v___x_702_ = l_Lean_MessageLog_append(v_b_686_, v___x_694_);
v___y_688_ = v___x_702_;
goto v___jp_687_;
}
else
{
size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = ((size_t)0ULL);
v___x_704_ = lean_usize_of_nat(v___x_698_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v___x_696_, v___x_703_, v___x_704_, v___x_694_);
lean_dec_ref(v___x_696_);
v___x_706_ = l_Lean_MessageLog_append(v_b_686_, v___x_705_);
v___y_688_ = v___x_706_;
goto v___jp_687_;
}
}
else
{
size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_707_ = ((size_t)0ULL);
v___x_708_ = lean_usize_of_nat(v___x_698_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v___x_696_, v___x_707_, v___x_708_, v___x_694_);
lean_dec_ref(v___x_696_);
v___x_710_ = l_Lean_MessageLog_append(v_b_686_, v___x_709_);
v___y_688_ = v___x_710_;
goto v___jp_687_;
}
}
}
else
{
return v_b_686_;
}
v___jp_687_:
{
size_t v___x_689_; size_t v___x_690_; 
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_i_684_, v___x_689_);
v_i_684_ = v___x_690_;
v_b_686_ = v___y_688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1___boxed(lean_object* v_as_711_, lean_object* v_i_712_, lean_object* v_stop_713_, lean_object* v_b_714_){
_start:
{
size_t v_i_boxed_715_; size_t v_stop_boxed_716_; lean_object* v_res_717_; 
v_i_boxed_715_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_stop_boxed_716_ = lean_unbox_usize(v_stop_713_);
lean_dec(v_stop_713_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_as_711_, v_i_boxed_715_, v_stop_boxed_716_, v_b_714_);
lean_dec_ref(v_as_711_);
return v_res_717_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(32u);
v___x_719_ = lean_mk_empty_array_with_capacity(v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1(void){
_start:
{
size_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_721_ = ((size_t)5ULL);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_unsigned_to_nat(32u);
v___x_724_ = lean_mk_empty_array_with_capacity(v___x_723_);
v___x_725_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0);
v___x_726_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
lean_ctor_set(v___x_726_, 2, v___x_722_);
lean_ctor_set(v___x_726_, 3, v___x_722_);
lean_ctor_set_usize(v___x_726_, 4, v___x_721_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = l_Lean_NameSet_empty;
v___x_728_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1);
v___x_729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
lean_ctor_set(v___x_729_, 2, v___x_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object* v_cmd_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_env_739_; lean_object* v_scopes_740_; lean_object* v_usedQuotCtxts_741_; lean_object* v_nextMacroScope_742_; lean_object* v_maxRecDepth_743_; lean_object* v_ngen_744_; lean_object* v_auxDeclNGen_745_; lean_object* v_infoState_746_; lean_object* v_traceState_747_; lean_object* v_snapshotTasks_748_; lean_object* v_prevLinterStates_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_843_; 
v___x_736_ = lean_st_ref_get(v_a_734_);
v___x_737_ = lean_st_ref_get(v_a_734_);
v___x_738_ = lean_st_ref_take(v_a_734_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
v_scopes_740_ = lean_ctor_get(v___x_738_, 2);
v_usedQuotCtxts_741_ = lean_ctor_get(v___x_738_, 3);
v_nextMacroScope_742_ = lean_ctor_get(v___x_738_, 4);
v_maxRecDepth_743_ = lean_ctor_get(v___x_738_, 5);
v_ngen_744_ = lean_ctor_get(v___x_738_, 6);
v_auxDeclNGen_745_ = lean_ctor_get(v___x_738_, 7);
v_infoState_746_ = lean_ctor_get(v___x_738_, 8);
v_traceState_747_ = lean_ctor_get(v___x_738_, 9);
v_snapshotTasks_748_ = lean_ctor_get(v___x_738_, 10);
v_prevLinterStates_749_ = lean_ctor_get(v___x_738_, 11);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v___x_738_, 1);
lean_dec(v_unused_844_);
v___x_751_ = v___x_738_;
v_isShared_752_ = v_isSharedCheck_843_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_prevLinterStates_749_);
lean_inc(v_snapshotTasks_748_);
lean_inc(v_traceState_747_);
lean_inc(v_infoState_746_);
lean_inc(v_auxDeclNGen_745_);
lean_inc(v_ngen_744_);
lean_inc(v_maxRecDepth_743_);
lean_inc(v_nextMacroScope_742_);
lean_inc(v_usedQuotCtxts_741_);
lean_inc(v_scopes_740_);
lean_inc(v_env_739_);
lean_dec(v___x_738_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_843_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v___x_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_env_739_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_scopes_740_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_usedQuotCtxts_741_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_nextMacroScope_742_);
lean_ctor_set(v_reuseFailAlloc_842_, 5, v_maxRecDepth_743_);
lean_ctor_set(v_reuseFailAlloc_842_, 6, v_ngen_744_);
lean_ctor_set(v_reuseFailAlloc_842_, 7, v_auxDeclNGen_745_);
lean_ctor_set(v_reuseFailAlloc_842_, 8, v_infoState_746_);
lean_ctor_set(v_reuseFailAlloc_842_, 9, v_traceState_747_);
lean_ctor_set(v_reuseFailAlloc_842_, 10, v_snapshotTasks_748_);
lean_ctor_set(v_reuseFailAlloc_842_, 11, v_prevLinterStates_749_);
v___x_756_ = v_reuseFailAlloc_842_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v_infoState_758_; lean_object* v_messages_759_; lean_object* v_trees_760_; lean_object* v_fileName_761_; lean_object* v_fileMap_762_; lean_object* v_currRecDepth_763_; lean_object* v_cmdPos_764_; lean_object* v_macroStack_765_; lean_object* v_quotContext_x3f_766_; lean_object* v_currMacroScope_767_; lean_object* v_ref_768_; lean_object* v_cancelTk_x3f_769_; uint8_t v_suppressElabErrors_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_757_ = lean_st_ref_set(v_a_734_, v___x_756_);
v_infoState_758_ = lean_ctor_get(v___x_737_, 8);
lean_inc_ref(v_infoState_758_);
lean_dec(v___x_737_);
v_messages_759_ = lean_ctor_get(v___x_736_, 1);
lean_inc_ref(v_messages_759_);
lean_dec(v___x_736_);
v_trees_760_ = lean_ctor_get(v_infoState_758_, 2);
lean_inc_ref(v_trees_760_);
lean_dec_ref(v_infoState_758_);
v_fileName_761_ = lean_ctor_get(v_a_733_, 0);
v_fileMap_762_ = lean_ctor_get(v_a_733_, 1);
v_currRecDepth_763_ = lean_ctor_get(v_a_733_, 2);
v_cmdPos_764_ = lean_ctor_get(v_a_733_, 3);
v_macroStack_765_ = lean_ctor_get(v_a_733_, 4);
v_quotContext_x3f_766_ = lean_ctor_get(v_a_733_, 5);
v_currMacroScope_767_ = lean_ctor_get(v_a_733_, 6);
v_ref_768_ = lean_ctor_get(v_a_733_, 7);
v_cancelTk_x3f_769_ = lean_ctor_get(v_a_733_, 9);
v_suppressElabErrors_770_ = lean_ctor_get_uint8(v_a_733_, sizeof(void*)*10);
v___x_771_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3));
v___x_772_ = lean_box(0);
lean_inc(v_cancelTk_x3f_769_);
lean_inc(v_ref_768_);
lean_inc(v_currMacroScope_767_);
lean_inc(v_quotContext_x3f_766_);
lean_inc(v_macroStack_765_);
lean_inc(v_cmdPos_764_);
lean_inc(v_currRecDepth_763_);
lean_inc_ref(v_fileMap_762_);
lean_inc_ref(v_fileName_761_);
v___x_773_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_773_, 0, v_fileName_761_);
lean_ctor_set(v___x_773_, 1, v_fileMap_762_);
lean_ctor_set(v___x_773_, 2, v_currRecDepth_763_);
lean_ctor_set(v___x_773_, 3, v_cmdPos_764_);
lean_ctor_set(v___x_773_, 4, v_macroStack_765_);
lean_ctor_set(v___x_773_, 5, v_quotContext_x3f_766_);
lean_ctor_set(v___x_773_, 6, v_currMacroScope_767_);
lean_ctor_set(v___x_773_, 7, v_ref_768_);
lean_ctor_set(v___x_773_, 8, v___x_772_);
lean_ctor_set(v___x_773_, 9, v_cancelTk_x3f_769_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*10, v_suppressElabErrors_770_);
v___x_774_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_732_, v___x_771_, v___x_773_, v_a_734_);
lean_dec_ref_known(v___x_773_, 10);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_830_; 
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_774_, 0);
lean_dec(v_unused_831_);
v___x_776_ = v___x_774_;
v_isShared_777_ = v_isSharedCheck_830_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_774_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_830_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_messages_780_; lean_object* v___y_782_; lean_object* v_snapshotTasks_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_778_ = lean_st_ref_get(v_a_734_);
v___x_779_ = lean_st_ref_get(v_a_734_);
v_messages_780_ = lean_ctor_get(v___x_778_, 1);
lean_inc_ref(v_messages_780_);
lean_dec(v___x_778_);
v_snapshotTasks_819_ = lean_ctor_get(v___x_779_, 10);
lean_inc_ref(v_snapshotTasks_819_);
lean_dec(v___x_779_);
v___x_820_ = l_Lean_MessageLog_empty;
v___x_821_ = lean_array_get_size(v_snapshotTasks_819_);
v___x_822_ = lean_nat_dec_lt(v___x_753_, v___x_821_);
if (v___x_822_ == 0)
{
lean_dec_ref(v_snapshotTasks_819_);
v___y_782_ = v___x_820_;
goto v___jp_781_;
}
else
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_le(v___x_821_, v___x_821_);
if (v___x_823_ == 0)
{
if (v___x_822_ == 0)
{
lean_dec_ref(v_snapshotTasks_819_);
v___y_782_ = v___x_820_;
goto v___jp_781_;
}
else
{
size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((size_t)0ULL);
v___x_825_ = lean_usize_of_nat(v___x_821_);
v___x_826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_819_, v___x_824_, v___x_825_, v___x_820_);
lean_dec_ref(v_snapshotTasks_819_);
v___y_782_ = v___x_826_;
goto v___jp_781_;
}
}
else
{
size_t v___x_827_; size_t v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((size_t)0ULL);
v___x_828_ = lean_usize_of_nat(v___x_821_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_819_, v___x_827_, v___x_828_, v___x_820_);
lean_dec_ref(v_snapshotTasks_819_);
v___y_782_ = v___x_829_;
goto v___jp_781_;
}
}
v___jp_781_:
{
lean_object* v___x_783_; lean_object* v_env_784_; lean_object* v_scopes_785_; lean_object* v_usedQuotCtxts_786_; lean_object* v_nextMacroScope_787_; lean_object* v_maxRecDepth_788_; lean_object* v_ngen_789_; lean_object* v_auxDeclNGen_790_; lean_object* v_infoState_791_; lean_object* v_traceState_792_; lean_object* v_prevLinterStates_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_816_; 
v___x_783_ = lean_st_ref_take(v_a_734_);
v_env_784_ = lean_ctor_get(v___x_783_, 0);
v_scopes_785_ = lean_ctor_get(v___x_783_, 2);
v_usedQuotCtxts_786_ = lean_ctor_get(v___x_783_, 3);
v_nextMacroScope_787_ = lean_ctor_get(v___x_783_, 4);
v_maxRecDepth_788_ = lean_ctor_get(v___x_783_, 5);
v_ngen_789_ = lean_ctor_get(v___x_783_, 6);
v_auxDeclNGen_790_ = lean_ctor_get(v___x_783_, 7);
v_infoState_791_ = lean_ctor_get(v___x_783_, 8);
v_traceState_792_ = lean_ctor_get(v___x_783_, 9);
v_prevLinterStates_793_ = lean_ctor_get(v___x_783_, 11);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_817_ = lean_ctor_get(v___x_783_, 10);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v___x_783_, 1);
lean_dec(v_unused_818_);
v___x_795_ = v___x_783_;
v_isShared_796_ = v_isSharedCheck_816_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_prevLinterStates_793_);
lean_inc(v_traceState_792_);
lean_inc(v_infoState_791_);
lean_inc(v_auxDeclNGen_790_);
lean_inc(v_ngen_789_);
lean_inc(v_maxRecDepth_788_);
lean_inc(v_nextMacroScope_787_);
lean_inc(v_usedQuotCtxts_786_);
lean_inc(v_scopes_785_);
lean_inc(v_env_784_);
lean_dec(v___x_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_816_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 10, v___x_771_);
lean_ctor_set(v___x_795_, 1, v___x_754_);
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_env_784_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_scopes_785_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_usedQuotCtxts_786_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_nextMacroScope_787_);
lean_ctor_set(v_reuseFailAlloc_815_, 5, v_maxRecDepth_788_);
lean_ctor_set(v_reuseFailAlloc_815_, 6, v_ngen_789_);
lean_ctor_set(v_reuseFailAlloc_815_, 7, v_auxDeclNGen_790_);
lean_ctor_set(v_reuseFailAlloc_815_, 8, v_infoState_791_);
lean_ctor_set(v_reuseFailAlloc_815_, 9, v_traceState_792_);
lean_ctor_set(v_reuseFailAlloc_815_, 10, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_815_, 11, v_prevLinterStates_793_);
v___x_798_ = v_reuseFailAlloc_815_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_799_ = lean_st_ref_set(v_a_734_, v___x_798_);
v___x_800_ = l_Lean_MessageLog_append(v_messages_780_, v___y_782_);
v___x_801_ = l_Lean_MessageLog_toArray(v___x_800_);
lean_dec_ref(v___x_800_);
lean_inc_ref(v___x_801_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_801_);
v___x_803_ = v___x_776_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_814_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_734_, v_messages_759_, v_trees_760_, v___x_804_);
lean_dec_ref_known(v___x_804_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v___x_805_, 0);
lean_dec(v_unused_813_);
v___x_807_ = v___x_805_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_dec(v___x_805_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_801_);
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_801_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
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
lean_object* v_a_832_; lean_object* v___x_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_a_832_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_774_, 1);
v___x_833_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_734_, v_messages_759_, v_trees_760_, v___x_772_);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_833_, 0);
lean_dec(v_unused_841_);
v___x_835_ = v___x_833_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_dec(v___x_833_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 1);
lean_ctor_set(v___x_835_, 0, v_a_832_);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_832_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___boxed(lean_object* v_cmd_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v_cmd_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(lean_object* v_type_850_, lean_object* v_e_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
uint8_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = 1;
v___x_858_ = 1;
v___x_859_ = l_Lean_Meta_evalExpr___redArg(v_type_850_, v_e_851_, v___x_857_, v___x_858_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1___boxed(lean_object* v_type_860_, lean_object* v_e_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(v_type_860_, v_e_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(lean_object* v_e_868_, lean_object* v___y_869_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = l_Lean_Expr_hasMVar(v_e_868_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_e_868_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v_mctx_874_; lean_object* v___x_875_; lean_object* v_fst_876_; lean_object* v_snd_877_; lean_object* v___x_878_; lean_object* v_cache_879_; lean_object* v_zetaDeltaFVarIds_880_; lean_object* v_postponed_881_; lean_object* v_diag_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_891_; 
v___x_873_ = lean_st_ref_get(v___y_869_);
v_mctx_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc_ref(v_mctx_874_);
lean_dec(v___x_873_);
v___x_875_ = l_Lean_instantiateMVarsCore(v_mctx_874_, v_e_868_);
v_fst_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_fst_876_);
v_snd_877_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_snd_877_);
lean_dec_ref(v___x_875_);
v___x_878_ = lean_st_ref_take(v___y_869_);
v_cache_879_ = lean_ctor_get(v___x_878_, 1);
v_zetaDeltaFVarIds_880_ = lean_ctor_get(v___x_878_, 2);
v_postponed_881_ = lean_ctor_get(v___x_878_, 3);
v_diag_882_ = lean_ctor_get(v___x_878_, 4);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; 
v_unused_892_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_892_);
v___x_884_ = v___x_878_;
v_isShared_885_ = v_isSharedCheck_891_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_diag_882_);
lean_inc(v_postponed_881_);
lean_inc(v_zetaDeltaFVarIds_880_);
lean_inc(v_cache_879_);
lean_dec(v___x_878_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_891_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v_snd_877_);
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_snd_877_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_cache_879_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_zetaDeltaFVarIds_880_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v_postponed_881_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v_diag_882_);
v___x_887_ = v_reuseFailAlloc_890_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_st_ref_set(v___y_869_, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v_fst_876_);
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg___boxed(lean_object* v_e_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_893_, v___y_894_);
lean_dec(v___y_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(lean_object* v_e_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_897_, v___y_901_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___boxed(lean_object* v_e_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(v_e_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_914_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_box(0);
v___x_916_ = l_Lean_Elab_abortTermExceptionId;
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg(){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___boxed(lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(lean_object* v_00_u03b1_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___boxed(lean_object* v_00_u03b1_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(v_00_u03b1_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(lean_object* v___x_941_, lean_object* v___x_942_, uint8_t v___x_943_, lean_object* v___x_944_, uint8_t v___x_945_, lean_object* v___x_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_941_, v___x_942_, v___x_943_, v___x_943_, v___x_944_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_945_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; uint8_t v___x_999_; 
lean_dec_ref_known(v___x_956_, 1);
v___x_957_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_a_955_, v___y_950_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
v___x_999_ = l_Lean_Expr_hasSyntheticSorry(v_a_958_);
if (v___x_999_ == 0)
{
v___y_960_ = v___y_947_;
v___y_961_ = v___y_948_;
v___y_962_ = v___y_949_;
v___y_963_ = v___y_950_;
v___y_964_ = v___y_951_;
v___y_965_ = v___y_952_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1000_; lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_a_958_);
lean_dec_ref(v___x_946_);
v___x_1000_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
v___jp_959_:
{
lean_object* v___x_966_; 
lean_inc(v_a_958_);
v___x_966_ = l_Lean_Meta_getMVars(v_a_958_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_box(0);
v___x_969_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_967_, v___x_968_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v_a_967_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; uint8_t v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = lean_unbox(v_a_970_);
lean_dec(v_a_970_);
if (v___x_971_ == 0)
{
uint8_t v___x_972_; lean_object* v___x_973_; 
v___x_972_ = 1;
v___x_973_ = l_Lean_Meta_evalExpr___redArg(v___x_946_, v_a_958_, v___x_972_, v___x_943_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_958_);
lean_dec_ref(v___x_946_);
v___x_974_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_a_958_);
lean_dec_ref(v___x_946_);
v_a_983_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_969_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_969_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_a_958_);
lean_dec_ref(v___x_946_);
v_a_991_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_966_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_966_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_a_955_);
lean_dec_ref(v___x_946_);
v_a_1009_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_956_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_956_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v___x_946_);
v_a_1017_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_954_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_954_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed(lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v___x_6069__boxed_1038_; uint8_t v___x_6071__boxed_1039_; lean_object* v_res_1040_; 
v___x_6069__boxed_1038_ = lean_unbox(v___x_1027_);
v___x_6071__boxed_1039_ = lean_unbox(v___x_1029_);
v_res_1040_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(v___x_1025_, v___x_1026_, v___x_6069__boxed_1038_, v___x_1028_, v___x_6071__boxed_1039_, v___x_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1040_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_1047_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
lean_ctor_set(v___x_1047_, 2, v___x_1046_);
lean_ctor_set(v___x_1047_, 3, v___x_1046_);
lean_ctor_set(v___x_1047_, 4, v___x_1046_);
lean_ctor_set(v___x_1047_, 5, v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(lean_object* v_env_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v_nextMacroScope_1053_; lean_object* v_ngen_1054_; lean_object* v_auxDeclNGen_1055_; lean_object* v_traceState_1056_; lean_object* v_messages_1057_; lean_object* v_infoState_1058_; lean_object* v_snapshotTasks_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1085_; 
v___x_1052_ = lean_st_ref_take(v___y_1050_);
v_nextMacroScope_1053_ = lean_ctor_get(v___x_1052_, 1);
v_ngen_1054_ = lean_ctor_get(v___x_1052_, 2);
v_auxDeclNGen_1055_ = lean_ctor_get(v___x_1052_, 3);
v_traceState_1056_ = lean_ctor_get(v___x_1052_, 4);
v_messages_1057_ = lean_ctor_get(v___x_1052_, 6);
v_infoState_1058_ = lean_ctor_get(v___x_1052_, 7);
v_snapshotTasks_1059_ = lean_ctor_get(v___x_1052_, 8);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; lean_object* v_unused_1087_; 
v_unused_1086_ = lean_ctor_get(v___x_1052_, 5);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v___x_1052_, 0);
lean_dec(v_unused_1087_);
v___x_1061_ = v___x_1052_;
v_isShared_1062_ = v_isSharedCheck_1085_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_snapshotTasks_1059_);
lean_inc(v_infoState_1058_);
lean_inc(v_messages_1057_);
lean_inc(v_traceState_1056_);
lean_inc(v_auxDeclNGen_1055_);
lean_inc(v_ngen_1054_);
lean_inc(v_nextMacroScope_1053_);
lean_dec(v___x_1052_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1085_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 5, v___x_1063_);
lean_ctor_set(v___x_1061_, 0, v_env_1048_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_env_1048_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_nextMacroScope_1053_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_ngen_1054_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v_auxDeclNGen_1055_);
lean_ctor_set(v_reuseFailAlloc_1084_, 4, v_traceState_1056_);
lean_ctor_set(v_reuseFailAlloc_1084_, 5, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1084_, 6, v_messages_1057_);
lean_ctor_set(v_reuseFailAlloc_1084_, 7, v_infoState_1058_);
lean_ctor_set(v_reuseFailAlloc_1084_, 8, v_snapshotTasks_1059_);
v___x_1065_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_mctx_1068_; lean_object* v_zetaDeltaFVarIds_1069_; lean_object* v_postponed_1070_; lean_object* v_diag_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1082_; 
v___x_1066_ = lean_st_ref_set(v___y_1050_, v___x_1065_);
v___x_1067_ = lean_st_ref_take(v___y_1049_);
v_mctx_1068_ = lean_ctor_get(v___x_1067_, 0);
v_zetaDeltaFVarIds_1069_ = lean_ctor_get(v___x_1067_, 2);
v_postponed_1070_ = lean_ctor_get(v___x_1067_, 3);
v_diag_1071_ = lean_ctor_get(v___x_1067_, 4);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_1067_, 1);
lean_dec(v_unused_1083_);
v___x_1073_ = v___x_1067_;
v_isShared_1074_ = v_isSharedCheck_1082_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_diag_1071_);
lean_inc(v_postponed_1070_);
lean_inc(v_zetaDeltaFVarIds_1069_);
lean_inc(v_mctx_1068_);
lean_dec(v___x_1067_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1082_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___x_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_mctx_1068_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_zetaDeltaFVarIds_1069_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_postponed_1070_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v_diag_1071_);
v___x_1077_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_st_ref_set(v___y_1049_, v___x_1077_);
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___boxed(lean_object* v_env_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec(v___y_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(lean_object* v_env_1093_, lean_object* v_x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v_env_1103_; lean_object* v_a_1105_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1102_ = lean_st_ref_get(v___y_1100_);
v_env_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1102_);
v___x_1115_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1093_, v___y_1098_, v___y_1100_);
lean_dec_ref(v___x_1115_);
lean_inc(v___y_1100_);
lean_inc_ref(v___y_1099_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1097_);
lean_inc(v___y_1096_);
lean_inc_ref(v___y_1095_);
v___x_1116_ = lean_apply_7(v_x_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, lean_box(0));
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1103_, v___y_1098_, v___y_1100_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1126_);
v___x_1120_ = v___x_1118_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v___x_1118_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v_a_1117_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1117_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1127_; 
v_a_1127_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1116_, 1);
v_a_1105_ = v_a_1127_;
goto v___jp_1104_;
}
v___jp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v___x_1106_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1103_, v___y_1098_, v___y_1100_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v___x_1106_, 0);
lean_dec(v_unused_1114_);
v___x_1108_ = v___x_1106_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_dec(v___x_1106_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 1);
lean_ctor_set(v___x_1108_, 0, v_a_1105_);
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1105_);
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
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg___boxed(lean_object* v_env_1128_, lean_object* v_x_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1128_, v_x_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1137_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10));
v___x_1159_ = l_String_toRawSubstring_x27(v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24));
v___x_1188_ = l_String_toRawSubstring_x27(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34));
v___x_1211_ = l_String_toRawSubstring_x27(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37));
v___x_1227_ = l_Lean_mkConst(v___x_1226_, v___x_1225_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(lean_object* v_post_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_ref_1238_; lean_object* v_quotContext_1239_; lean_object* v_currMacroScope_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_env_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_ref_1238_ = lean_ctor_get(v_a_1235_, 5);
v_quotContext_1239_ = lean_ctor_get(v_a_1235_, 10);
v_currMacroScope_1240_ = lean_ctor_get(v_a_1235_, 11);
v___x_1241_ = 0;
v___x_1242_ = l_Lean_SourceInfo_fromRef(v_ref_1238_, v___x_1241_);
v___x_1243_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3));
v___x_1244_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4));
lean_inc_n(v___x_1242_, 14);
v___x_1245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1242_);
lean_ctor_set(v___x_1245_, 1, v___x_1243_);
v___x_1246_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7));
v___x_1247_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9));
v___x_1248_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11);
v___x_1249_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13));
lean_inc_n(v_currMacroScope_1240_, 3);
lean_inc_n(v_quotContext_1239_, 3);
v___x_1250_ = l_Lean_addMacroScope(v_quotContext_1239_, v___x_1249_, v_currMacroScope_1240_);
v___x_1251_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15));
v___x_1252_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1242_);
lean_ctor_set(v___x_1252_, 1, v___x_1248_);
lean_ctor_set(v___x_1252_, 2, v___x_1250_);
lean_ctor_set(v___x_1252_, 3, v___x_1251_);
v___x_1253_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1247_, v___x_1252_);
v___x_1254_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1246_, v___x_1253_);
v___x_1255_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16));
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1242_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18));
v___x_1258_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20));
v___x_1259_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21));
v___x_1260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1242_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23));
v___x_1262_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25);
v___x_1263_ = lean_box(0);
v___x_1264_ = l_Lean_addMacroScope(v_quotContext_1239_, v___x_1263_, v_currMacroScope_1240_);
v___x_1265_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32));
v___x_1266_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1242_);
lean_ctor_set(v___x_1266_, 1, v___x_1262_);
lean_ctor_set(v___x_1266_, 2, v___x_1264_);
lean_ctor_set(v___x_1266_, 3, v___x_1265_);
v___x_1267_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1261_, v___x_1266_);
v___x_1268_ = l_Lean_Syntax_node2(v___x_1242_, v___x_1258_, v___x_1260_, v___x_1267_);
v___x_1269_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33));
v___x_1270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1242_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35);
v___x_1272_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36));
v___x_1273_ = l_Lean_addMacroScope(v_quotContext_1239_, v___x_1272_, v_currMacroScope_1240_);
v___x_1274_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39));
v___x_1275_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1242_);
lean_ctor_set(v___x_1275_, 1, v___x_1271_);
lean_ctor_set(v___x_1275_, 2, v___x_1273_);
lean_ctor_set(v___x_1275_, 3, v___x_1274_);
v___x_1276_ = l_Lean_Syntax_node1(v___x_1242_, v___x_1247_, v___x_1275_);
v___x_1277_ = lean_st_ref_get(v_a_1236_);
v___x_1278_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40));
v___x_1279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1242_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v_env_1280_ = lean_ctor_get(v___x_1277_, 0);
lean_inc_ref(v_env_1280_);
lean_dec(v___x_1277_);
v___x_1281_ = l_Lean_Syntax_node5(v___x_1242_, v___x_1257_, v___x_1268_, v_post_1230_, v___x_1270_, v___x_1276_, v___x_1279_);
v___x_1282_ = l_Lean_Syntax_node4(v___x_1242_, v___x_1244_, v___x_1245_, v___x_1254_, v___x_1256_, v___x_1281_);
v___x_1283_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41);
v___x_1284_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42);
v___x_1285_ = 1;
v___x_1286_ = lean_box(0);
v___x_1287_ = lean_box(v___x_1285_);
v___x_1288_ = lean_box(v___x_1241_);
v___f_1289_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1289_, 0, v___x_1282_);
lean_closure_set(v___f_1289_, 1, v___x_1284_);
lean_closure_set(v___f_1289_, 2, v___x_1287_);
lean_closure_set(v___f_1289_, 3, v___x_1286_);
lean_closure_set(v___f_1289_, 4, v___x_1288_);
lean_closure_set(v___f_1289_, 5, v___x_1283_);
v___x_1290_ = l_Lean_Environment_unlockAsync(v_env_1280_);
v___x_1291_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v___x_1290_, v___f_1289_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___boxed(lean_object* v_post_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(lean_object* v_env_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1301_, v___y_1305_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___boxed(lean_object* v_env_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(v_env_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(lean_object* v_00_u03b1_1319_, lean_object* v_env_1320_, lean_object* v_x_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1320_, v_x_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_env_1331_, lean_object* v_x_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(v_00_u03b1_1330_, v_env_1331_, v_x_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(lean_object* v_post_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1341_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed(lean_object* v_post_1351_, lean_object* v_x_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(v_post_1351_, v_x_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec_ref(v_x_1352_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(lean_object* v_a_1361_, lean_object* v_traceState_1362_, lean_object* v_a_x3f_1363_){
_start:
{
lean_object* v___x_1365_; lean_object* v_env_1366_; lean_object* v_messages_1367_; lean_object* v_scopes_1368_; lean_object* v_usedQuotCtxts_1369_; lean_object* v_nextMacroScope_1370_; lean_object* v_maxRecDepth_1371_; lean_object* v_ngen_1372_; lean_object* v_auxDeclNGen_1373_; lean_object* v_infoState_1374_; lean_object* v_snapshotTasks_1375_; lean_object* v_prevLinterStates_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1386_; 
v___x_1365_ = lean_st_ref_take(v_a_1361_);
v_env_1366_ = lean_ctor_get(v___x_1365_, 0);
v_messages_1367_ = lean_ctor_get(v___x_1365_, 1);
v_scopes_1368_ = lean_ctor_get(v___x_1365_, 2);
v_usedQuotCtxts_1369_ = lean_ctor_get(v___x_1365_, 3);
v_nextMacroScope_1370_ = lean_ctor_get(v___x_1365_, 4);
v_maxRecDepth_1371_ = lean_ctor_get(v___x_1365_, 5);
v_ngen_1372_ = lean_ctor_get(v___x_1365_, 6);
v_auxDeclNGen_1373_ = lean_ctor_get(v___x_1365_, 7);
v_infoState_1374_ = lean_ctor_get(v___x_1365_, 8);
v_snapshotTasks_1375_ = lean_ctor_get(v___x_1365_, 10);
v_prevLinterStates_1376_ = lean_ctor_get(v___x_1365_, 11);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v___x_1365_, 9);
lean_dec(v_unused_1387_);
v___x_1378_ = v___x_1365_;
v_isShared_1379_ = v_isSharedCheck_1386_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_prevLinterStates_1376_);
lean_inc(v_snapshotTasks_1375_);
lean_inc(v_infoState_1374_);
lean_inc(v_auxDeclNGen_1373_);
lean_inc(v_ngen_1372_);
lean_inc(v_maxRecDepth_1371_);
lean_inc(v_nextMacroScope_1370_);
lean_inc(v_usedQuotCtxts_1369_);
lean_inc(v_scopes_1368_);
lean_inc(v_messages_1367_);
lean_inc(v_env_1366_);
lean_dec(v___x_1365_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1386_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 9, v_traceState_1362_);
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_env_1366_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_messages_1367_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_scopes_1368_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_usedQuotCtxts_1369_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_nextMacroScope_1370_);
lean_ctor_set(v_reuseFailAlloc_1385_, 5, v_maxRecDepth_1371_);
lean_ctor_set(v_reuseFailAlloc_1385_, 6, v_ngen_1372_);
lean_ctor_set(v_reuseFailAlloc_1385_, 7, v_auxDeclNGen_1373_);
lean_ctor_set(v_reuseFailAlloc_1385_, 8, v_infoState_1374_);
lean_ctor_set(v_reuseFailAlloc_1385_, 9, v_traceState_1362_);
lean_ctor_set(v_reuseFailAlloc_1385_, 10, v_snapshotTasks_1375_);
lean_ctor_set(v_reuseFailAlloc_1385_, 11, v_prevLinterStates_1376_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_st_ref_set(v_a_1361_, v___x_1381_);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1___boxed(lean_object* v_a_1388_, lean_object* v_traceState_1389_, lean_object* v_a_x3f_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1388_, v_traceState_1389_, v_a_x3f_1390_);
lean_dec(v_a_x3f_1390_);
lean_dec(v_a_1388_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(lean_object* v_a_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_apply_4(v_a_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed(lean_object* v_a_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(v_a_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object* v_post_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v_traceState_1410_; lean_object* v___f_1411_; lean_object* v_r_1412_; 
v___x_1409_ = lean_st_ref_get(v_a_1407_);
v_traceState_1410_ = lean_ctor_get(v___x_1409_, 9);
lean_inc_ref(v_traceState_1410_);
lean_dec(v___x_1409_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1411_, 0, v_post_1405_);
v_r_1412_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_1411_, v_a_1406_, v_a_1407_);
if (lean_obj_tag(v_r_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1430_; 
v_a_1413_ = lean_ctor_get(v_r_1412_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_r_1412_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1415_ = v_r_1412_;
v_isShared_1416_ = v_isSharedCheck_1430_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v_r_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1430_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
lean_inc(v_a_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 1);
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1427_; 
v___x_1419_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1407_, v_traceState_1410_, v___x_1418_);
lean_dec_ref(v___x_1418_);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v___x_1419_, 0);
lean_dec(v_unused_1428_);
v___x_1421_ = v___x_1419_;
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v___x_1419_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___f_1423_; lean_object* v___x_1425_; 
v___f_1423_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed), 5, 1);
lean_closure_set(v___f_1423_, 0, v_a_1413_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___f_1423_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___f_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1431_ = lean_ctor_get(v_r_1412_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v_r_1412_, 1);
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1407_, v_traceState_1410_, v___x_1432_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1441_);
v___x_1435_ = v___x_1433_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_dec(v___x_1433_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set_tag(v___x_1435_, 1);
lean_ctor_set(v___x_1435_, 0, v_a_1431_);
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1431_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___boxed(lean_object* v_post_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1446_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PostprocessTraces_instInhabitedTraceTree = _init_l_Lean_PostprocessTraces_instInhabitedTraceTree();
lean_mark_persistent(l_Lean_PostprocessTraces_instInhabitedTraceTree);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PostprocessTraces_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PostprocessTraces_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
