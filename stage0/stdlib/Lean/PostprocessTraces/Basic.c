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
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
double lean_float_maximum(double, double);
double lean_float_add(double, double);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toArray(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_PostprocessTraces_TraceTree_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_data_7_; lean_object* v_msg_8_; lean_object* v_children_9_; lean_object* v_wrap_10_; lean_object* v___x_11_; 
v_data_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_data_7_);
v_msg_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_msg_8_);
v_children_9_ = lean_ctor_get(v_t_5_, 2);
lean_inc_ref(v_children_9_);
v_wrap_10_ = lean_ctor_get(v_t_5_, 3);
lean_inc_ref(v_wrap_10_);
lean_dec_ref_known(v_t_5_, 4);
v___x_11_ = lean_apply_4(v_k_6_, v_data_7_, v_msg_8_, v_children_9_, v_wrap_10_);
return v___x_11_;
}
else
{
lean_object* v_msg_12_; lean_object* v___x_13_; 
v_msg_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_msg_12_);
lean_dec_ref_known(v_t_5_, 1);
v___x_13_ = lean_apply_1(v_k_6_, v_msg_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim(lean_object* v_motive__1_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ctorElim___boxed(lean_object* v_motive__1_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_PostprocessTraces_TraceTree_ctorElim(v_motive__1_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim___redArg(lean_object* v_t_26_, lean_object* v_node_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_26_, v_node_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_node_elim(lean_object* v_motive__1_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_node_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_30_, v_node_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim___redArg(lean_object* v_t_34_, lean_object* v_leaf_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_34_, v_leaf_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_leaf_elim(lean_object* v_motive__1_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_leaf_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_PostprocessTraces_TraceTree_ctorElim___redArg(v_t_38_, v_leaf_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = l_Lean_MessageData_nil;
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_instInhabitedTraceTree(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0, &l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0_once, _init_l_Lean_PostprocessTraces_instInhabitedTraceTree___closed__0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0(lean_object* v_a_45_, lean_object* v_wrap_46_, lean_object* v_m_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_48_, 0, v_a_45_);
lean_ctor_set(v___x_48_, 1, v_m_47_);
v___x_49_ = lean_apply_1(v_wrap_46_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1(lean_object* v_a_50_, lean_object* v_wrap_51_, lean_object* v_m_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_53_, 0, v_a_50_);
lean_ctor_set(v___x_53_, 1, v_m_52_);
v___x_54_ = lean_apply_1(v_wrap_51_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0(lean_object* v___y_55_){
_start:
{
lean_inc_ref(v___y_55_);
return v___y_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0___boxed(lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___lam__0(v___y_56_);
lean_dec_ref(v___y_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(lean_object* v_wrap_59_, lean_object* v_a_60_){
_start:
{
switch(lean_obj_tag(v_a_60_))
{
case 3:
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___f_63_; 
v_a_61_ = lean_ctor_get(v_a_60_, 0);
lean_inc_ref(v_a_61_);
v_a_62_ = lean_ctor_get(v_a_60_, 1);
lean_inc_ref(v_a_62_);
lean_dec_ref_known(v_a_60_, 2);
v___f_63_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0), 3, 2);
lean_closure_set(v___f_63_, 0, v_a_61_);
lean_closure_set(v___f_63_, 1, v_wrap_59_);
v_wrap_59_ = v___f_63_;
v_a_60_ = v_a_62_;
goto _start;
}
case 4:
{
lean_object* v_a_65_; lean_object* v_a_66_; lean_object* v___f_67_; 
v_a_65_ = lean_ctor_get(v_a_60_, 0);
lean_inc_ref(v_a_65_);
v_a_66_ = lean_ctor_get(v_a_60_, 1);
lean_inc_ref(v_a_66_);
lean_dec_ref_known(v_a_60_, 2);
v___f_67_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1), 3, 2);
lean_closure_set(v___f_67_, 0, v_a_65_);
lean_closure_set(v___f_67_, 1, v_wrap_59_);
v_wrap_59_ = v___f_67_;
v_a_60_ = v_a_66_;
goto _start;
}
case 9:
{
lean_object* v_data_69_; lean_object* v_msg_70_; lean_object* v_children_71_; size_t v_sz_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_data_69_ = lean_ctor_get(v_a_60_, 0);
lean_inc_ref(v_data_69_);
v_msg_70_ = lean_ctor_get(v_a_60_, 1);
lean_inc_ref(v_msg_70_);
v_children_71_ = lean_ctor_get(v_a_60_, 2);
lean_inc_ref(v_children_71_);
lean_dec_ref_known(v_a_60_, 3);
v_sz_72_ = lean_array_size(v_children_71_);
v___x_73_ = ((size_t)0ULL);
v___x_74_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(v_sz_72_, v___x_73_, v_children_71_);
v___x_75_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_75_, 0, v_data_69_);
lean_ctor_set(v___x_75_, 1, v_msg_70_);
lean_ctor_set(v___x_75_, 2, v___x_74_);
lean_ctor_set(v___x_75_, 3, v_wrap_59_);
return v___x_75_;
}
default: 
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_apply_1(v_wrap_59_, v_a_60_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(size_t v_sz_78_, size_t v_i_79_, lean_object* v_bs_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = lean_usize_dec_lt(v_i_79_, v_sz_78_);
if (v___x_81_ == 0)
{
return v_bs_80_;
}
else
{
lean_object* v___f_82_; lean_object* v_v_83_; lean_object* v___x_84_; lean_object* v_bs_x27_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___f_82_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___closed__0));
v_v_83_ = lean_array_uget(v_bs_80_, v_i_79_);
v___x_84_ = lean_unsigned_to_nat(0u);
v_bs_x27_85_ = lean_array_uset(v_bs_80_, v_i_79_, v___x_84_);
v___x_86_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(v___f_82_, v_v_83_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_add(v_i_79_, v___x_87_);
v___x_89_ = lean_array_uset(v_bs_x27_85_, v_i_79_, v___x_86_);
v_i_79_ = v___x_88_;
v_bs_80_ = v___x_89_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_78_ = stack[0].m_num;
size_t v_i_79_ = stack[1].m_num;
lean_object* v_bs_80_ = stack[2].m_obj;
lean_object* v_res_91_;
v_res_91_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(v_sz_78_, v_i_79_, v_bs_80_);
stack->m_obj
 = v_res_91_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(size_t v_sz_105_, size_t v_i_106_, lean_object* v_bs_107_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_105_ = stack[0].m_num;
size_t v_i_106_ = stack[1].m_num;
lean_object* v_bs_107_ = stack[2].m_obj;
lean_object* v_res_117_;
v_res_117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_105_, v_i_106_, v_bs_107_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_toMessageData(lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
lean_object* v_data_119_; lean_object* v_msg_120_; lean_object* v_children_121_; lean_object* v_wrap_122_; size_t v_sz_123_; size_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_data_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc_ref(v_data_119_);
v_msg_120_ = lean_ctor_get(v_x_118_, 1);
lean_inc_ref(v_msg_120_);
v_children_121_ = lean_ctor_get(v_x_118_, 2);
lean_inc_ref(v_children_121_);
v_wrap_122_ = lean_ctor_get(v_x_118_, 3);
lean_inc_ref(v_wrap_122_);
lean_dec_ref_known(v_x_118_, 4);
v_sz_123_ = lean_array_size(v_children_121_);
v___x_124_ = ((size_t)0ULL);
v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_123_, v___x_124_, v_children_121_);
v___x_126_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_126_, 0, v_data_119_);
lean_ctor_set(v___x_126_, 1, v_msg_120_);
lean_ctor_set(v___x_126_, 2, v___x_125_);
v___x_127_ = lean_apply_1(v_wrap_122_, v___x_126_);
return v___x_127_;
}
else
{
lean_object* v_msg_128_; 
v_msg_128_ = lean_ctor_get(v_x_118_, 0);
lean_inc_ref(v_msg_128_);
lean_dec_ref_known(v_x_118_, 1);
return v_msg_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0___boxed(lean_object* v_sz_129_, lean_object* v_i_130_, lean_object* v_bs_131_){
_start:
{
size_t v_sz_boxed_132_; size_t v_i_boxed_133_; lean_object* v_res_134_; 
v_sz_boxed_132_ = lean_unbox_usize(v_sz_129_);
lean_dec(v_sz_129_);
v_i_boxed_133_ = lean_unbox_usize(v_i_130_);
lean_dec(v_i_130_);
v_res_134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_boxed_132_, v_i_boxed_133_, v_bs_131_);
return v_res_134_;
}
}
lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(lean_object* v_roots_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v_roots_135_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_roots_135_ = stack[0].m_obj;
lean_object* v___y_136_ = stack[1].m_obj;
lean_object* v___y_137_ = stack[2].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(v_roots_135_, v___y_136_, v___y_137_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0___boxed(lean_object* v_roots_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(v_roots_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f(lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v_data_149_; lean_object* v___x_150_; 
v_data_149_ = lean_ctor_get(v_x_148_, 0);
lean_inc_ref(v_data_149_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v_data_149_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f___boxed(lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_x_152_);
lean_dec_ref(v_x_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f(lean_object* v_t_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v_val_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_165_; 
v_val_157_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_165_ == 0)
{
v___x_159_ = v___x_155_;
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_val_157_);
lean_dec(v___x_155_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_165_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v_cls_161_; lean_object* v___x_163_; 
v_cls_161_ = lean_ctor_get(v_val_157_, 0);
lean_inc(v_cls_161_);
lean_dec(v_val_157_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v_cls_161_);
v___x_163_ = v___x_159_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_cls_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f___boxed(lean_object* v_t_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_166_);
lean_dec_ref(v_t_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children(lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v_children_171_; 
v_children_171_ = lean_ctor_get(v_x_170_, 2);
lean_inc_ref(v_children_171_);
return v_children_171_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children___boxed(lean_object* v_x_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_PostprocessTraces_TraceTree_children(v_x_173_);
lean_dec_ref(v_x_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_withChildren(lean_object* v_t_175_, lean_object* v_children_176_){
_start:
{
if (lean_obj_tag(v_t_175_) == 0)
{
lean_object* v_data_177_; lean_object* v_msg_178_; lean_object* v_wrap_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_data_177_ = lean_ctor_get(v_t_175_, 0);
v_msg_178_ = lean_ctor_get(v_t_175_, 1);
v_wrap_179_ = lean_ctor_get(v_t_175_, 3);
v_isSharedCheck_186_ = !lean_is_exclusive(v_t_175_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v_t_175_, 2);
lean_dec(v_unused_187_);
v___x_181_ = v_t_175_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_wrap_179_);
lean_inc(v_msg_178_);
lean_inc(v_data_177_);
lean_dec(v_t_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 2, v_children_176_);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_data_177_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_msg_178_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_children_176_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_wrap_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_dec_ref(v_children_176_);
return v_t_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_modifyData(lean_object* v_t_188_, lean_object* v_f_189_){
_start:
{
if (lean_obj_tag(v_t_188_) == 0)
{
lean_object* v_data_190_; lean_object* v_msg_191_; lean_object* v_children_192_; lean_object* v_wrap_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_201_; 
v_data_190_ = lean_ctor_get(v_t_188_, 0);
v_msg_191_ = lean_ctor_get(v_t_188_, 1);
v_children_192_ = lean_ctor_get(v_t_188_, 2);
v_wrap_193_ = lean_ctor_get(v_t_188_, 3);
v_isSharedCheck_201_ = !lean_is_exclusive(v_t_188_);
if (v_isSharedCheck_201_ == 0)
{
v___x_195_ = v_t_188_;
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_wrap_193_);
lean_inc(v_children_192_);
lean_inc(v_msg_191_);
lean_inc(v_data_190_);
lean_dec(v_t_188_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_apply_1(v_f_189_, v_data_190_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_msg_191_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_children_192_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_wrap_193_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_dec_ref(v_f_189_);
return v_t_188_;
}
}
}
static double _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0(void){
_start:
{
lean_object* v___x_202_; double v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_float_of_nat(v___x_202_);
return v___x_203_;
}
}
double l_Lean_PostprocessTraces_TraceTree_elapsed(lean_object* v_t_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
double v___x_206_; 
v___x_206_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
return v___x_206_;
}
else
{
lean_object* v_val_207_; double v_startTime_208_; double v_stopTime_209_; double v___x_210_; 
v_val_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v___x_205_, 1);
v_startTime_208_ = lean_ctor_get_float(v_val_207_, sizeof(void*)*3);
v_stopTime_209_ = lean_ctor_get_float(v_val_207_, sizeof(void*)*3 + 8);
lean_dec(v_val_207_);
v___x_210_ = lean_float_sub(v_stopTime_209_, v_startTime_208_);
return v___x_210_;
}
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_TraceTree_elapsed_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_204_ = stack[0].m_obj;
double v_res_211_;
v_res_211_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_204_);
stack->m_float
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_elapsed___boxed(lean_object* v_t_212_){
_start:
{
double v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_212_);
lean_dec_ref(v_t_212_);
v_r_214_ = lean_box_float(v_res_213_);
return v_r_214_;
}
}
double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(lean_object* v_as_215_, size_t v_i_216_, size_t v_stop_217_, double v_b_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = lean_usize_dec_eq(v_i_216_, v_stop_217_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; double v___x_221_; double v___x_222_; size_t v___x_223_; size_t v___x_224_; 
v___x_220_ = lean_array_uget_borrowed(v_as_215_, v_i_216_);
v___x_221_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v___x_220_);
v___x_222_ = lean_float_add(v_b_218_, v___x_221_);
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_add(v_i_216_, v___x_223_);
v_i_216_ = v___x_224_;
v_b_218_ = v___x_222_;
goto _start;
}
else
{
return v_b_218_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_215_ = stack[0].m_obj;
size_t v_i_216_ = stack[1].m_num;
size_t v_stop_217_ = stack[2].m_num;
double v_b_218_ = stack[3].m_float;
double v_res_226_;
v_res_226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v_as_215_, v_i_216_, v_stop_217_, v_b_218_);
stack->m_float
 = v_res_226_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0___boxed(lean_object* v_as_227_, lean_object* v_i_228_, lean_object* v_stop_229_, lean_object* v_b_230_){
_start:
{
size_t v_i_boxed_231_; size_t v_stop_boxed_232_; double v_b_boxed_233_; double v_res_234_; lean_object* v_r_235_; 
v_i_boxed_231_ = lean_unbox_usize(v_i_228_);
lean_dec(v_i_228_);
v_stop_boxed_232_ = lean_unbox_usize(v_stop_229_);
lean_dec(v_stop_229_);
v_b_boxed_233_ = lean_unbox_float(v_b_230_);
lean_dec_ref(v_b_230_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v_as_227_, v_i_boxed_231_, v_stop_boxed_232_, v_b_boxed_233_);
lean_dec_ref(v_as_227_);
v_r_235_ = lean_box_float(v_res_234_);
return v_r_235_;
}
}
double l_Lean_PostprocessTraces_TraceTree_selfElapsed(lean_object* v_t_236_){
_start:
{
lean_object* v___x_237_; double v___x_238_; double v___x_239_; double v___y_241_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
v___x_239_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_236_);
v___x_244_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_236_);
v___x_245_ = lean_array_get_size(v___x_244_);
v___x_246_ = lean_nat_dec_lt(v___x_237_, v___x_245_);
if (v___x_246_ == 0)
{
lean_dec_ref(v___x_244_);
v___y_241_ = v___x_238_;
goto v___jp_240_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = lean_nat_dec_le(v___x_245_, v___x_245_);
if (v___x_247_ == 0)
{
if (v___x_246_ == 0)
{
lean_dec_ref(v___x_244_);
v___y_241_ = v___x_238_;
goto v___jp_240_;
}
else
{
size_t v___x_248_; size_t v___x_249_; double v___x_250_; 
v___x_248_ = ((size_t)0ULL);
v___x_249_ = lean_usize_of_nat(v___x_245_);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_244_, v___x_248_, v___x_249_, v___x_238_);
lean_dec_ref(v___x_244_);
v___y_241_ = v___x_250_;
goto v___jp_240_;
}
}
else
{
size_t v___x_251_; size_t v___x_252_; double v___x_253_; 
v___x_251_ = ((size_t)0ULL);
v___x_252_ = lean_usize_of_nat(v___x_245_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_244_, v___x_251_, v___x_252_, v___x_238_);
lean_dec_ref(v___x_244_);
v___y_241_ = v___x_253_;
goto v___jp_240_;
}
}
v___jp_240_:
{
double v___x_242_; double v___x_243_; 
v___x_242_ = lean_float_sub(v___x_239_, v___y_241_);
v___x_243_ = lean_float_maximum(v___x_238_, v___x_242_);
return v___x_243_;
}
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_TraceTree_selfElapsed_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_236_ = stack[0].m_obj;
double v_res_254_;
v_res_254_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_236_);
stack->m_float
 = v_res_254_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_selfElapsed___boxed(lean_object* v_t_255_){
_start:
{
double v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_255_);
lean_dec_ref(v_t_255_);
v_r_257_ = lean_box_float(v_res_256_);
return v_r_257_;
}
}
lean_object* l_Lean_PostprocessTraces_TraceTree_headText(lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_data_261_; lean_object* v_msg_262_; lean_object* v_wrap_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_result_x3f_266_; 
v_data_261_ = lean_ctor_get(v_x_259_, 0);
lean_inc_ref(v_data_261_);
v_msg_262_ = lean_ctor_get(v_x_259_, 1);
lean_inc_ref(v_msg_262_);
v_wrap_263_ = lean_ctor_get(v_x_259_, 3);
lean_inc_ref(v_wrap_263_);
lean_dec_ref_known(v_x_259_, 4);
v___x_264_ = lean_apply_1(v_wrap_263_, v_msg_262_);
v___x_265_ = l_Lean_MessageData_toString(v___x_264_);
v_result_x3f_266_ = lean_ctor_get(v_data_261_, 1);
lean_inc(v_result_x3f_266_);
lean_dec_ref(v_data_261_);
if (lean_obj_tag(v_result_x3f_266_) == 0)
{
return v___x_265_;
}
else
{
lean_object* v_val_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_val_267_ = lean_ctor_get(v_result_x3f_266_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v_result_x3f_266_, 1);
v___x_268_ = lean_unbox(v_val_267_);
lean_dec(v_val_267_);
v___x_269_ = l_Lean_TraceResult_toEmoji(v___x_268_);
v___x_270_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_headText___closed__0));
v___x_271_ = lean_string_append(v___x_269_, v___x_270_);
v___x_272_ = lean_string_append(v___x_271_, v___x_265_);
lean_dec_ref(v___x_265_);
return v___x_272_;
}
}
else
{
lean_object* v_msg_273_; lean_object* v___x_274_; 
v_msg_273_ = lean_ctor_get(v_x_259_, 0);
lean_inc_ref(v_msg_273_);
lean_dec_ref_known(v_x_259_, 1);
v___x_274_ = l_Lean_MessageData_toString(v_msg_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_TraceTree_headText_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_259_ = stack[0].m_obj;
lean_object* v_res_275_;
v_res_275_ = l_Lean_PostprocessTraces_TraceTree_headText(v_x_259_);
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText___boxed(lean_object* v_x_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_PostprocessTraces_TraceTree_headText(v_x_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f(lean_object* v_t_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
else
{
lean_object* v_val_282_; lean_object* v_result_x3f_283_; 
v_val_282_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v___x_280_, 1);
v_result_x3f_283_ = lean_ctor_get(v_val_282_, 1);
lean_inc(v_result_x3f_283_);
lean_dec(v_val_282_);
return v_result_x3f_283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f___boxed(lean_object* v_t_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_284_);
lean_dec_ref(v_t_284_);
return v_res_285_;
}
}
lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees(lean_object* v_p_286_, lean_object* v_t_287_, lean_object* v_acc_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_292_; 
lean_inc_ref(v_p_286_);
lean_inc(v_a_290_);
lean_inc_ref(v_a_289_);
lean_inc_ref(v_t_287_);
v___x_292_ = lean_apply_4(v_p_286_, v_t_287_, v_a_289_, v_a_290_, lean_box(0));
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_319_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_319_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_319_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_319_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
uint8_t v___x_297_; 
v___x_297_ = lean_unbox(v_a_293_);
lean_dec(v_a_293_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_298_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_287_);
lean_dec_ref(v_t_287_);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_array_get_size(v___x_298_);
v___x_301_ = lean_nat_dec_lt(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_298_);
lean_dec_ref(v_p_286_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v_acc_288_);
v___x_303_ = v___x_295_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_acc_288_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
else
{
uint8_t v___x_305_; 
v___x_305_ = lean_nat_dec_le(v___x_300_, v___x_300_);
if (v___x_305_ == 0)
{
if (v___x_301_ == 0)
{
lean_object* v___x_307_; 
lean_dec_ref(v___x_298_);
lean_dec_ref(v_p_286_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v_acc_288_);
v___x_307_ = v___x_295_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_acc_288_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
else
{
size_t v___x_309_; size_t v___x_310_; lean_object* v___x_311_; 
lean_del_object(v___x_295_);
v___x_309_ = ((size_t)0ULL);
v___x_310_ = lean_usize_of_nat(v___x_300_);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_286_, v___x_298_, v___x_309_, v___x_310_, v_acc_288_, v_a_289_, v_a_290_);
lean_dec_ref(v___x_298_);
return v___x_311_;
}
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
lean_del_object(v___x_295_);
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_300_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_286_, v___x_298_, v___x_312_, v___x_313_, v_acc_288_, v_a_289_, v_a_290_);
lean_dec_ref(v___x_298_);
return v___x_314_;
}
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec_ref(v_p_286_);
v___x_315_ = lean_array_push(v_acc_288_, v_t_287_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_315_);
v___x_317_ = v___x_295_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_acc_288_);
lean_dec_ref(v_t_287_);
lean_dec_ref(v_p_286_);
v_a_320_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_292_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_292_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_TraceTree_collectSubtrees_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_286_ = stack[0].m_obj;
lean_object* v_t_287_ = stack[1].m_obj;
lean_object* v_acc_288_ = stack[2].m_obj;
lean_object* v_a_289_ = stack[3].m_obj;
lean_object* v_a_290_ = stack[4].m_obj;
lean_object* v_res_328_;
v_res_328_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_286_, v_t_287_, v_acc_288_, v_a_289_, v_a_290_);
stack->m_obj
 = v_res_328_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(lean_object* v_p_329_, lean_object* v_as_330_, size_t v_i_331_, size_t v_stop_332_, lean_object* v_b_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_eq(v_i_331_, v_stop_332_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_array_uget_borrowed(v_as_330_, v_i_331_);
lean_inc(v___x_338_);
lean_inc_ref(v_p_329_);
v___x_339_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_329_, v___x_338_, v_b_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; size_t v___x_341_; size_t v___x_342_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_add(v_i_331_, v___x_341_);
v_i_331_ = v___x_342_;
v_b_333_ = v_a_340_;
goto _start;
}
else
{
lean_dec_ref(v_p_329_);
return v___x_339_;
}
}
else
{
lean_object* v___x_344_; 
lean_dec_ref(v_p_329_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_b_333_);
return v___x_344_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_329_ = stack[0].m_obj;
lean_object* v_as_330_ = stack[1].m_obj;
size_t v_i_331_ = stack[2].m_num;
size_t v_stop_332_ = stack[3].m_num;
lean_object* v_b_333_ = stack[4].m_obj;
lean_object* v___y_334_ = stack[5].m_obj;
lean_object* v___y_335_ = stack[6].m_obj;
lean_object* v_res_345_;
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_329_, v_as_330_, v_i_331_, v_stop_332_, v_b_333_, v___y_334_, v___y_335_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0___boxed(lean_object* v_p_346_, lean_object* v_as_347_, lean_object* v_i_348_, lean_object* v_stop_349_, lean_object* v_b_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
size_t v_i_boxed_354_; size_t v_stop_boxed_355_; lean_object* v_res_356_; 
v_i_boxed_354_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_stop_boxed_355_ = lean_unbox_usize(v_stop_349_);
lean_dec(v_stop_349_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_346_, v_as_347_, v_i_boxed_354_, v_stop_boxed_355_, v_b_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec_ref(v_as_347_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees___boxed(lean_object* v_p_357_, lean_object* v_t_358_, lean_object* v_acc_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_357_, v_t_358_, v_acc_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
return v_res_363_;
}
}
lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(lean_object* v_p_364_, lean_object* v_as_365_, lean_object* v_start_366_, lean_object* v_stop_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
v___x_372_ = lean_nat_dec_lt(v_start_366_, v_stop_367_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; 
lean_dec_ref(v_p_364_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = lean_array_get_size(v_as_365_);
v___x_375_ = lean_nat_dec_le(v_stop_367_, v___x_374_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; 
v___x_376_ = lean_nat_dec_lt(v_start_366_, v___x_374_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec_ref(v_p_364_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_371_);
return v___x_377_;
}
else
{
size_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_usize_of_nat(v_start_366_);
v___x_379_ = lean_usize_of_nat(v___x_374_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_364_, v_as_365_, v___x_378_, v___x_379_, v___x_371_, v___y_368_, v___y_369_);
return v___x_380_;
}
}
else
{
size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_usize_of_nat(v_start_366_);
v___x_382_ = lean_usize_of_nat(v_stop_367_);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_364_, v_as_365_, v___x_381_, v___x_382_, v___x_371_, v___y_368_, v___y_369_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT void l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_364_ = stack[0].m_obj;
lean_object* v_as_365_ = stack[1].m_obj;
lean_object* v_start_366_ = stack[2].m_obj;
lean_object* v_stop_367_ = stack[3].m_obj;
lean_object* v___y_368_ = stack[4].m_obj;
lean_object* v___y_369_ = stack[5].m_obj;
lean_object* v_res_384_;
v_res_384_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_364_, v_as_365_, v_start_366_, v_stop_367_, v___y_368_, v___y_369_);
stack->m_obj
 = v_res_384_;
}
lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees(lean_object* v_p_385_, lean_object* v_t_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_390_; 
lean_inc_ref(v_p_385_);
lean_inc(v_a_388_);
lean_inc_ref(v_a_387_);
lean_inc_ref(v_t_386_);
v___x_390_ = lean_apply_4(v_p_385_, v_t_386_, v_a_387_, v_a_388_, lean_box(0));
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_428_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_428_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_428_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_428_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint8_t v___x_395_; 
v___x_395_ = lean_unbox(v_a_391_);
lean_dec(v_a_391_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_del_object(v___x_393_);
v___x_396_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_386_);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_array_get_size(v___x_396_);
v___x_399_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_385_, v___x_396_, v___x_397_, v___x_398_, v_a_387_, v_a_388_);
lean_dec_ref(v___x_396_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_415_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_415_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_415_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_415_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_array_get_size(v_a_400_);
v___x_405_ = lean_nat_dec_eq(v___x_404_, v___x_397_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_406_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_386_, v_a_400_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_407_);
v___x_409_ = v___x_402_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_413_; 
lean_dec(v_a_400_);
lean_dec_ref(v_t_386_);
v___x_411_ = lean_box(0);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_411_);
v___x_413_ = v___x_402_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec_ref(v_t_386_);
v_a_416_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_399_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_399_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_426_; 
lean_dec_ref(v_p_385_);
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v_t_386_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_424_);
v___x_426_ = v___x_393_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_t_386_);
lean_dec_ref(v_p_385_);
v_a_429_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_390_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_390_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_TraceTree_filterSubtrees_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_385_ = stack[0].m_obj;
lean_object* v_t_386_ = stack[1].m_obj;
lean_object* v_a_387_ = stack[2].m_obj;
lean_object* v_a_388_ = stack[3].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_385_, v_t_386_, v_a_387_, v_a_388_);
stack->m_obj
 = v_res_437_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(lean_object* v_p_438_, lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_a_447_; uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_eq(v_i_440_, v_stop_441_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_array_uget_borrowed(v_as_439_, v_i_440_);
lean_inc(v___x_452_);
lean_inc_ref(v_p_438_);
v___x_453_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_438_, v___x_452_, v___y_443_, v___y_444_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
if (lean_obj_tag(v_a_454_) == 0)
{
v_a_447_ = v_b_442_;
goto v___jp_446_;
}
else
{
lean_object* v_val_455_; lean_object* v___x_456_; 
v_val_455_ = lean_ctor_get(v_a_454_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v_a_454_, 1);
v___x_456_ = lean_array_push(v_b_442_, v_val_455_);
v_a_447_ = v___x_456_;
goto v___jp_446_;
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v_b_442_);
lean_dec_ref(v_p_438_);
v_a_457_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_453_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_453_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v___x_465_; 
lean_dec_ref(v_p_438_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_b_442_);
return v___x_465_;
}
v___jp_446_:
{
size_t v___x_448_; size_t v___x_449_; 
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_440_, v___x_448_);
v_i_440_ = v___x_449_;
v_b_442_ = v_a_447_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_438_ = stack[0].m_obj;
lean_object* v_as_439_ = stack[1].m_obj;
size_t v_i_440_ = stack[2].m_num;
size_t v_stop_441_ = stack[3].m_num;
lean_object* v_b_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v___y_444_ = stack[6].m_obj;
lean_object* v_res_466_;
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_438_, v_as_439_, v_i_440_, v_stop_441_, v_b_442_, v___y_443_, v___y_444_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0___boxed(lean_object* v_p_467_, lean_object* v_as_468_, lean_object* v_i_469_, lean_object* v_stop_470_, lean_object* v_b_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
size_t v_i_boxed_475_; size_t v_stop_boxed_476_; lean_object* v_res_477_; 
v_i_boxed_475_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_stop_boxed_476_ = lean_unbox_usize(v_stop_470_);
lean_dec(v_stop_470_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_467_, v_as_468_, v_i_boxed_475_, v_stop_boxed_476_, v_b_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec_ref(v_as_468_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0___boxed(lean_object* v_p_478_, lean_object* v_as_479_, lean_object* v_start_480_, lean_object* v_stop_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_478_, v_as_479_, v_start_480_, v_stop_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v_stop_481_);
lean_dec(v_start_480_);
lean_dec_ref(v_as_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees___boxed(lean_object* v_p_486_, lean_object* v_t_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_486_, v_t_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2(lean_object* v_data_492_, lean_object* v_msg_493_, lean_object* v_a_494_, lean_object* v_wrap_495_, lean_object* v_children_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_497_, 0, v_data_492_);
lean_ctor_set(v___x_497_, 1, v_msg_493_);
lean_ctor_set(v___x_497_, 2, v_children_496_);
v___x_498_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_498_, 0, v_a_494_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_apply_1(v_wrap_495_, v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(lean_object* v_wrap_503_, lean_object* v_a_504_){
_start:
{
switch(lean_obj_tag(v_a_504_))
{
case 3:
{
lean_object* v_a_505_; lean_object* v_a_506_; lean_object* v___f_507_; 
v_a_505_ = lean_ctor_get(v_a_504_, 0);
lean_inc_ref(v_a_505_);
v_a_506_ = lean_ctor_get(v_a_504_, 1);
lean_inc_ref(v_a_506_);
lean_dec_ref_known(v_a_504_, 2);
v___f_507_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0), 3, 2);
lean_closure_set(v___f_507_, 0, v_a_505_);
lean_closure_set(v___f_507_, 1, v_wrap_503_);
v_wrap_503_ = v___f_507_;
v_a_504_ = v_a_506_;
goto _start;
}
case 4:
{
lean_object* v_a_509_; lean_object* v_a_510_; lean_object* v___f_511_; 
v_a_509_ = lean_ctor_get(v_a_504_, 0);
lean_inc_ref(v_a_509_);
v_a_510_ = lean_ctor_get(v_a_504_, 1);
lean_inc_ref(v_a_510_);
lean_dec_ref_known(v_a_504_, 2);
v___f_511_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1), 3, 2);
lean_closure_set(v___f_511_, 0, v_a_509_);
lean_closure_set(v___f_511_, 1, v_wrap_503_);
v_wrap_503_ = v___f_511_;
v_a_504_ = v_a_510_;
goto _start;
}
case 8:
{
lean_object* v_a_513_; 
v_a_513_ = lean_ctor_get(v_a_504_, 1);
lean_inc_ref(v_a_513_);
if (lean_obj_tag(v_a_513_) == 9)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_529_; 
v_a_514_ = lean_ctor_get(v_a_504_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_a_504_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_a_504_, 1);
lean_dec(v_unused_530_);
v___x_516_ = v_a_504_;
v_isShared_517_ = v_isSharedCheck_529_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v_a_504_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_529_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_data_518_; lean_object* v_msg_519_; lean_object* v_children_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_data_518_ = lean_ctor_get(v_a_513_, 0);
lean_inc_ref(v_data_518_);
v_msg_519_ = lean_ctor_get(v_a_513_, 1);
lean_inc_ref(v_msg_519_);
v_children_520_ = lean_ctor_get(v_a_513_, 2);
lean_inc_ref(v_children_520_);
lean_dec_ref_known(v_a_513_, 3);
v___x_521_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__1));
v___x_522_ = lean_name_eq(v_a_514_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec_ref(v_children_520_);
lean_dec_ref(v_msg_519_);
lean_dec_ref(v_data_518_);
lean_del_object(v___x_516_);
lean_dec(v_a_514_);
lean_dec_ref(v_wrap_503_);
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v___f_524_; lean_object* v___x_526_; 
v___f_524_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2), 5, 4);
lean_closure_set(v___f_524_, 0, v_data_518_);
lean_closure_set(v___f_524_, 1, v_msg_519_);
lean_closure_set(v___f_524_, 2, v_a_514_);
lean_closure_set(v___f_524_, 3, v_wrap_503_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 0);
lean_ctor_set(v___x_516_, 1, v_children_520_);
lean_ctor_set(v___x_516_, 0, v___f_524_);
v___x_526_ = v___x_516_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___f_524_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_children_520_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_531_; 
lean_dec_ref(v_a_513_);
lean_dec_ref_known(v_a_504_, 2);
lean_dec_ref(v_wrap_503_);
v___x_531_ = lean_box(0);
return v___x_531_;
}
}
default: 
{
lean_object* v___x_532_; 
lean_dec_ref(v_a_504_);
lean_dec_ref(v_wrap_503_);
v___x_532_ = lean_box(0);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_traceContainer_x3f(lean_object* v_data_533_){
_start:
{
lean_object* v___f_534_; lean_object* v___x_535_; 
v___f_534_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0));
v___x_535_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(v___f_534_, v_data_533_);
return v___x_535_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(size_t v_sz_536_, size_t v_i_537_, lean_object* v_bs_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_lt(v_i_537_, v_sz_536_);
if (v___x_539_ == 0)
{
return v_bs_538_;
}
else
{
lean_object* v_v_540_; lean_object* v___x_541_; lean_object* v_bs_x27_542_; lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v_v_540_ = lean_array_uget(v_bs_538_, v_i_537_);
v___x_541_ = lean_unsigned_to_nat(0u);
v_bs_x27_542_ = lean_array_uset(v_bs_538_, v_i_537_, v___x_541_);
v___x_543_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData(v_v_540_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_537_, v___x_544_);
v___x_546_ = lean_array_uset(v_bs_x27_542_, v_i_537_, v___x_543_);
v_i_537_ = v___x_545_;
v_bs_538_ = v___x_546_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_536_ = stack[0].m_num;
size_t v_i_537_ = stack[1].m_num;
lean_object* v_bs_538_ = stack[2].m_obj;
lean_object* v_res_548_;
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_536_, v_i_537_, v_bs_538_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0___boxed(lean_object* v_sz_549_, lean_object* v_i_550_, lean_object* v_bs_551_){
_start:
{
size_t v_sz_boxed_552_; size_t v_i_boxed_553_; lean_object* v_res_554_; 
v_sz_boxed_552_ = lean_unbox_usize(v_sz_549_);
lean_dec(v_sz_549_);
v_i_boxed_553_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_boxed_552_, v_i_boxed_553_, v_bs_551_);
return v_res_554_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage(lean_object* v_post_555_, lean_object* v_msg_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_fileName_560_; lean_object* v_pos_561_; lean_object* v_endPos_562_; uint8_t v_keepFullRange_563_; uint8_t v_severity_564_; uint8_t v_isSilent_565_; lean_object* v_caption_566_; lean_object* v_data_567_; lean_object* v___x_568_; 
v_fileName_560_ = lean_ctor_get(v_msg_556_, 0);
v_pos_561_ = lean_ctor_get(v_msg_556_, 1);
v_endPos_562_ = lean_ctor_get(v_msg_556_, 2);
v_keepFullRange_563_ = lean_ctor_get_uint8(v_msg_556_, sizeof(void*)*5);
v_severity_564_ = lean_ctor_get_uint8(v_msg_556_, sizeof(void*)*5 + 1);
v_isSilent_565_ = lean_ctor_get_uint8(v_msg_556_, sizeof(void*)*5 + 2);
v_caption_566_ = lean_ctor_get(v_msg_556_, 3);
v_data_567_ = lean_ctor_get(v_msg_556_, 4);
lean_inc(v_data_567_);
v___x_568_ = l_Lean_Elab_PostprocessTraces_traceContainer_x3f(v_data_567_);
if (lean_obj_tag(v___x_568_) == 1)
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_615_; 
lean_inc_ref(v_caption_566_);
lean_inc(v_endPos_562_);
lean_inc_ref(v_pos_561_);
lean_inc_ref(v_fileName_560_);
v_isSharedCheck_615_ = !lean_is_exclusive(v_msg_556_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_616_ = lean_ctor_get(v_msg_556_, 4);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_msg_556_, 3);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_msg_556_, 2);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_msg_556_, 1);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_msg_556_, 0);
lean_dec(v_unused_620_);
v___x_570_ = v_msg_556_;
v_isShared_571_ = v_isSharedCheck_615_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_msg_556_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_615_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_614_; 
v_val_572_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_614_ == 0)
{
v___x_574_ = v___x_568_;
v_isShared_575_ = v_isSharedCheck_614_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v___x_568_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_614_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_fst_576_; lean_object* v_snd_577_; size_t v_sz_578_; size_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_fst_576_ = lean_ctor_get(v_val_572_, 0);
lean_inc(v_fst_576_);
v_snd_577_ = lean_ctor_get(v_val_572_, 1);
lean_inc(v_snd_577_);
lean_dec(v_val_572_);
v_sz_578_ = lean_array_size(v_snd_577_);
v___x_579_ = ((size_t)0ULL);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_578_, v___x_579_, v_snd_577_);
lean_inc(v_a_558_);
lean_inc_ref(v_a_557_);
v___x_581_ = lean_apply_4(v_post_555_, v___x_580_, v_a_557_, v_a_558_, lean_box(0));
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_605_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_605_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_605_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_605_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_array_get_size(v_a_582_);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_nat_dec_eq(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
size_t v_sz_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v_sz_589_ = lean_array_size(v_a_582_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_589_, v___x_579_, v_a_582_);
v___x_591_ = lean_apply_1(v_fst_576_, v___x_590_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 4, v___x_591_);
v___x_593_ = v___x_570_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_fileName_560_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_pos_561_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_endPos_562_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_caption_566_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v___x_591_);
lean_ctor_set_uint8(v_reuseFailAlloc_600_, sizeof(void*)*5, v_keepFullRange_563_);
lean_ctor_set_uint8(v_reuseFailAlloc_600_, sizeof(void*)*5 + 1, v_severity_564_);
lean_ctor_set_uint8(v_reuseFailAlloc_600_, sizeof(void*)*5 + 2, v_isSilent_565_);
v___x_593_ = v_reuseFailAlloc_600_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_595_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_593_);
v___x_595_ = v___x_574_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_595_);
v___x_597_ = v___x_584_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec(v_a_582_);
lean_dec(v_fst_576_);
lean_del_object(v___x_574_);
lean_del_object(v___x_570_);
lean_dec_ref(v_caption_566_);
lean_dec(v_endPos_562_);
lean_dec_ref(v_pos_561_);
lean_dec_ref(v_fileName_560_);
v___x_601_ = lean_box(0);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_601_);
v___x_603_ = v___x_584_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_fst_576_);
lean_del_object(v___x_574_);
lean_del_object(v___x_570_);
lean_dec_ref(v_caption_566_);
lean_dec(v_endPos_562_);
lean_dec_ref(v_pos_561_);
lean_dec_ref(v_fileName_560_);
v_a_606_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_581_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_581_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v___x_568_);
lean_dec_ref(v_post_555_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v_msg_556_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_postprocessMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_post_555_ = stack[0].m_obj;
lean_object* v_msg_556_ = stack[1].m_obj;
lean_object* v_a_557_ = stack[2].m_obj;
lean_object* v_a_558_ = stack[3].m_obj;
lean_object* v_res_623_;
v_res_623_ = l_Lean_Elab_PostprocessTraces_postprocessMessage(v_post_555_, v_msg_556_, v_a_557_, v_a_558_);
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed(lean_object* v_post_624_, lean_object* v_msg_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Elab_PostprocessTraces_postprocessMessage(v_post_624_, v_msg_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
return v_res_629_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(lean_object* v_a_630_, lean_object* v_messages_631_, lean_object* v_trees_632_, lean_object* v_a_x3f_633_){
_start:
{
lean_object* v___x_635_; lean_object* v_infoState_636_; lean_object* v_env_637_; lean_object* v_messages_638_; lean_object* v_scopes_639_; lean_object* v_usedQuotCtxts_640_; lean_object* v_nextMacroScope_641_; lean_object* v_maxRecDepth_642_; lean_object* v_ngen_643_; lean_object* v_auxDeclNGen_644_; lean_object* v_traceState_645_; lean_object* v_snapshotTasks_646_; lean_object* v_prevLinterStates_647_; lean_object* v_codeQualityEntryTasks_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_671_; 
v___x_635_ = lean_st_ref_take(v_a_630_);
v_infoState_636_ = lean_ctor_get(v___x_635_, 8);
v_env_637_ = lean_ctor_get(v___x_635_, 0);
v_messages_638_ = lean_ctor_get(v___x_635_, 1);
v_scopes_639_ = lean_ctor_get(v___x_635_, 2);
v_usedQuotCtxts_640_ = lean_ctor_get(v___x_635_, 3);
v_nextMacroScope_641_ = lean_ctor_get(v___x_635_, 4);
v_maxRecDepth_642_ = lean_ctor_get(v___x_635_, 5);
v_ngen_643_ = lean_ctor_get(v___x_635_, 6);
v_auxDeclNGen_644_ = lean_ctor_get(v___x_635_, 7);
v_traceState_645_ = lean_ctor_get(v___x_635_, 9);
v_snapshotTasks_646_ = lean_ctor_get(v___x_635_, 10);
v_prevLinterStates_647_ = lean_ctor_get(v___x_635_, 11);
v_codeQualityEntryTasks_648_ = lean_ctor_get(v___x_635_, 12);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_671_ == 0)
{
v___x_650_ = v___x_635_;
v_isShared_651_ = v_isSharedCheck_671_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_codeQualityEntryTasks_648_);
lean_inc(v_prevLinterStates_647_);
lean_inc(v_snapshotTasks_646_);
lean_inc(v_traceState_645_);
lean_inc(v_infoState_636_);
lean_inc(v_auxDeclNGen_644_);
lean_inc(v_ngen_643_);
lean_inc(v_maxRecDepth_642_);
lean_inc(v_nextMacroScope_641_);
lean_inc(v_usedQuotCtxts_640_);
lean_inc(v_scopes_639_);
lean_inc(v_messages_638_);
lean_inc(v_env_637_);
lean_dec(v___x_635_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_671_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
uint8_t v_enabled_652_; lean_object* v_assignment_653_; lean_object* v_lazyAssignment_654_; lean_object* v_trees_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_670_; 
v_enabled_652_ = lean_ctor_get_uint8(v_infoState_636_, sizeof(void*)*3);
v_assignment_653_ = lean_ctor_get(v_infoState_636_, 0);
v_lazyAssignment_654_ = lean_ctor_get(v_infoState_636_, 1);
v_trees_655_ = lean_ctor_get(v_infoState_636_, 2);
v_isSharedCheck_670_ = !lean_is_exclusive(v_infoState_636_);
if (v_isSharedCheck_670_ == 0)
{
v___x_657_ = v_infoState_636_;
v_isShared_658_ = v_isSharedCheck_670_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_trees_655_);
lean_inc(v_lazyAssignment_654_);
lean_inc(v_assignment_653_);
lean_dec(v_infoState_636_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_670_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_Lean_MessageLog_append(v_messages_631_, v_messages_638_);
v___x_661_ = l_Lean_PersistentArray_append___redArg(v_trees_632_, v_trees_655_);
lean_dec_ref(v_trees_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 2, v___x_661_);
v___x_663_ = v___x_657_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_assignment_653_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_lazyAssignment_654_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v___x_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_669_, sizeof(void*)*3, v_enabled_652_);
v___x_663_ = v_reuseFailAlloc_669_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 8, v___x_663_);
lean_ctor_set(v___x_650_, 1, v___x_660_);
v___x_665_ = v___x_650_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_env_637_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_scopes_639_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_usedQuotCtxts_640_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_nextMacroScope_641_);
lean_ctor_set(v_reuseFailAlloc_668_, 5, v_maxRecDepth_642_);
lean_ctor_set(v_reuseFailAlloc_668_, 6, v_ngen_643_);
lean_ctor_set(v_reuseFailAlloc_668_, 7, v_auxDeclNGen_644_);
lean_ctor_set(v_reuseFailAlloc_668_, 8, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_668_, 9, v_traceState_645_);
lean_ctor_set(v_reuseFailAlloc_668_, 10, v_snapshotTasks_646_);
lean_ctor_set(v_reuseFailAlloc_668_, 11, v_prevLinterStates_647_);
lean_ctor_set(v_reuseFailAlloc_668_, 12, v_codeQualityEntryTasks_648_);
v___x_665_ = v_reuseFailAlloc_668_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_st_ref_put(v_a_630_, v___x_665_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_659_);
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_630_ = stack[0].m_obj;
lean_object* v_messages_631_ = stack[1].m_obj;
lean_object* v_trees_632_ = stack[2].m_obj;
lean_object* v_a_x3f_633_ = stack[3].m_obj;
lean_object* v_res_672_;
v_res_672_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_630_, v_messages_631_, v_trees_632_, v_a_x3f_633_);
stack->m_obj
 = v_res_672_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0___boxed(lean_object* v_a_673_, lean_object* v_messages_674_, lean_object* v_trees_675_, lean_object* v_a_x3f_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_673_, v_messages_674_, v_trees_675_, v_a_x3f_676_);
lean_dec(v_a_x3f_676_);
lean_dec(v_a_673_);
return v_res_678_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(lean_object* v_as_679_, size_t v_i_680_, size_t v_stop_681_, lean_object* v_b_682_){
_start:
{
uint8_t v___x_683_; 
v___x_683_ = lean_usize_dec_eq(v_i_680_, v_stop_681_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v_diagnostics_685_; lean_object* v_msgLog_686_; lean_object* v___x_687_; size_t v___x_688_; size_t v___x_689_; 
v___x_684_ = lean_array_uget_borrowed(v_as_679_, v_i_680_);
v_diagnostics_685_ = lean_ctor_get(v___x_684_, 1);
v_msgLog_686_ = lean_ctor_get(v_diagnostics_685_, 0);
lean_inc_ref(v_msgLog_686_);
v___x_687_ = l_Lean_MessageLog_append(v_b_682_, v_msgLog_686_);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_add(v_i_680_, v___x_688_);
v_i_680_ = v___x_689_;
v_b_682_ = v___x_687_;
goto _start;
}
else
{
return v_b_682_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_679_ = stack[0].m_obj;
size_t v_i_680_ = stack[1].m_num;
size_t v_stop_681_ = stack[2].m_num;
lean_object* v_b_682_ = stack[3].m_obj;
lean_object* v_res_691_;
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v_as_679_, v_i_680_, v_stop_681_, v_b_682_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0___boxed(lean_object* v_as_692_, lean_object* v_i_693_, lean_object* v_stop_694_, lean_object* v_b_695_){
_start:
{
size_t v_i_boxed_696_; size_t v_stop_boxed_697_; lean_object* v_res_698_; 
v_i_boxed_696_ = lean_unbox_usize(v_i_693_);
lean_dec(v_i_693_);
v_stop_boxed_697_ = lean_unbox_usize(v_stop_694_);
lean_dec(v_stop_694_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v_as_692_, v_i_boxed_696_, v_stop_boxed_697_, v_b_695_);
lean_dec_ref(v_as_692_);
return v_res_698_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(lean_object* v_as_699_, size_t v_i_700_, size_t v_stop_701_, lean_object* v_b_702_){
_start:
{
lean_object* v___y_704_; uint8_t v___x_708_; 
v___x_708_ = lean_usize_dec_eq(v_i_700_, v_stop_701_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_709_ = lean_array_uget_borrowed(v_as_699_, v_i_700_);
v___x_710_ = l_Lean_MessageLog_empty;
lean_inc(v___x_709_);
v___x_711_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_709_);
v___x_712_ = l_Lean_Language_SnapshotTree_getAll(v___x_711_);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_array_get_size(v___x_712_);
v___x_715_ = lean_nat_dec_lt(v___x_713_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v___x_712_);
v___x_716_ = l_Lean_MessageLog_append(v_b_702_, v___x_710_);
v___y_704_ = v___x_716_;
goto v___jp_703_;
}
else
{
uint8_t v___x_717_; 
v___x_717_ = lean_nat_dec_le(v___x_714_, v___x_714_);
if (v___x_717_ == 0)
{
if (v___x_715_ == 0)
{
lean_object* v___x_718_; 
lean_dec_ref(v___x_712_);
v___x_718_ = l_Lean_MessageLog_append(v_b_702_, v___x_710_);
v___y_704_ = v___x_718_;
goto v___jp_703_;
}
else
{
size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_719_ = ((size_t)0ULL);
v___x_720_ = lean_usize_of_nat(v___x_714_);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v___x_712_, v___x_719_, v___x_720_, v___x_710_);
lean_dec_ref(v___x_712_);
v___x_722_ = l_Lean_MessageLog_append(v_b_702_, v___x_721_);
v___y_704_ = v___x_722_;
goto v___jp_703_;
}
}
else
{
size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = ((size_t)0ULL);
v___x_724_ = lean_usize_of_nat(v___x_714_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v___x_712_, v___x_723_, v___x_724_, v___x_710_);
lean_dec_ref(v___x_712_);
v___x_726_ = l_Lean_MessageLog_append(v_b_702_, v___x_725_);
v___y_704_ = v___x_726_;
goto v___jp_703_;
}
}
}
else
{
return v_b_702_;
}
v___jp_703_:
{
size_t v___x_705_; size_t v___x_706_; 
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_700_, v___x_705_);
v_i_700_ = v___x_706_;
v_b_702_ = v___y_704_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_699_ = stack[0].m_obj;
size_t v_i_700_ = stack[1].m_num;
size_t v_stop_701_ = stack[2].m_num;
lean_object* v_b_702_ = stack[3].m_obj;
lean_object* v_res_727_;
v_res_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_as_699_, v_i_700_, v_stop_701_, v_b_702_);
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1___boxed(lean_object* v_as_728_, lean_object* v_i_729_, lean_object* v_stop_730_, lean_object* v_b_731_){
_start:
{
size_t v_i_boxed_732_; size_t v_stop_boxed_733_; lean_object* v_res_734_; 
v_i_boxed_732_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_stop_boxed_733_ = lean_unbox_usize(v_stop_730_);
lean_dec(v_stop_730_);
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_as_728_, v_i_boxed_732_, v_stop_boxed_733_, v_b_731_);
lean_dec_ref(v_as_728_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_unsigned_to_nat(32u);
v___x_736_ = lean_mk_empty_array_with_capacity(v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1(void){
_start:
{
size_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_738_ = ((size_t)5ULL);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_unsigned_to_nat(32u);
v___x_741_ = lean_mk_empty_array_with_capacity(v___x_740_);
v___x_742_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0);
v___x_743_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
lean_ctor_set(v___x_743_, 2, v___x_739_);
lean_ctor_set(v___x_743_, 3, v___x_739_);
lean_ctor_set_usize(v___x_743_, 4, v___x_738_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = l_Lean_NameSet_empty;
v___x_745_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
lean_ctor_set(v___x_746_, 2, v___x_744_);
return v___x_746_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object* v_cmd_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_753_; lean_object* v_messages_754_; lean_object* v___x_755_; lean_object* v_infoState_756_; lean_object* v_trees_757_; lean_object* v___x_758_; lean_object* v_env_759_; lean_object* v_scopes_760_; lean_object* v_usedQuotCtxts_761_; lean_object* v_nextMacroScope_762_; lean_object* v_maxRecDepth_763_; lean_object* v_ngen_764_; lean_object* v_auxDeclNGen_765_; lean_object* v_infoState_766_; lean_object* v_traceState_767_; lean_object* v_snapshotTasks_768_; lean_object* v_prevLinterStates_769_; lean_object* v_codeQualityEntryTasks_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_862_; 
v___x_753_ = lean_st_ref_get(v_a_751_);
v_messages_754_ = lean_ctor_get(v___x_753_, 1);
lean_inc_ref(v_messages_754_);
lean_dec(v___x_753_);
v___x_755_ = lean_st_ref_get(v_a_751_);
v_infoState_756_ = lean_ctor_get(v___x_755_, 8);
lean_inc_ref(v_infoState_756_);
lean_dec(v___x_755_);
v_trees_757_ = lean_ctor_get(v_infoState_756_, 2);
lean_inc_ref(v_trees_757_);
lean_dec_ref(v_infoState_756_);
v___x_758_ = lean_st_ref_take(v_a_751_);
v_env_759_ = lean_ctor_get(v___x_758_, 0);
v_scopes_760_ = lean_ctor_get(v___x_758_, 2);
v_usedQuotCtxts_761_ = lean_ctor_get(v___x_758_, 3);
v_nextMacroScope_762_ = lean_ctor_get(v___x_758_, 4);
v_maxRecDepth_763_ = lean_ctor_get(v___x_758_, 5);
v_ngen_764_ = lean_ctor_get(v___x_758_, 6);
v_auxDeclNGen_765_ = lean_ctor_get(v___x_758_, 7);
v_infoState_766_ = lean_ctor_get(v___x_758_, 8);
v_traceState_767_ = lean_ctor_get(v___x_758_, 9);
v_snapshotTasks_768_ = lean_ctor_get(v___x_758_, 10);
v_prevLinterStates_769_ = lean_ctor_get(v___x_758_, 11);
v_codeQualityEntryTasks_770_ = lean_ctor_get(v___x_758_, 12);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v___x_758_, 1);
lean_dec(v_unused_863_);
v___x_772_ = v___x_758_;
v_isShared_773_ = v_isSharedCheck_862_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_codeQualityEntryTasks_770_);
lean_inc(v_prevLinterStates_769_);
lean_inc(v_snapshotTasks_768_);
lean_inc(v_traceState_767_);
lean_inc(v_infoState_766_);
lean_inc(v_auxDeclNGen_765_);
lean_inc(v_ngen_764_);
lean_inc(v_maxRecDepth_763_);
lean_inc(v_nextMacroScope_762_);
lean_inc(v_usedQuotCtxts_761_);
lean_inc(v_scopes_760_);
lean_inc(v_env_759_);
lean_dec(v___x_758_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_862_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_775_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_env_759_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_scopes_760_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_usedQuotCtxts_761_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_nextMacroScope_762_);
lean_ctor_set(v_reuseFailAlloc_861_, 5, v_maxRecDepth_763_);
lean_ctor_set(v_reuseFailAlloc_861_, 6, v_ngen_764_);
lean_ctor_set(v_reuseFailAlloc_861_, 7, v_auxDeclNGen_765_);
lean_ctor_set(v_reuseFailAlloc_861_, 8, v_infoState_766_);
lean_ctor_set(v_reuseFailAlloc_861_, 9, v_traceState_767_);
lean_ctor_set(v_reuseFailAlloc_861_, 10, v_snapshotTasks_768_);
lean_ctor_set(v_reuseFailAlloc_861_, 11, v_prevLinterStates_769_);
lean_ctor_set(v_reuseFailAlloc_861_, 12, v_codeQualityEntryTasks_770_);
v___x_777_ = v_reuseFailAlloc_861_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v_fileName_779_; lean_object* v_fileMap_780_; lean_object* v_currRecDepth_781_; lean_object* v_cmdPos_782_; lean_object* v_macroStack_783_; lean_object* v_quotContext_x3f_784_; lean_object* v_currMacroScope_785_; lean_object* v_ref_786_; lean_object* v_cancelTk_x3f_787_; uint8_t v_suppressElabErrors_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_778_ = lean_st_ref_put(v_a_751_, v___x_777_);
v_fileName_779_ = lean_ctor_get(v_a_750_, 0);
v_fileMap_780_ = lean_ctor_get(v_a_750_, 1);
v_currRecDepth_781_ = lean_ctor_get(v_a_750_, 2);
v_cmdPos_782_ = lean_ctor_get(v_a_750_, 3);
v_macroStack_783_ = lean_ctor_get(v_a_750_, 4);
v_quotContext_x3f_784_ = lean_ctor_get(v_a_750_, 5);
v_currMacroScope_785_ = lean_ctor_get(v_a_750_, 6);
v_ref_786_ = lean_ctor_get(v_a_750_, 7);
v_cancelTk_x3f_787_ = lean_ctor_get(v_a_750_, 9);
v_suppressElabErrors_788_ = lean_ctor_get_uint8(v_a_750_, sizeof(void*)*10);
v___x_789_ = lean_box(0);
lean_inc(v_cancelTk_x3f_787_);
lean_inc(v_ref_786_);
lean_inc(v_currMacroScope_785_);
lean_inc(v_quotContext_x3f_784_);
lean_inc(v_macroStack_783_);
lean_inc(v_cmdPos_782_);
lean_inc(v_currRecDepth_781_);
lean_inc_ref(v_fileMap_780_);
lean_inc_ref(v_fileName_779_);
v___x_790_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_790_, 0, v_fileName_779_);
lean_ctor_set(v___x_790_, 1, v_fileMap_780_);
lean_ctor_set(v___x_790_, 2, v_currRecDepth_781_);
lean_ctor_set(v___x_790_, 3, v_cmdPos_782_);
lean_ctor_set(v___x_790_, 4, v_macroStack_783_);
lean_ctor_set(v___x_790_, 5, v_quotContext_x3f_784_);
lean_ctor_set(v___x_790_, 6, v_currMacroScope_785_);
lean_ctor_set(v___x_790_, 7, v_ref_786_);
lean_ctor_set(v___x_790_, 8, v___x_789_);
lean_ctor_set(v___x_790_, 9, v_cancelTk_x3f_787_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*10, v_suppressElabErrors_788_);
v___x_791_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_749_, v___x_790_, v_a_751_);
lean_dec_ref_known(v___x_790_, 10);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_849_; 
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_850_);
v___x_793_ = v___x_791_;
v_isShared_794_ = v_isSharedCheck_849_;
goto v_resetjp_792_;
}
else
{
lean_dec(v___x_791_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_849_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_messages_797_; lean_object* v___y_799_; lean_object* v_snapshotTasks_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_795_ = lean_st_ref_get(v_a_751_);
v___x_796_ = lean_st_ref_get(v_a_751_);
v_messages_797_ = lean_ctor_get(v___x_795_, 1);
lean_inc_ref(v_messages_797_);
lean_dec(v___x_795_);
v_snapshotTasks_838_ = lean_ctor_get(v___x_796_, 10);
lean_inc_ref(v_snapshotTasks_838_);
lean_dec(v___x_796_);
v___x_839_ = l_Lean_MessageLog_empty;
v___x_840_ = lean_array_get_size(v_snapshotTasks_838_);
v___x_841_ = lean_nat_dec_lt(v___x_774_, v___x_840_);
if (v___x_841_ == 0)
{
lean_dec_ref(v_snapshotTasks_838_);
v___y_799_ = v___x_839_;
goto v___jp_798_;
}
else
{
uint8_t v___x_842_; 
v___x_842_ = lean_nat_dec_le(v___x_840_, v___x_840_);
if (v___x_842_ == 0)
{
if (v___x_841_ == 0)
{
lean_dec_ref(v_snapshotTasks_838_);
v___y_799_ = v___x_839_;
goto v___jp_798_;
}
else
{
size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((size_t)0ULL);
v___x_844_ = lean_usize_of_nat(v___x_840_);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_838_, v___x_843_, v___x_844_, v___x_839_);
lean_dec_ref(v_snapshotTasks_838_);
v___y_799_ = v___x_845_;
goto v___jp_798_;
}
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((size_t)0ULL);
v___x_847_ = lean_usize_of_nat(v___x_840_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_838_, v___x_846_, v___x_847_, v___x_839_);
lean_dec_ref(v_snapshotTasks_838_);
v___y_799_ = v___x_848_;
goto v___jp_798_;
}
}
v___jp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v_env_802_; lean_object* v_scopes_803_; lean_object* v_usedQuotCtxts_804_; lean_object* v_nextMacroScope_805_; lean_object* v_maxRecDepth_806_; lean_object* v_ngen_807_; lean_object* v_auxDeclNGen_808_; lean_object* v_infoState_809_; lean_object* v_traceState_810_; lean_object* v_prevLinterStates_811_; lean_object* v_codeQualityEntryTasks_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_835_; 
v___x_800_ = l_Lean_MessageLog_append(v_messages_797_, v___y_799_);
v___x_801_ = lean_st_ref_take(v_a_751_);
v_env_802_ = lean_ctor_get(v___x_801_, 0);
v_scopes_803_ = lean_ctor_get(v___x_801_, 2);
v_usedQuotCtxts_804_ = lean_ctor_get(v___x_801_, 3);
v_nextMacroScope_805_ = lean_ctor_get(v___x_801_, 4);
v_maxRecDepth_806_ = lean_ctor_get(v___x_801_, 5);
v_ngen_807_ = lean_ctor_get(v___x_801_, 6);
v_auxDeclNGen_808_ = lean_ctor_get(v___x_801_, 7);
v_infoState_809_ = lean_ctor_get(v___x_801_, 8);
v_traceState_810_ = lean_ctor_get(v___x_801_, 9);
v_prevLinterStates_811_ = lean_ctor_get(v___x_801_, 11);
v_codeQualityEntryTasks_812_ = lean_ctor_get(v___x_801_, 12);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; lean_object* v_unused_837_; 
v_unused_836_ = lean_ctor_get(v___x_801_, 10);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v___x_801_, 1);
lean_dec(v_unused_837_);
v___x_814_ = v___x_801_;
v_isShared_815_ = v_isSharedCheck_835_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_codeQualityEntryTasks_812_);
lean_inc(v_prevLinterStates_811_);
lean_inc(v_traceState_810_);
lean_inc(v_infoState_809_);
lean_inc(v_auxDeclNGen_808_);
lean_inc(v_ngen_807_);
lean_inc(v_maxRecDepth_806_);
lean_inc(v_nextMacroScope_805_);
lean_inc(v_usedQuotCtxts_804_);
lean_inc(v_scopes_803_);
lean_inc(v_env_802_);
lean_dec(v___x_801_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_835_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3));
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 10, v___x_816_);
lean_ctor_set(v___x_814_, 1, v___x_775_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_env_802_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_scopes_803_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_usedQuotCtxts_804_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v_nextMacroScope_805_);
lean_ctor_set(v_reuseFailAlloc_834_, 5, v_maxRecDepth_806_);
lean_ctor_set(v_reuseFailAlloc_834_, 6, v_ngen_807_);
lean_ctor_set(v_reuseFailAlloc_834_, 7, v_auxDeclNGen_808_);
lean_ctor_set(v_reuseFailAlloc_834_, 8, v_infoState_809_);
lean_ctor_set(v_reuseFailAlloc_834_, 9, v_traceState_810_);
lean_ctor_set(v_reuseFailAlloc_834_, 10, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_834_, 11, v_prevLinterStates_811_);
lean_ctor_set(v_reuseFailAlloc_834_, 12, v_codeQualityEntryTasks_812_);
v___x_818_ = v_reuseFailAlloc_834_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = lean_st_ref_put(v_a_751_, v___x_818_);
v___x_820_ = l_Lean_MessageLog_toArray(v___x_800_);
lean_dec_ref(v___x_800_);
lean_inc_ref(v___x_820_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_820_);
v___x_822_ = v___x_793_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_833_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
v___x_824_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_751_, v_messages_754_, v_trees_757_, v___x_823_);
lean_dec_ref_known(v___x_823_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v___x_824_, 0);
lean_dec(v_unused_832_);
v___x_826_ = v___x_824_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_dec(v___x_824_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_820_);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_820_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
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
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_851_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_791_, 1);
v___x_852_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_751_, v_messages_754_, v_trees_757_, v___x_789_);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v___x_852_, 0);
lean_dec(v_unused_860_);
v___x_854_ = v___x_852_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_dec(v___x_852_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 1);
lean_ctor_set(v___x_854_, 0, v_a_851_);
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_851_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_runAndCollectMessages_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_749_ = stack[0].m_obj;
lean_object* v_a_750_ = stack[1].m_obj;
lean_object* v_a_751_ = stack[2].m_obj;
lean_object* v_res_864_;
v_res_864_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v_cmd_749_, v_a_750_, v_a_751_);
stack->m_obj
 = v_res_864_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___boxed(lean_object* v_cmd_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v_cmd_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_869_;
}
}
lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(lean_object* v_type_870_, lean_object* v_e_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
uint8_t v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; 
v___x_877_ = 1;
v___x_878_ = 1;
v___x_879_ = l_Lean_Meta_evalExpr___redArg(v_type_870_, v_e_871_, v___x_877_, v___x_878_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
return v___x_879_;
}
}
LEAN_EXPORT void l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_870_ = stack[0].m_obj;
lean_object* v_e_871_ = stack[1].m_obj;
lean_object* v_a_872_ = stack[2].m_obj;
lean_object* v_a_873_ = stack[3].m_obj;
lean_object* v_a_874_ = stack[4].m_obj;
lean_object* v_a_875_ = stack[5].m_obj;
lean_object* v_res_880_;
v_res_880_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(v_type_870_, v_e_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1___boxed(lean_object* v_type_881_, lean_object* v_e_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(v_type_881_, v_e_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
return v_res_888_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(lean_object* v_e_889_, lean_object* v___y_890_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_Expr_hasMVar(v_e_889_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v_e_889_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; lean_object* v_mctx_895_; lean_object* v___x_896_; lean_object* v_fst_897_; lean_object* v_snd_898_; lean_object* v___x_899_; lean_object* v_cache_900_; lean_object* v_zetaDeltaFVarIds_901_; lean_object* v_postponed_902_; lean_object* v_diag_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_912_; 
v___x_894_ = lean_st_ref_get(v___y_890_);
v_mctx_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_mctx_895_);
lean_dec(v___x_894_);
v___x_896_ = l_Lean_instantiateMVarsCore(v_mctx_895_, v_e_889_);
v_fst_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_fst_897_);
v_snd_898_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_snd_898_);
lean_dec_ref(v___x_896_);
v___x_899_ = lean_st_ref_take(v___y_890_);
v_cache_900_ = lean_ctor_get(v___x_899_, 1);
v_zetaDeltaFVarIds_901_ = lean_ctor_get(v___x_899_, 2);
v_postponed_902_ = lean_ctor_get(v___x_899_, 3);
v_diag_903_ = lean_ctor_get(v___x_899_, 4);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_913_);
v___x_905_ = v___x_899_;
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_diag_903_);
lean_inc(v_postponed_902_);
lean_inc(v_zetaDeltaFVarIds_901_);
lean_inc(v_cache_900_);
lean_dec(v___x_899_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v_snd_898_);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_snd_898_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_cache_900_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_zetaDeltaFVarIds_901_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_postponed_902_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v_diag_903_);
v___x_908_ = v_reuseFailAlloc_911_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_st_ref_put(v___y_890_, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v_fst_897_);
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_889_ = stack[0].m_obj;
lean_object* v___y_890_ = stack[1].m_obj;
lean_object* v_res_914_;
v_res_914_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_889_, v___y_890_);
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg___boxed(lean_object* v_e_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_915_, v___y_916_);
lean_dec(v___y_916_);
return v_res_918_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(lean_object* v_e_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_919_, v___y_923_);
return v___x_927_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_919_ = stack[0].m_obj;
lean_object* v___y_920_ = stack[1].m_obj;
lean_object* v___y_921_ = stack[2].m_obj;
lean_object* v___y_922_ = stack[3].m_obj;
lean_object* v___y_923_ = stack[4].m_obj;
lean_object* v___y_924_ = stack[5].m_obj;
lean_object* v___y_925_ = stack[6].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(v_e_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___boxed(lean_object* v_e_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(v_e_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_937_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_box(0);
v___x_939_ = l_Lean_Elab_abortTermExceptionId;
v___x_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
return v___x_940_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg(){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_944_;
v_res_944_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___boxed(lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v_res_946_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(lean_object* v_00_u03b1_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v___x_955_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_948_ = stack[1].m_obj;
lean_object* v___y_949_ = stack[2].m_obj;
lean_object* v___y_950_ = stack[3].m_obj;
lean_object* v___y_951_ = stack[4].m_obj;
lean_object* v___y_952_ = stack[5].m_obj;
lean_object* v___y_953_ = stack[6].m_obj;
lean_object* v_res_956_;
v_res_956_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(lean_box(0), v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___boxed(lean_object* v_00_u03b1_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(v_00_u03b1_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_965_;
}
}
lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(lean_object* v___x_966_, lean_object* v___x_967_, uint8_t v___x_968_, lean_object* v___x_969_, uint8_t v___x_970_, lean_object* v___x_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_966_, v___x_967_, v___x_968_, v___x_968_, v___x_969_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_970_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; lean_object* v_a_983_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; uint8_t v___x_1024_; 
lean_dec_ref_known(v___x_981_, 1);
v___x_982_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_a_980_, v___y_975_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___x_982_);
v___x_1024_ = l_Lean_Expr_hasSyntheticSorry(v_a_983_);
if (v___x_1024_ == 0)
{
v___y_985_ = v___y_972_;
v___y_986_ = v___y_973_;
v___y_987_ = v___y_974_;
v___y_988_ = v___y_975_;
v___y_989_ = v___y_976_;
v___y_990_ = v___y_977_;
goto v___jp_984_;
}
else
{
lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_a_983_);
lean_dec_ref(v___x_971_);
v___x_1025_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
v___jp_984_:
{
lean_object* v___x_991_; 
lean_inc(v_a_983_);
v___x_991_ = l_Lean_Meta_getMVars(v_a_983_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = lean_box(0);
v___x_994_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_992_, v___x_993_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v_a_992_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; uint8_t v___x_996_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = lean_unbox(v_a_995_);
lean_dec(v_a_995_);
if (v___x_996_ == 0)
{
uint8_t v___x_997_; lean_object* v___x_998_; 
v___x_997_ = 1;
v___x_998_ = l_Lean_Meta_evalExpr___redArg(v___x_971_, v_a_983_, v___x_997_, v___x_968_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_a_983_);
lean_dec_ref(v___x_971_);
v___x_999_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_a_983_);
lean_dec_ref(v___x_971_);
v_a_1008_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_994_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_994_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_a_983_);
lean_dec_ref(v___x_971_);
v_a_1016_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_991_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_991_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_a_980_);
lean_dec_ref(v___x_971_);
v_a_1034_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_981_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_981_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v___x_971_);
v_a_1042_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_979_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_979_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_966_ = stack[0].m_obj;
lean_object* v___x_967_ = stack[1].m_obj;
uint8_t v___x_968_ = stack[2].m_num;
lean_object* v___x_969_ = stack[3].m_obj;
uint8_t v___x_970_ = stack[4].m_num;
lean_object* v___x_971_ = stack[5].m_obj;
lean_object* v___y_972_ = stack[6].m_obj;
lean_object* v___y_973_ = stack[7].m_obj;
lean_object* v___y_974_ = stack[8].m_obj;
lean_object* v___y_975_ = stack[9].m_obj;
lean_object* v___y_976_ = stack[10].m_obj;
lean_object* v___y_977_ = stack[11].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(v___x_966_, v___x_967_, v___x_968_, v___x_969_, v___x_970_, v___x_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed(lean_object* v___x_1051_, lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v___x_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v___x_5916__boxed_1064_; uint8_t v___x_5918__boxed_1065_; lean_object* v_res_1066_; 
v___x_5916__boxed_1064_ = lean_unbox(v___x_1053_);
v___x_5918__boxed_1065_ = lean_unbox(v___x_1055_);
v_res_1066_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(v___x_1051_, v___x_1052_, v___x_5916__boxed_1064_, v___x_1054_, v___x_5918__boxed_1065_, v___x_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1066_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_1073_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
lean_ctor_set(v___x_1073_, 2, v___x_1072_);
lean_ctor_set(v___x_1073_, 3, v___x_1072_);
lean_ctor_set(v___x_1073_, 4, v___x_1072_);
lean_ctor_set(v___x_1073_, 5, v___x_1072_);
return v___x_1073_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(lean_object* v_env_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v_nextMacroScope_1079_; lean_object* v_ngen_1080_; lean_object* v_auxDeclNGen_1081_; lean_object* v_traceState_1082_; lean_object* v_recordedDeps_1083_; lean_object* v_messages_1084_; lean_object* v_infoState_1085_; lean_object* v_snapshotTasks_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1112_; 
v___x_1078_ = lean_st_ref_take(v___y_1076_);
v_nextMacroScope_1079_ = lean_ctor_get(v___x_1078_, 1);
v_ngen_1080_ = lean_ctor_get(v___x_1078_, 2);
v_auxDeclNGen_1081_ = lean_ctor_get(v___x_1078_, 3);
v_traceState_1082_ = lean_ctor_get(v___x_1078_, 4);
v_recordedDeps_1083_ = lean_ctor_get(v___x_1078_, 6);
v_messages_1084_ = lean_ctor_get(v___x_1078_, 7);
v_infoState_1085_ = lean_ctor_get(v___x_1078_, 8);
v_snapshotTasks_1086_ = lean_ctor_get(v___x_1078_, 9);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; lean_object* v_unused_1114_; 
v_unused_1113_ = lean_ctor_get(v___x_1078_, 5);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v___x_1078_, 0);
lean_dec(v_unused_1114_);
v___x_1088_ = v___x_1078_;
v_isShared_1089_ = v_isSharedCheck_1112_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snapshotTasks_1086_);
lean_inc(v_infoState_1085_);
lean_inc(v_messages_1084_);
lean_inc(v_recordedDeps_1083_);
lean_inc(v_traceState_1082_);
lean_inc(v_auxDeclNGen_1081_);
lean_inc(v_ngen_1080_);
lean_inc(v_nextMacroScope_1079_);
lean_dec(v___x_1078_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1112_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 5, v___x_1090_);
lean_ctor_set(v___x_1088_, 0, v_env_1074_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_env_1074_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_nextMacroScope_1079_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_ngen_1080_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_auxDeclNGen_1081_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v_traceState_1082_);
lean_ctor_set(v_reuseFailAlloc_1111_, 5, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1111_, 6, v_recordedDeps_1083_);
lean_ctor_set(v_reuseFailAlloc_1111_, 7, v_messages_1084_);
lean_ctor_set(v_reuseFailAlloc_1111_, 8, v_infoState_1085_);
lean_ctor_set(v_reuseFailAlloc_1111_, 9, v_snapshotTasks_1086_);
v___x_1092_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_mctx_1095_; lean_object* v_zetaDeltaFVarIds_1096_; lean_object* v_postponed_1097_; lean_object* v_diag_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1109_; 
v___x_1093_ = lean_st_ref_put(v___y_1076_, v___x_1092_);
v___x_1094_ = lean_st_ref_take(v___y_1075_);
v_mctx_1095_ = lean_ctor_get(v___x_1094_, 0);
v_zetaDeltaFVarIds_1096_ = lean_ctor_get(v___x_1094_, 2);
v_postponed_1097_ = lean_ctor_get(v___x_1094_, 3);
v_diag_1098_ = lean_ctor_get(v___x_1094_, 4);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v___x_1094_, 1);
lean_dec(v_unused_1110_);
v___x_1100_ = v___x_1094_;
v_isShared_1101_ = v_isSharedCheck_1109_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_diag_1098_);
lean_inc(v_postponed_1097_);
lean_inc(v_zetaDeltaFVarIds_1096_);
lean_inc(v_mctx_1095_);
lean_dec(v___x_1094_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1109_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v___x_1103_);
v___x_1105_ = v___x_1100_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_mctx_1095_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_zetaDeltaFVarIds_1096_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_postponed_1097_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_diag_1098_);
v___x_1105_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_st_ref_put(v___y_1075_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1102_);
return v___x_1107_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1074_ = stack[0].m_obj;
lean_object* v___y_1075_ = stack[1].m_obj;
lean_object* v___y_1076_ = stack[2].m_obj;
lean_object* v_res_1115_;
v_res_1115_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1074_, v___y_1075_, v___y_1076_);
stack->m_obj
 = v_res_1115_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___boxed(lean_object* v_env_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec(v___y_1117_);
return v_res_1120_;
}
}
lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(lean_object* v_env_1121_, lean_object* v_x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v_env_1131_; lean_object* v_a_1133_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1130_ = lean_st_ref_get(v___y_1128_);
v_env_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc_ref(v_env_1131_);
lean_dec(v___x_1130_);
v___x_1143_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1121_, v___y_1126_, v___y_1128_);
lean_dec_ref(v___x_1143_);
lean_inc(v___y_1128_);
lean_inc_ref(v___y_1127_);
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___y_1124_);
lean_inc_ref(v___y_1123_);
v___x_1144_ = lean_apply_7(v_x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, lean_box(0));
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1131_, v___y_1126_, v___y_1128_);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1154_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_a_1145_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1145_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1144_, 1);
v_a_1133_ = v_a_1155_;
goto v___jp_1132_;
}
v___jp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v___x_1134_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1131_, v___y_1126_, v___y_1128_);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v___x_1134_, 0);
lean_dec(v_unused_1142_);
v___x_1136_ = v___x_1134_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_dec(v___x_1134_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 1);
lean_ctor_set(v___x_1136_, 0, v_a_1133_);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1133_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1121_ = stack[0].m_obj;
lean_object* v_x_1122_ = stack[1].m_obj;
lean_object* v___y_1123_ = stack[2].m_obj;
lean_object* v___y_1124_ = stack[3].m_obj;
lean_object* v___y_1125_ = stack[4].m_obj;
lean_object* v___y_1126_ = stack[5].m_obj;
lean_object* v___y_1127_ = stack[6].m_obj;
lean_object* v___y_1128_ = stack[7].m_obj;
lean_object* v_res_1156_;
v_res_1156_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1121_, v_x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
stack->m_obj
 = v_res_1156_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg___boxed(lean_object* v_env_1157_, lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1157_, v_x_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1166_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10));
v___x_1188_ = l_String_toRawSubstring_x27(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24));
v___x_1217_ = l_String_toRawSubstring_x27(v___x_1216_);
return v___x_1217_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34));
v___x_1240_ = l_String_toRawSubstring_x27(v___x_1239_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_box(0);
v___x_1255_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37));
v___x_1256_ = l_Lean_mkConst(v___x_1255_, v___x_1254_);
return v___x_1256_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41);
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(lean_object* v_post_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_toCold_1267_; lean_object* v_ref_1268_; lean_object* v_quotContext_1269_; lean_object* v_currMacroScope_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v_env_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_toCold_1267_ = lean_ctor_get(v_a_1264_, 0);
v_ref_1268_ = lean_ctor_get(v_a_1264_, 2);
v_quotContext_1269_ = lean_ctor_get(v_toCold_1267_, 8);
v_currMacroScope_1270_ = lean_ctor_get(v_toCold_1267_, 9);
v___x_1271_ = 0;
v___x_1272_ = l_Lean_SourceInfo_fromRef(v_ref_1268_, v___x_1271_);
v___x_1273_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3));
v___x_1274_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4));
lean_inc_n(v___x_1272_, 14);
v___x_1275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1272_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
v___x_1276_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7));
v___x_1277_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9));
v___x_1278_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11);
v___x_1279_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13));
lean_inc_n(v_currMacroScope_1270_, 3);
lean_inc_n(v_quotContext_1269_, 3);
v___x_1280_ = l_Lean_addMacroScope(v_quotContext_1269_, v___x_1279_, v_currMacroScope_1270_);
v___x_1281_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15));
v___x_1282_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1272_);
lean_ctor_set(v___x_1282_, 1, v___x_1278_);
lean_ctor_set(v___x_1282_, 2, v___x_1280_);
lean_ctor_set(v___x_1282_, 3, v___x_1281_);
v___x_1283_ = l_Lean_Syntax_node1(v___x_1272_, v___x_1277_, v___x_1282_);
v___x_1284_ = l_Lean_Syntax_node1(v___x_1272_, v___x_1276_, v___x_1283_);
v___x_1285_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16));
v___x_1286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1272_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18));
v___x_1288_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20));
v___x_1289_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21));
v___x_1290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1272_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23));
v___x_1292_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25);
v___x_1293_ = lean_box(0);
v___x_1294_ = l_Lean_addMacroScope(v_quotContext_1269_, v___x_1293_, v_currMacroScope_1270_);
v___x_1295_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32));
v___x_1296_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1272_);
lean_ctor_set(v___x_1296_, 1, v___x_1292_);
lean_ctor_set(v___x_1296_, 2, v___x_1294_);
lean_ctor_set(v___x_1296_, 3, v___x_1295_);
v___x_1297_ = l_Lean_Syntax_node1(v___x_1272_, v___x_1291_, v___x_1296_);
v___x_1298_ = l_Lean_Syntax_node2(v___x_1272_, v___x_1288_, v___x_1290_, v___x_1297_);
v___x_1299_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33));
v___x_1300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1272_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35);
v___x_1302_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36));
v___x_1303_ = l_Lean_addMacroScope(v_quotContext_1269_, v___x_1302_, v_currMacroScope_1270_);
v___x_1304_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39));
v___x_1305_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1272_);
lean_ctor_set(v___x_1305_, 1, v___x_1301_);
lean_ctor_set(v___x_1305_, 2, v___x_1303_);
lean_ctor_set(v___x_1305_, 3, v___x_1304_);
v___x_1306_ = l_Lean_Syntax_node1(v___x_1272_, v___x_1277_, v___x_1305_);
v___x_1307_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40));
v___x_1308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1272_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_Syntax_node5(v___x_1272_, v___x_1287_, v___x_1298_, v_post_1259_, v___x_1300_, v___x_1306_, v___x_1308_);
v___x_1310_ = l_Lean_Syntax_node4(v___x_1272_, v___x_1274_, v___x_1275_, v___x_1284_, v___x_1286_, v___x_1309_);
v___x_1311_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41);
v___x_1312_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42);
v___x_1313_ = 1;
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_box(v___x_1313_);
v___x_1316_ = lean_box(v___x_1271_);
v___f_1317_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1317_, 0, v___x_1310_);
lean_closure_set(v___f_1317_, 1, v___x_1312_);
lean_closure_set(v___f_1317_, 2, v___x_1315_);
lean_closure_set(v___f_1317_, 3, v___x_1314_);
lean_closure_set(v___f_1317_, 4, v___x_1316_);
lean_closure_set(v___f_1317_, 5, v___x_1311_);
v___x_1318_ = lean_st_ref_get(v_a_1265_);
v_env_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_ref(v_env_1319_);
lean_dec(v___x_1318_);
v___x_1320_ = l_Lean_Environment_unlockAsync(v_env_1319_);
v___x_1321_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v___x_1320_, v___f_1317_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
return v___x_1321_;
}
}
LEAN_EXPORT void l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_0interp(lean_interpreter_value* stack)
{
lean_object* v_post_1259_ = stack[0].m_obj;
lean_object* v_a_1260_ = stack[1].m_obj;
lean_object* v_a_1261_ = stack[2].m_obj;
lean_object* v_a_1262_ = stack[3].m_obj;
lean_object* v_a_1263_ = stack[4].m_obj;
lean_object* v_a_1264_ = stack[5].m_obj;
lean_object* v_a_1265_ = stack[6].m_obj;
lean_object* v_res_1322_;
v_res_1322_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
stack->m_obj
 = v_res_1322_;
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___boxed(lean_object* v_post_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1331_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(lean_object* v_env_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1332_, v___y_1336_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1332_ = stack[0].m_obj;
lean_object* v___y_1333_ = stack[1].m_obj;
lean_object* v___y_1334_ = stack[2].m_obj;
lean_object* v___y_1335_ = stack[3].m_obj;
lean_object* v___y_1336_ = stack[4].m_obj;
lean_object* v___y_1337_ = stack[5].m_obj;
lean_object* v___y_1338_ = stack[6].m_obj;
lean_object* v_res_1341_;
v_res_1341_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(v_env_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
stack->m_obj
 = v_res_1341_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___boxed(lean_object* v_env_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(v_env_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1350_;
}
}
lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(lean_object* v_00_u03b1_1351_, lean_object* v_env_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1352_, v_x_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT void l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1352_ = stack[1].m_obj;
lean_object* v_x_1353_ = stack[2].m_obj;
lean_object* v___y_1354_ = stack[3].m_obj;
lean_object* v___y_1355_ = stack[4].m_obj;
lean_object* v___y_1356_ = stack[5].m_obj;
lean_object* v___y_1357_ = stack[6].m_obj;
lean_object* v___y_1358_ = stack[7].m_obj;
lean_object* v___y_1359_ = stack[8].m_obj;
lean_object* v_res_1362_;
v_res_1362_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(lean_box(0), v_env_1352_, v_x_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
stack->m_obj
 = v_res_1362_;
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_env_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(v_00_u03b1_1363_, v_env_1364_, v_x_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1373_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(lean_object* v_post_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1374_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_post_1374_ = stack[0].m_obj;
lean_object* v_x_1375_ = stack[1].m_obj;
lean_object* v___y_1376_ = stack[2].m_obj;
lean_object* v___y_1377_ = stack[3].m_obj;
lean_object* v___y_1378_ = stack[4].m_obj;
lean_object* v___y_1379_ = stack[5].m_obj;
lean_object* v___y_1380_ = stack[6].m_obj;
lean_object* v___y_1381_ = stack[7].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(v_post_1374_, v_x_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
stack->m_obj
 = v_res_1384_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed(lean_object* v_post_1385_, lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(v_post_1385_, v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec_ref(v_x_1386_);
return v_res_1394_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(lean_object* v_a_1395_, lean_object* v_traceState_1396_, lean_object* v_a_x3f_1397_){
_start:
{
lean_object* v___x_1399_; lean_object* v_env_1400_; lean_object* v_messages_1401_; lean_object* v_scopes_1402_; lean_object* v_usedQuotCtxts_1403_; lean_object* v_nextMacroScope_1404_; lean_object* v_maxRecDepth_1405_; lean_object* v_ngen_1406_; lean_object* v_auxDeclNGen_1407_; lean_object* v_infoState_1408_; lean_object* v_snapshotTasks_1409_; lean_object* v_prevLinterStates_1410_; lean_object* v_codeQualityEntryTasks_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1421_; 
v___x_1399_ = lean_st_ref_take(v_a_1395_);
v_env_1400_ = lean_ctor_get(v___x_1399_, 0);
v_messages_1401_ = lean_ctor_get(v___x_1399_, 1);
v_scopes_1402_ = lean_ctor_get(v___x_1399_, 2);
v_usedQuotCtxts_1403_ = lean_ctor_get(v___x_1399_, 3);
v_nextMacroScope_1404_ = lean_ctor_get(v___x_1399_, 4);
v_maxRecDepth_1405_ = lean_ctor_get(v___x_1399_, 5);
v_ngen_1406_ = lean_ctor_get(v___x_1399_, 6);
v_auxDeclNGen_1407_ = lean_ctor_get(v___x_1399_, 7);
v_infoState_1408_ = lean_ctor_get(v___x_1399_, 8);
v_snapshotTasks_1409_ = lean_ctor_get(v___x_1399_, 10);
v_prevLinterStates_1410_ = lean_ctor_get(v___x_1399_, 11);
v_codeQualityEntryTasks_1411_ = lean_ctor_get(v___x_1399_, 12);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1399_, 9);
lean_dec(v_unused_1422_);
v___x_1413_ = v___x_1399_;
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1411_);
lean_inc(v_prevLinterStates_1410_);
lean_inc(v_snapshotTasks_1409_);
lean_inc(v_infoState_1408_);
lean_inc(v_auxDeclNGen_1407_);
lean_inc(v_ngen_1406_);
lean_inc(v_maxRecDepth_1405_);
lean_inc(v_nextMacroScope_1404_);
lean_inc(v_usedQuotCtxts_1403_);
lean_inc(v_scopes_1402_);
lean_inc(v_messages_1401_);
lean_inc(v_env_1400_);
lean_dec(v___x_1399_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1421_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = lean_box(0);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 9, v_traceState_1396_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_env_1400_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_messages_1401_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_scopes_1402_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_usedQuotCtxts_1403_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_nextMacroScope_1404_);
lean_ctor_set(v_reuseFailAlloc_1420_, 5, v_maxRecDepth_1405_);
lean_ctor_set(v_reuseFailAlloc_1420_, 6, v_ngen_1406_);
lean_ctor_set(v_reuseFailAlloc_1420_, 7, v_auxDeclNGen_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 8, v_infoState_1408_);
lean_ctor_set(v_reuseFailAlloc_1420_, 9, v_traceState_1396_);
lean_ctor_set(v_reuseFailAlloc_1420_, 10, v_snapshotTasks_1409_);
lean_ctor_set(v_reuseFailAlloc_1420_, 11, v_prevLinterStates_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 12, v_codeQualityEntryTasks_1411_);
v___x_1417_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_st_ref_put(v_a_1395_, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1415_);
return v___x_1419_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1395_ = stack[0].m_obj;
lean_object* v_traceState_1396_ = stack[1].m_obj;
lean_object* v_a_x3f_1397_ = stack[2].m_obj;
lean_object* v_res_1423_;
v_res_1423_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1395_, v_traceState_1396_, v_a_x3f_1397_);
stack->m_obj
 = v_res_1423_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1___boxed(lean_object* v_a_1424_, lean_object* v_traceState_1425_, lean_object* v_a_x3f_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1424_, v_traceState_1425_, v_a_x3f_1426_);
lean_dec(v_a_x3f_1426_);
lean_dec(v_a_1424_);
return v_res_1428_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(lean_object* v_a_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_apply_4(v_a_1429_, v___y_1430_, v___y_1431_, v___y_1432_, lean_box(0));
return v___x_1434_;
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1429_ = stack[0].m_obj;
lean_object* v___y_1430_ = stack[1].m_obj;
lean_object* v___y_1431_ = stack[2].m_obj;
lean_object* v___y_1432_ = stack[3].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(v_a_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed(lean_object* v_a_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(v_a_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
return v_res_1441_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object* v_post_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___f_1446_; lean_object* v___x_1447_; lean_object* v_traceState_1448_; lean_object* v_r_1449_; 
v___f_1446_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1446_, 0, v_post_1442_);
v___x_1447_ = lean_st_ref_get(v_a_1444_);
v_traceState_1448_ = lean_ctor_get(v___x_1447_, 9);
lean_inc_ref(v_traceState_1448_);
lean_dec(v___x_1447_);
v_r_1449_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_1446_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v_r_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1467_; 
v_a_1450_ = lean_ctor_get(v_r_1449_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_r_1449_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1452_ = v_r_1449_;
v_isShared_1453_ = v_isSharedCheck_1467_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v_r_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1467_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___f_1454_; lean_object* v___x_1456_; 
lean_inc(v_a_1450_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed), 5, 1);
lean_closure_set(v___f_1454_, 0, v_a_1450_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1450_);
v___x_1456_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v___x_1457_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1444_, v_traceState_1448_, v___x_1456_);
lean_dec_ref(v___x_1456_);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v___x_1457_, 0);
lean_dec(v_unused_1465_);
v___x_1459_ = v___x_1457_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v___x_1457_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___f_1454_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___f_1454_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1468_ = lean_ctor_get(v_r_1449_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v_r_1449_, 1);
v___x_1469_ = lean_box(0);
v___x_1470_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1444_, v_traceState_1448_, v___x_1469_);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v___x_1470_, 0);
lean_dec(v_unused_1478_);
v___x_1472_ = v___x_1470_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v___x_1470_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 1);
lean_ctor_set(v___x_1472_, 0, v_a_1468_);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1468_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_post_1442_ = stack[0].m_obj;
lean_object* v_a_1443_ = stack[1].m_obj;
lean_object* v_a_1444_ = stack[2].m_obj;
lean_object* v_res_1479_;
v_res_1479_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1442_, v_a_1443_, v_a_1444_);
stack->m_obj
 = v_res_1479_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___boxed(lean_object* v_post_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1480_, v_a_1481_, v_a_1482_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
return v_res_1484_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
