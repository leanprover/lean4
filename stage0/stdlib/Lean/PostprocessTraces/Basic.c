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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(size_t v_sz_78_, size_t v_i_79_, lean_object* v_bs_80_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0___boxed(lean_object* v_sz_91_, lean_object* v_i_92_, lean_object* v_bs_93_){
_start:
{
size_t v_sz_boxed_94_; size_t v_i_boxed_95_; lean_object* v_res_96_; 
v_sz_boxed_94_ = lean_unbox_usize(v_sz_91_);
lean_dec(v_sz_91_);
v_i_boxed_95_ = lean_unbox_usize(v_i_92_);
lean_dec(v_i_92_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go_spec__0(v_sz_boxed_94_, v_i_boxed_95_, v_bs_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0(lean_object* v___y_97_){
_start:
{
lean_inc_ref(v___y_97_);
return v___y_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0___boxed(lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData___lam__0(v___y_98_);
lean_dec_ref(v___y_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_ofMessageData(lean_object* v_msg_101_){
_start:
{
lean_object* v___f_102_; lean_object* v___x_103_; 
v___f_102_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0));
v___x_103_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go(v___f_102_, v_msg_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(size_t v_sz_104_, size_t v_i_105_, lean_object* v_bs_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = lean_usize_dec_lt(v_i_105_, v_sz_104_);
if (v___x_107_ == 0)
{
return v_bs_106_;
}
else
{
lean_object* v_v_108_; lean_object* v___x_109_; lean_object* v_bs_x27_110_; lean_object* v___x_111_; size_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; 
v_v_108_ = lean_array_uget(v_bs_106_, v_i_105_);
v___x_109_ = lean_unsigned_to_nat(0u);
v_bs_x27_110_ = lean_array_uset(v_bs_106_, v_i_105_, v___x_109_);
v___x_111_ = l_Lean_PostprocessTraces_TraceTree_toMessageData(v_v_108_);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_add(v_i_105_, v___x_112_);
v___x_114_ = lean_array_uset(v_bs_x27_110_, v_i_105_, v___x_111_);
v_i_105_ = v___x_113_;
v_bs_106_ = v___x_114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_toMessageData(lean_object* v_x_116_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v_data_117_; lean_object* v_msg_118_; lean_object* v_children_119_; lean_object* v_wrap_120_; size_t v_sz_121_; size_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_data_117_ = lean_ctor_get(v_x_116_, 0);
lean_inc_ref(v_data_117_);
v_msg_118_ = lean_ctor_get(v_x_116_, 1);
lean_inc_ref(v_msg_118_);
v_children_119_ = lean_ctor_get(v_x_116_, 2);
lean_inc_ref(v_children_119_);
v_wrap_120_ = lean_ctor_get(v_x_116_, 3);
lean_inc_ref(v_wrap_120_);
lean_dec_ref_known(v_x_116_, 4);
v_sz_121_ = lean_array_size(v_children_119_);
v___x_122_ = ((size_t)0ULL);
v___x_123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_121_, v___x_122_, v_children_119_);
v___x_124_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_124_, 0, v_data_117_);
lean_ctor_set(v___x_124_, 1, v_msg_118_);
lean_ctor_set(v___x_124_, 2, v___x_123_);
v___x_125_ = lean_apply_1(v_wrap_120_, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v_msg_126_; 
v_msg_126_ = lean_ctor_get(v_x_116_, 0);
lean_inc_ref(v_msg_126_);
lean_dec_ref_known(v_x_116_, 1);
return v_msg_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0___boxed(lean_object* v_sz_127_, lean_object* v_i_128_, lean_object* v_bs_129_){
_start:
{
size_t v_sz_boxed_130_; size_t v_i_boxed_131_; lean_object* v_res_132_; 
v_sz_boxed_130_ = lean_unbox_usize(v_sz_127_);
lean_dec(v_sz_127_);
v_i_boxed_131_ = lean_unbox_usize(v_i_128_);
lean_dec(v_i_128_);
v_res_132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_boxed_130_, v_i_boxed_131_, v_bs_129_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(lean_object* v_roots_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v_roots_133_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0___boxed(lean_object* v_roots_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_PostprocessTraces_instInhabitedTracePostprocessor___lam__0(v_roots_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f(lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v_data_146_; lean_object* v___x_147_; 
v_data_146_ = lean_ctor_get(v_x_145_, 0);
lean_inc_ref(v_data_146_);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v_data_146_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_data_x3f___boxed(lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_x_149_);
lean_dec_ref(v_x_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f(lean_object* v_t_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_151_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_val_154_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v___x_152_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_val_154_);
lean_dec(v___x_152_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v_cls_158_; lean_object* v___x_160_; 
v_cls_158_ = lean_ctor_get(v_val_154_, 0);
lean_inc(v_cls_158_);
lean_dec(v_val_154_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v_cls_158_);
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_cls_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_cls_x3f___boxed(lean_object* v_t_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_163_);
lean_dec_ref(v_t_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children(lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v_children_168_; 
v_children_168_ = lean_ctor_get(v_x_167_, 2);
lean_inc_ref(v_children_168_);
return v_children_168_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_children___boxed(lean_object* v_x_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_PostprocessTraces_TraceTree_children(v_x_170_);
lean_dec_ref(v_x_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_withChildren(lean_object* v_t_172_, lean_object* v_children_173_){
_start:
{
if (lean_obj_tag(v_t_172_) == 0)
{
lean_object* v_data_174_; lean_object* v_msg_175_; lean_object* v_wrap_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_data_174_ = lean_ctor_get(v_t_172_, 0);
v_msg_175_ = lean_ctor_get(v_t_172_, 1);
v_wrap_176_ = lean_ctor_get(v_t_172_, 3);
v_isSharedCheck_183_ = !lean_is_exclusive(v_t_172_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_t_172_, 2);
lean_dec(v_unused_184_);
v___x_178_ = v_t_172_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_wrap_176_);
lean_inc(v_msg_175_);
lean_inc(v_data_174_);
lean_dec(v_t_172_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 2, v_children_173_);
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_data_174_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_msg_175_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_children_173_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_wrap_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_dec_ref(v_children_173_);
return v_t_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_modifyData(lean_object* v_t_185_, lean_object* v_f_186_){
_start:
{
if (lean_obj_tag(v_t_185_) == 0)
{
lean_object* v_data_187_; lean_object* v_msg_188_; lean_object* v_children_189_; lean_object* v_wrap_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_198_; 
v_data_187_ = lean_ctor_get(v_t_185_, 0);
v_msg_188_ = lean_ctor_get(v_t_185_, 1);
v_children_189_ = lean_ctor_get(v_t_185_, 2);
v_wrap_190_ = lean_ctor_get(v_t_185_, 3);
v_isSharedCheck_198_ = !lean_is_exclusive(v_t_185_);
if (v_isSharedCheck_198_ == 0)
{
v___x_192_ = v_t_185_;
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_wrap_190_);
lean_inc(v_children_189_);
lean_inc(v_msg_188_);
lean_inc(v_data_187_);
lean_dec(v_t_185_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_apply_1(v_f_186_, v_data_187_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_msg_188_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_children_189_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_wrap_190_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_dec_ref(v_f_186_);
return v_t_185_;
}
}
}
static double _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0(void){
_start:
{
lean_object* v___x_199_; double v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_float_of_nat(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_elapsed(lean_object* v_t_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
double v___x_203_; 
v___x_203_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
return v___x_203_;
}
else
{
lean_object* v_val_204_; double v_startTime_205_; double v_stopTime_206_; double v___x_207_; 
v_val_204_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_val_204_);
lean_dec_ref_known(v___x_202_, 1);
v_startTime_205_ = lean_ctor_get_float(v_val_204_, sizeof(void*)*3);
v_stopTime_206_ = lean_ctor_get_float(v_val_204_, sizeof(void*)*3 + 8);
lean_dec(v_val_204_);
v___x_207_ = lean_float_sub(v_stopTime_206_, v_startTime_205_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_elapsed___boxed(lean_object* v_t_208_){
_start:
{
double v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_208_);
lean_dec_ref(v_t_208_);
v_r_210_ = lean_box_float(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(lean_object* v_as_211_, size_t v_i_212_, size_t v_stop_213_, double v_b_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = lean_usize_dec_eq(v_i_212_, v_stop_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; double v___x_217_; double v___x_218_; size_t v___x_219_; size_t v___x_220_; 
v___x_216_ = lean_array_uget_borrowed(v_as_211_, v_i_212_);
v___x_217_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v___x_216_);
v___x_218_ = lean_float_add(v_b_214_, v___x_217_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_add(v_i_212_, v___x_219_);
v_i_212_ = v___x_220_;
v_b_214_ = v___x_218_;
goto _start;
}
else
{
return v_b_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0___boxed(lean_object* v_as_222_, lean_object* v_i_223_, lean_object* v_stop_224_, lean_object* v_b_225_){
_start:
{
size_t v_i_boxed_226_; size_t v_stop_boxed_227_; double v_b_boxed_228_; double v_res_229_; lean_object* v_r_230_; 
v_i_boxed_226_ = lean_unbox_usize(v_i_223_);
lean_dec(v_i_223_);
v_stop_boxed_227_ = lean_unbox_usize(v_stop_224_);
lean_dec(v_stop_224_);
v_b_boxed_228_ = lean_unbox_float(v_b_225_);
lean_dec_ref(v_b_225_);
v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v_as_222_, v_i_boxed_226_, v_stop_boxed_227_, v_b_boxed_228_);
lean_dec_ref(v_as_222_);
v_r_230_ = lean_box_float(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT double l_Lean_PostprocessTraces_TraceTree_selfElapsed(lean_object* v_t_231_){
_start:
{
lean_object* v___x_232_; double v___x_233_; double v___x_234_; double v___y_236_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_float_once(&l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0, &l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0_once, _init_l_Lean_PostprocessTraces_TraceTree_elapsed___closed__0);
v___x_234_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_231_);
v___x_239_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_231_);
v___x_240_ = lean_array_get_size(v___x_239_);
v___x_241_ = lean_nat_dec_lt(v___x_232_, v___x_240_);
if (v___x_241_ == 0)
{
lean_dec_ref(v___x_239_);
v___y_236_ = v___x_233_;
goto v___jp_235_;
}
else
{
size_t v___x_242_; size_t v___x_243_; double v___x_244_; 
v___x_242_ = ((size_t)0ULL);
v___x_243_ = lean_usize_of_nat(v___x_240_);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_239_, v___x_242_, v___x_243_, v___x_233_);
lean_dec_ref(v___x_239_);
v___y_236_ = v___x_244_;
goto v___jp_235_;
}
v___jp_235_:
{
double v___x_237_; double v___x_238_; 
v___x_237_ = lean_float_sub(v___x_234_, v___y_236_);
v___x_238_ = lean_float_maximum(v___x_233_, v___x_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_selfElapsed___boxed(lean_object* v_t_245_){
_start:
{
double v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_245_);
lean_dec_ref(v_t_245_);
v_r_247_ = lean_box_float(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText(lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v_data_251_; lean_object* v_msg_252_; lean_object* v_wrap_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_result_x3f_256_; 
v_data_251_ = lean_ctor_get(v_x_249_, 0);
lean_inc_ref(v_data_251_);
v_msg_252_ = lean_ctor_get(v_x_249_, 1);
lean_inc_ref(v_msg_252_);
v_wrap_253_ = lean_ctor_get(v_x_249_, 3);
lean_inc_ref(v_wrap_253_);
lean_dec_ref_known(v_x_249_, 4);
v___x_254_ = lean_apply_1(v_wrap_253_, v_msg_252_);
v___x_255_ = l_Lean_MessageData_toString(v___x_254_);
v_result_x3f_256_ = lean_ctor_get(v_data_251_, 1);
lean_inc(v_result_x3f_256_);
lean_dec_ref(v_data_251_);
if (lean_obj_tag(v_result_x3f_256_) == 0)
{
return v___x_255_;
}
else
{
lean_object* v_val_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_val_257_ = lean_ctor_get(v_result_x3f_256_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v_result_x3f_256_, 1);
v___x_258_ = lean_unbox(v_val_257_);
lean_dec(v_val_257_);
v___x_259_ = l_Lean_TraceResult_toEmoji(v___x_258_);
v___x_260_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_headText___closed__0));
v___x_261_ = lean_string_append(v___x_259_, v___x_260_);
v___x_262_ = lean_string_append(v___x_261_, v___x_255_);
lean_dec_ref(v___x_255_);
return v___x_262_;
}
}
else
{
lean_object* v_msg_263_; lean_object* v___x_264_; 
v_msg_263_ = lean_ctor_get(v_x_249_, 0);
lean_inc_ref(v_msg_263_);
lean_dec_ref_known(v_x_249_, 1);
v___x_264_ = l_Lean_MessageData_toString(v_msg_263_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText___boxed(lean_object* v_x_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_PostprocessTraces_TraceTree_headText(v_x_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f(lean_object* v_t_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_268_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_box(0);
return v___x_270_;
}
else
{
lean_object* v_val_271_; lean_object* v_result_x3f_272_; 
v_val_271_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_val_271_);
lean_dec_ref_known(v___x_269_, 1);
v_result_x3f_272_ = lean_ctor_get(v_val_271_, 1);
lean_inc(v_result_x3f_272_);
lean_dec(v_val_271_);
return v_result_x3f_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f___boxed(lean_object* v_t_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_273_);
lean_dec_ref(v_t_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees(lean_object* v_p_275_, lean_object* v_t_276_, lean_object* v_acc_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_281_; 
lean_inc_ref(v_p_275_);
lean_inc(v_a_279_);
lean_inc_ref(v_a_278_);
lean_inc_ref(v_t_276_);
v___x_281_ = lean_apply_4(v_p_275_, v_t_276_, v_a_278_, v_a_279_, lean_box(0));
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_301_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_301_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_301_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_301_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
uint8_t v___x_286_; 
v___x_286_ = lean_unbox(v_a_282_);
lean_dec(v_a_282_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_287_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_276_);
lean_dec_ref(v_t_276_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_array_get_size(v___x_287_);
v___x_290_ = lean_nat_dec_lt(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_292_; 
lean_dec_ref(v___x_287_);
lean_dec_ref(v_p_275_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_acc_277_);
v___x_292_ = v___x_284_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_acc_277_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; 
lean_del_object(v___x_284_);
v___x_294_ = ((size_t)0ULL);
v___x_295_ = lean_usize_of_nat(v___x_289_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_275_, v___x_287_, v___x_294_, v___x_295_, v_acc_277_, v_a_278_, v_a_279_);
lean_dec_ref(v___x_287_);
return v___x_296_;
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec_ref(v_p_275_);
v___x_297_ = lean_array_push(v_acc_277_, v_t_276_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_297_);
v___x_299_ = v___x_284_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v_acc_277_);
lean_dec_ref(v_t_276_);
lean_dec_ref(v_p_275_);
v_a_302_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_281_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_281_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(lean_object* v_p_310_, lean_object* v_as_311_, size_t v_i_312_, size_t v_stop_313_, lean_object* v_b_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = lean_usize_dec_eq(v_i_312_, v_stop_313_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_array_uget_borrowed(v_as_311_, v_i_312_);
lean_inc(v___x_319_);
lean_inc_ref(v_p_310_);
v___x_320_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_310_, v___x_319_, v_b_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; size_t v___x_322_; size_t v___x_323_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = ((size_t)1ULL);
v___x_323_ = lean_usize_add(v_i_312_, v___x_322_);
v_i_312_ = v___x_323_;
v_b_314_ = v_a_321_;
goto _start;
}
else
{
lean_dec_ref(v_p_310_);
return v___x_320_;
}
}
else
{
lean_object* v___x_325_; 
lean_dec_ref(v_p_310_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_b_314_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0___boxed(lean_object* v_p_326_, lean_object* v_as_327_, lean_object* v_i_328_, lean_object* v_stop_329_, lean_object* v_b_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
size_t v_i_boxed_334_; size_t v_stop_boxed_335_; lean_object* v_res_336_; 
v_i_boxed_334_ = lean_unbox_usize(v_i_328_);
lean_dec(v_i_328_);
v_stop_boxed_335_ = lean_unbox_usize(v_stop_329_);
lean_dec(v_stop_329_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_326_, v_as_327_, v_i_boxed_334_, v_stop_boxed_335_, v_b_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec_ref(v_as_327_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees___boxed(lean_object* v_p_337_, lean_object* v_t_338_, lean_object* v_acc_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_337_, v_t_338_, v_acc_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(lean_object* v_p_344_, lean_object* v_as_345_, lean_object* v_start_346_, lean_object* v_stop_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
v___x_352_ = lean_nat_dec_lt(v_start_346_, v_stop_347_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
lean_dec_ref(v_p_344_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_array_get_size(v_as_345_);
v___x_355_ = lean_nat_dec_le(v_stop_347_, v___x_354_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
v___x_356_ = lean_nat_dec_lt(v_start_346_, v___x_354_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec_ref(v_p_344_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_351_);
return v___x_357_;
}
else
{
size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_usize_of_nat(v_start_346_);
v___x_359_ = lean_usize_of_nat(v___x_354_);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_344_, v_as_345_, v___x_358_, v___x_359_, v___x_351_, v___y_348_, v___y_349_);
return v___x_360_;
}
}
else
{
size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_usize_of_nat(v_start_346_);
v___x_362_ = lean_usize_of_nat(v_stop_347_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_344_, v_as_345_, v___x_361_, v___x_362_, v___x_351_, v___y_348_, v___y_349_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees(lean_object* v_p_364_, lean_object* v_t_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
lean_inc_ref(v_p_364_);
lean_inc(v_a_367_);
lean_inc_ref(v_a_366_);
lean_inc_ref(v_t_365_);
v___x_369_ = lean_apply_4(v_p_364_, v_t_365_, v_a_366_, v_a_367_, lean_box(0));
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_407_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_407_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_407_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_407_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = lean_unbox(v_a_370_);
lean_dec(v_a_370_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_del_object(v___x_372_);
v___x_375_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_365_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_array_get_size(v___x_375_);
v___x_378_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_364_, v___x_375_, v___x_376_, v___x_377_, v_a_366_, v_a_367_);
lean_dec_ref(v___x_375_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_394_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_394_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_394_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_394_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_array_get_size(v_a_379_);
v___x_384_ = lean_nat_dec_eq(v___x_383_, v___x_376_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_365_, v_a_379_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_386_);
v___x_388_ = v___x_381_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_392_; 
lean_dec(v_a_379_);
lean_dec_ref(v_t_365_);
v___x_390_ = lean_box(0);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_390_);
v___x_392_ = v___x_381_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_t_365_);
v_a_395_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_378_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_378_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_405_; 
lean_dec_ref(v_p_364_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v_t_365_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_403_);
v___x_405_ = v___x_372_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_t_365_);
lean_dec_ref(v_p_364_);
v_a_408_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_369_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_369_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(lean_object* v_p_416_, lean_object* v_as_417_, size_t v_i_418_, size_t v_stop_419_, lean_object* v_b_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_a_425_; uint8_t v___x_429_; 
v___x_429_ = lean_usize_dec_eq(v_i_418_, v_stop_419_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_array_uget_borrowed(v_as_417_, v_i_418_);
lean_inc(v___x_430_);
lean_inc_ref(v_p_416_);
v___x_431_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_416_, v___x_430_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
if (lean_obj_tag(v_a_432_) == 0)
{
v_a_425_ = v_b_420_;
goto v___jp_424_;
}
else
{
lean_object* v_val_433_; lean_object* v___x_434_; 
v_val_433_ = lean_ctor_get(v_a_432_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v_a_432_, 1);
v___x_434_ = lean_array_push(v_b_420_, v_val_433_);
v_a_425_ = v___x_434_;
goto v___jp_424_;
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec_ref(v_b_420_);
lean_dec_ref(v_p_416_);
v_a_435_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_431_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_431_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
lean_object* v___x_443_; 
lean_dec_ref(v_p_416_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v_b_420_);
return v___x_443_;
}
v___jp_424_:
{
size_t v___x_426_; size_t v___x_427_; 
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_add(v_i_418_, v___x_426_);
v_i_418_ = v___x_427_;
v_b_420_ = v_a_425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0___boxed(lean_object* v_p_444_, lean_object* v_as_445_, lean_object* v_i_446_, lean_object* v_stop_447_, lean_object* v_b_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
size_t v_i_boxed_452_; size_t v_stop_boxed_453_; lean_object* v_res_454_; 
v_i_boxed_452_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_stop_boxed_453_ = lean_unbox_usize(v_stop_447_);
lean_dec(v_stop_447_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_444_, v_as_445_, v_i_boxed_452_, v_stop_boxed_453_, v_b_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec_ref(v_as_445_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0___boxed(lean_object* v_p_455_, lean_object* v_as_456_, lean_object* v_start_457_, lean_object* v_stop_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_455_, v_as_456_, v_start_457_, v_stop_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v_stop_458_);
lean_dec(v_start_457_);
lean_dec_ref(v_as_456_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees___boxed(lean_object* v_p_463_, lean_object* v_t_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_463_, v_t_464_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2(lean_object* v_data_469_, lean_object* v_msg_470_, lean_object* v_a_471_, lean_object* v_wrap_472_, lean_object* v_children_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_474_, 0, v_data_469_);
lean_ctor_set(v___x_474_, 1, v_msg_470_);
lean_ctor_set(v___x_474_, 2, v_children_473_);
v___x_475_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_475_, 0, v_a_471_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = lean_apply_1(v_wrap_472_, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(lean_object* v_wrap_480_, lean_object* v_a_481_){
_start:
{
switch(lean_obj_tag(v_a_481_))
{
case 3:
{
lean_object* v_a_482_; lean_object* v_a_483_; lean_object* v___f_484_; 
v_a_482_ = lean_ctor_get(v_a_481_, 0);
lean_inc_ref(v_a_482_);
v_a_483_ = lean_ctor_get(v_a_481_, 1);
lean_inc_ref(v_a_483_);
lean_dec_ref_known(v_a_481_, 2);
v___f_484_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0), 3, 2);
lean_closure_set(v___f_484_, 0, v_a_482_);
lean_closure_set(v___f_484_, 1, v_wrap_480_);
v_wrap_480_ = v___f_484_;
v_a_481_ = v_a_483_;
goto _start;
}
case 4:
{
lean_object* v_a_486_; lean_object* v_a_487_; lean_object* v___f_488_; 
v_a_486_ = lean_ctor_get(v_a_481_, 0);
lean_inc_ref(v_a_486_);
v_a_487_ = lean_ctor_get(v_a_481_, 1);
lean_inc_ref(v_a_487_);
lean_dec_ref_known(v_a_481_, 2);
v___f_488_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1), 3, 2);
lean_closure_set(v___f_488_, 0, v_a_486_);
lean_closure_set(v___f_488_, 1, v_wrap_480_);
v_wrap_480_ = v___f_488_;
v_a_481_ = v_a_487_;
goto _start;
}
case 8:
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v_a_481_, 1);
lean_inc_ref(v_a_490_);
if (lean_obj_tag(v_a_490_) == 9)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_506_; 
v_a_491_ = lean_ctor_get(v_a_481_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_a_481_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_a_481_, 1);
lean_dec(v_unused_507_);
v___x_493_ = v_a_481_;
v_isShared_494_ = v_isSharedCheck_506_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v_a_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_506_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_data_495_; lean_object* v_msg_496_; lean_object* v_children_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_data_495_ = lean_ctor_get(v_a_490_, 0);
lean_inc_ref(v_data_495_);
v_msg_496_ = lean_ctor_get(v_a_490_, 1);
lean_inc_ref(v_msg_496_);
v_children_497_ = lean_ctor_get(v_a_490_, 2);
lean_inc_ref(v_children_497_);
lean_dec_ref_known(v_a_490_, 3);
v___x_498_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__1));
v___x_499_ = lean_name_eq(v_a_491_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec_ref(v_children_497_);
lean_dec_ref(v_msg_496_);
lean_dec_ref(v_data_495_);
lean_del_object(v___x_493_);
lean_dec(v_a_491_);
lean_dec_ref(v_wrap_480_);
v___x_500_ = lean_box(0);
return v___x_500_;
}
else
{
lean_object* v___f_501_; lean_object* v___x_503_; 
v___f_501_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2), 5, 4);
lean_closure_set(v___f_501_, 0, v_data_495_);
lean_closure_set(v___f_501_, 1, v_msg_496_);
lean_closure_set(v___f_501_, 2, v_a_491_);
lean_closure_set(v___f_501_, 3, v_wrap_480_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 0);
lean_ctor_set(v___x_493_, 1, v_children_497_);
lean_ctor_set(v___x_493_, 0, v___f_501_);
v___x_503_ = v___x_493_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___f_501_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_children_497_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
}
else
{
lean_object* v___x_508_; 
lean_dec_ref_known(v_a_481_, 2);
lean_dec_ref(v_a_490_);
lean_dec_ref(v_wrap_480_);
v___x_508_ = lean_box(0);
return v___x_508_;
}
}
default: 
{
lean_object* v___x_509_; 
lean_dec_ref(v_a_481_);
lean_dec_ref(v_wrap_480_);
v___x_509_ = lean_box(0);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_traceContainer_x3f(lean_object* v_data_510_){
_start:
{
lean_object* v___f_511_; lean_object* v___x_512_; 
v___f_511_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0));
v___x_512_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(v___f_511_, v_data_510_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(size_t v_sz_513_, size_t v_i_514_, lean_object* v_bs_515_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = lean_usize_dec_lt(v_i_514_, v_sz_513_);
if (v___x_516_ == 0)
{
return v_bs_515_;
}
else
{
lean_object* v_v_517_; lean_object* v___x_518_; lean_object* v_bs_x27_519_; lean_object* v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v_v_517_ = lean_array_uget(v_bs_515_, v_i_514_);
v___x_518_ = lean_unsigned_to_nat(0u);
v_bs_x27_519_ = lean_array_uset(v_bs_515_, v_i_514_, v___x_518_);
v___x_520_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData(v_v_517_);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_514_, v___x_521_);
v___x_523_ = lean_array_uset(v_bs_x27_519_, v_i_514_, v___x_520_);
v_i_514_ = v___x_522_;
v_bs_515_ = v___x_523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0___boxed(lean_object* v_sz_525_, lean_object* v_i_526_, lean_object* v_bs_527_){
_start:
{
size_t v_sz_boxed_528_; size_t v_i_boxed_529_; lean_object* v_res_530_; 
v_sz_boxed_528_ = lean_unbox_usize(v_sz_525_);
lean_dec(v_sz_525_);
v_i_boxed_529_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_boxed_528_, v_i_boxed_529_, v_bs_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage(lean_object* v_post_531_, lean_object* v_msg_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_fileName_536_; lean_object* v_pos_537_; lean_object* v_endPos_538_; uint8_t v_keepFullRange_539_; uint8_t v_severity_540_; uint8_t v_isSilent_541_; lean_object* v_caption_542_; lean_object* v_data_543_; lean_object* v___x_544_; 
v_fileName_536_ = lean_ctor_get(v_msg_532_, 0);
v_pos_537_ = lean_ctor_get(v_msg_532_, 1);
v_endPos_538_ = lean_ctor_get(v_msg_532_, 2);
v_keepFullRange_539_ = lean_ctor_get_uint8(v_msg_532_, sizeof(void*)*5);
v_severity_540_ = lean_ctor_get_uint8(v_msg_532_, sizeof(void*)*5 + 1);
v_isSilent_541_ = lean_ctor_get_uint8(v_msg_532_, sizeof(void*)*5 + 2);
v_caption_542_ = lean_ctor_get(v_msg_532_, 3);
v_data_543_ = lean_ctor_get(v_msg_532_, 4);
lean_inc(v_data_543_);
v___x_544_ = l_Lean_Elab_PostprocessTraces_traceContainer_x3f(v_data_543_);
if (lean_obj_tag(v___x_544_) == 1)
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_591_; 
lean_inc_ref(v_caption_542_);
lean_inc(v_endPos_538_);
lean_inc_ref(v_pos_537_);
lean_inc_ref(v_fileName_536_);
v_isSharedCheck_591_ = !lean_is_exclusive(v_msg_532_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; lean_object* v_unused_593_; lean_object* v_unused_594_; lean_object* v_unused_595_; lean_object* v_unused_596_; 
v_unused_592_ = lean_ctor_get(v_msg_532_, 4);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_msg_532_, 3);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_msg_532_, 2);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_msg_532_, 1);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_msg_532_, 0);
lean_dec(v_unused_596_);
v___x_546_ = v_msg_532_;
v_isShared_547_ = v_isSharedCheck_591_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_msg_532_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_591_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_590_; 
v_val_548_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_590_ == 0)
{
v___x_550_ = v___x_544_;
v_isShared_551_ = v_isSharedCheck_590_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v___x_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_590_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_fst_552_; lean_object* v_snd_553_; size_t v_sz_554_; size_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_fst_552_ = lean_ctor_get(v_val_548_, 0);
lean_inc(v_fst_552_);
v_snd_553_ = lean_ctor_get(v_val_548_, 1);
lean_inc(v_snd_553_);
lean_dec(v_val_548_);
v_sz_554_ = lean_array_size(v_snd_553_);
v___x_555_ = ((size_t)0ULL);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_554_, v___x_555_, v_snd_553_);
lean_inc(v_a_534_);
lean_inc_ref(v_a_533_);
v___x_557_ = lean_apply_4(v_post_531_, v___x_556_, v_a_533_, v_a_534_, lean_box(0));
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_581_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_581_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_581_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_581_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_562_ = lean_array_get_size(v_a_558_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_nat_dec_eq(v___x_562_, v___x_563_);
if (v___x_564_ == 0)
{
size_t v_sz_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v_sz_565_ = lean_array_size(v_a_558_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_565_, v___x_555_, v_a_558_);
v___x_567_ = lean_apply_1(v_fst_552_, v___x_566_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 4, v___x_567_);
v___x_569_ = v___x_546_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_fileName_536_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_pos_537_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_endPos_538_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_caption_542_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v___x_567_);
lean_ctor_set_uint8(v_reuseFailAlloc_576_, sizeof(void*)*5, v_keepFullRange_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_576_, sizeof(void*)*5 + 1, v_severity_540_);
lean_ctor_set_uint8(v_reuseFailAlloc_576_, sizeof(void*)*5 + 2, v_isSilent_541_);
v___x_569_ = v_reuseFailAlloc_576_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_569_);
v___x_571_ = v___x_550_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_575_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_573_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_571_);
v___x_573_ = v___x_560_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_579_; 
lean_dec(v_a_558_);
lean_dec(v_fst_552_);
lean_del_object(v___x_550_);
lean_del_object(v___x_546_);
lean_dec_ref(v_caption_542_);
lean_dec(v_endPos_538_);
lean_dec_ref(v_pos_537_);
lean_dec_ref(v_fileName_536_);
v___x_577_ = lean_box(0);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_577_);
v___x_579_ = v___x_560_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_fst_552_);
lean_del_object(v___x_550_);
lean_del_object(v___x_546_);
lean_dec_ref(v_caption_542_);
lean_dec(v_endPos_538_);
lean_dec_ref(v_pos_537_);
lean_dec_ref(v_fileName_536_);
v_a_582_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_557_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_557_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v___x_544_);
lean_dec_ref(v_post_531_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_msg_532_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed(lean_object* v_post_599_, lean_object* v_msg_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Elab_PostprocessTraces_postprocessMessage(v_post_599_, v_msg_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(lean_object* v_a_605_, lean_object* v_messages_606_, lean_object* v_trees_607_, lean_object* v_a_x3f_608_){
_start:
{
lean_object* v___x_610_; lean_object* v_infoState_611_; lean_object* v_env_612_; lean_object* v_messages_613_; lean_object* v_scopes_614_; lean_object* v_usedQuotCtxts_615_; lean_object* v_nextMacroScope_616_; lean_object* v_maxRecDepth_617_; lean_object* v_ngen_618_; lean_object* v_auxDeclNGen_619_; lean_object* v_traceState_620_; lean_object* v_snapshotTasks_621_; lean_object* v_prevLinterStates_622_; lean_object* v_codeQualityEntryTasks_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_646_; 
v___x_610_ = lean_st_ref_take(v_a_605_);
v_infoState_611_ = lean_ctor_get(v___x_610_, 8);
v_env_612_ = lean_ctor_get(v___x_610_, 0);
v_messages_613_ = lean_ctor_get(v___x_610_, 1);
v_scopes_614_ = lean_ctor_get(v___x_610_, 2);
v_usedQuotCtxts_615_ = lean_ctor_get(v___x_610_, 3);
v_nextMacroScope_616_ = lean_ctor_get(v___x_610_, 4);
v_maxRecDepth_617_ = lean_ctor_get(v___x_610_, 5);
v_ngen_618_ = lean_ctor_get(v___x_610_, 6);
v_auxDeclNGen_619_ = lean_ctor_get(v___x_610_, 7);
v_traceState_620_ = lean_ctor_get(v___x_610_, 9);
v_snapshotTasks_621_ = lean_ctor_get(v___x_610_, 10);
v_prevLinterStates_622_ = lean_ctor_get(v___x_610_, 11);
v_codeQualityEntryTasks_623_ = lean_ctor_get(v___x_610_, 12);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_646_ == 0)
{
v___x_625_ = v___x_610_;
v_isShared_626_ = v_isSharedCheck_646_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_codeQualityEntryTasks_623_);
lean_inc(v_prevLinterStates_622_);
lean_inc(v_snapshotTasks_621_);
lean_inc(v_traceState_620_);
lean_inc(v_infoState_611_);
lean_inc(v_auxDeclNGen_619_);
lean_inc(v_ngen_618_);
lean_inc(v_maxRecDepth_617_);
lean_inc(v_nextMacroScope_616_);
lean_inc(v_usedQuotCtxts_615_);
lean_inc(v_scopes_614_);
lean_inc(v_messages_613_);
lean_inc(v_env_612_);
lean_dec(v___x_610_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_646_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v_enabled_627_; lean_object* v_assignment_628_; lean_object* v_lazyAssignment_629_; lean_object* v_trees_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_645_; 
v_enabled_627_ = lean_ctor_get_uint8(v_infoState_611_, sizeof(void*)*3);
v_assignment_628_ = lean_ctor_get(v_infoState_611_, 0);
v_lazyAssignment_629_ = lean_ctor_get(v_infoState_611_, 1);
v_trees_630_ = lean_ctor_get(v_infoState_611_, 2);
v_isSharedCheck_645_ = !lean_is_exclusive(v_infoState_611_);
if (v_isSharedCheck_645_ == 0)
{
v___x_632_ = v_infoState_611_;
v_isShared_633_ = v_isSharedCheck_645_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_trees_630_);
lean_inc(v_lazyAssignment_629_);
lean_inc(v_assignment_628_);
lean_dec(v_infoState_611_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_645_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_634_ = lean_box(0);
v___x_635_ = l_Lean_MessageLog_append(v_messages_606_, v_messages_613_);
v___x_636_ = l_Lean_PersistentArray_append___redArg(v_trees_607_, v_trees_630_);
lean_dec_ref(v_trees_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 2, v___x_636_);
v___x_638_ = v___x_632_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_assignment_628_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_lazyAssignment_629_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v___x_636_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*3, v_enabled_627_);
v___x_638_ = v_reuseFailAlloc_644_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 8, v___x_638_);
lean_ctor_set(v___x_625_, 1, v___x_635_);
v___x_640_ = v___x_625_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_env_612_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_scopes_614_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_usedQuotCtxts_615_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_nextMacroScope_616_);
lean_ctor_set(v_reuseFailAlloc_643_, 5, v_maxRecDepth_617_);
lean_ctor_set(v_reuseFailAlloc_643_, 6, v_ngen_618_);
lean_ctor_set(v_reuseFailAlloc_643_, 7, v_auxDeclNGen_619_);
lean_ctor_set(v_reuseFailAlloc_643_, 8, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_643_, 9, v_traceState_620_);
lean_ctor_set(v_reuseFailAlloc_643_, 10, v_snapshotTasks_621_);
lean_ctor_set(v_reuseFailAlloc_643_, 11, v_prevLinterStates_622_);
lean_ctor_set(v_reuseFailAlloc_643_, 12, v_codeQualityEntryTasks_623_);
v___x_640_ = v_reuseFailAlloc_643_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_st_ref_put(v_a_605_, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_634_);
return v___x_642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0___boxed(lean_object* v_a_647_, lean_object* v_messages_648_, lean_object* v_trees_649_, lean_object* v_a_x3f_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_647_, v_messages_648_, v_trees_649_, v_a_x3f_650_);
lean_dec(v_a_x3f_650_);
lean_dec(v_a_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(lean_object* v_as_653_, size_t v_i_654_, size_t v_stop_655_, lean_object* v_b_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_eq(v_i_654_, v_stop_655_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v_diagnostics_659_; lean_object* v_msgLog_660_; lean_object* v___x_661_; size_t v___x_662_; size_t v___x_663_; 
v___x_658_ = lean_array_uget_borrowed(v_as_653_, v_i_654_);
v_diagnostics_659_ = lean_ctor_get(v___x_658_, 1);
v_msgLog_660_ = lean_ctor_get(v_diagnostics_659_, 0);
lean_inc_ref(v_msgLog_660_);
v___x_661_ = l_Lean_MessageLog_append(v_b_656_, v_msgLog_660_);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_add(v_i_654_, v___x_662_);
v_i_654_ = v___x_663_;
v_b_656_ = v___x_661_;
goto _start;
}
else
{
return v_b_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0___boxed(lean_object* v_as_665_, lean_object* v_i_666_, lean_object* v_stop_667_, lean_object* v_b_668_){
_start:
{
size_t v_i_boxed_669_; size_t v_stop_boxed_670_; lean_object* v_res_671_; 
v_i_boxed_669_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_stop_boxed_670_ = lean_unbox_usize(v_stop_667_);
lean_dec(v_stop_667_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v_as_665_, v_i_boxed_669_, v_stop_boxed_670_, v_b_668_);
lean_dec_ref(v_as_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(lean_object* v_as_672_, size_t v_i_673_, size_t v_stop_674_, lean_object* v_b_675_){
_start:
{
lean_object* v___y_677_; uint8_t v___x_681_; 
v___x_681_ = lean_usize_dec_eq(v_i_673_, v_stop_674_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_682_ = lean_array_uget_borrowed(v_as_672_, v_i_673_);
v___x_683_ = l_Lean_MessageLog_empty;
lean_inc(v___x_682_);
v___x_684_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_682_);
v___x_685_ = l_Lean_Language_SnapshotTree_getAll(v___x_684_);
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v___x_685_);
v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec_ref(v___x_685_);
v___x_689_ = l_Lean_MessageLog_append(v_b_675_, v___x_683_);
v___y_677_ = v___x_689_;
goto v___jp_676_;
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_687_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__0(v___x_685_, v___x_690_, v___x_691_, v___x_683_);
lean_dec_ref(v___x_685_);
v___x_693_ = l_Lean_MessageLog_append(v_b_675_, v___x_692_);
v___y_677_ = v___x_693_;
goto v___jp_676_;
}
}
else
{
return v_b_675_;
}
v___jp_676_:
{
size_t v___x_678_; size_t v___x_679_; 
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_673_, v___x_678_);
v_i_673_ = v___x_679_;
v_b_675_ = v___y_677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1___boxed(lean_object* v_as_694_, lean_object* v_i_695_, lean_object* v_stop_696_, lean_object* v_b_697_){
_start:
{
size_t v_i_boxed_698_; size_t v_stop_boxed_699_; lean_object* v_res_700_; 
v_i_boxed_698_ = lean_unbox_usize(v_i_695_);
lean_dec(v_i_695_);
v_stop_boxed_699_ = lean_unbox_usize(v_stop_696_);
lean_dec(v_stop_696_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_as_694_, v_i_boxed_698_, v_stop_boxed_699_, v_b_697_);
lean_dec_ref(v_as_694_);
return v_res_700_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(32u);
v___x_702_ = lean_mk_empty_array_with_capacity(v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1(void){
_start:
{
size_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_704_ = ((size_t)5ULL);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_unsigned_to_nat(32u);
v___x_707_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_708_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__0);
v___x_709_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_707_);
lean_ctor_set(v___x_709_, 2, v___x_705_);
lean_ctor_set(v___x_709_, 3, v___x_705_);
lean_ctor_set_usize(v___x_709_, 4, v___x_704_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = l_Lean_NameSet_empty;
v___x_711_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__1);
v___x_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_ctor_set(v___x_712_, 2, v___x_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object* v_cmd_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; lean_object* v_messages_720_; lean_object* v___x_721_; lean_object* v_infoState_722_; lean_object* v_trees_723_; lean_object* v___x_724_; lean_object* v_env_725_; lean_object* v_scopes_726_; lean_object* v_usedQuotCtxts_727_; lean_object* v_nextMacroScope_728_; lean_object* v_maxRecDepth_729_; lean_object* v_ngen_730_; lean_object* v_auxDeclNGen_731_; lean_object* v_infoState_732_; lean_object* v_traceState_733_; lean_object* v_snapshotTasks_734_; lean_object* v_prevLinterStates_735_; lean_object* v_codeQualityEntryTasks_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_825_; 
v___x_719_ = lean_st_ref_get(v_a_717_);
v_messages_720_ = lean_ctor_get(v___x_719_, 1);
lean_inc_ref(v_messages_720_);
lean_dec(v___x_719_);
v___x_721_ = lean_st_ref_get(v_a_717_);
v_infoState_722_ = lean_ctor_get(v___x_721_, 8);
lean_inc_ref(v_infoState_722_);
lean_dec(v___x_721_);
v_trees_723_ = lean_ctor_get(v_infoState_722_, 2);
lean_inc_ref(v_trees_723_);
lean_dec_ref(v_infoState_722_);
v___x_724_ = lean_st_ref_take(v_a_717_);
v_env_725_ = lean_ctor_get(v___x_724_, 0);
v_scopes_726_ = lean_ctor_get(v___x_724_, 2);
v_usedQuotCtxts_727_ = lean_ctor_get(v___x_724_, 3);
v_nextMacroScope_728_ = lean_ctor_get(v___x_724_, 4);
v_maxRecDepth_729_ = lean_ctor_get(v___x_724_, 5);
v_ngen_730_ = lean_ctor_get(v___x_724_, 6);
v_auxDeclNGen_731_ = lean_ctor_get(v___x_724_, 7);
v_infoState_732_ = lean_ctor_get(v___x_724_, 8);
v_traceState_733_ = lean_ctor_get(v___x_724_, 9);
v_snapshotTasks_734_ = lean_ctor_get(v___x_724_, 10);
v_prevLinterStates_735_ = lean_ctor_get(v___x_724_, 11);
v_codeQualityEntryTasks_736_ = lean_ctor_get(v___x_724_, 12);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_724_, 1);
lean_dec(v_unused_826_);
v___x_738_ = v___x_724_;
v_isShared_739_ = v_isSharedCheck_825_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_codeQualityEntryTasks_736_);
lean_inc(v_prevLinterStates_735_);
lean_inc(v_snapshotTasks_734_);
lean_inc(v_traceState_733_);
lean_inc(v_infoState_732_);
lean_inc(v_auxDeclNGen_731_);
lean_inc(v_ngen_730_);
lean_inc(v_maxRecDepth_729_);
lean_inc(v_nextMacroScope_728_);
lean_inc(v_usedQuotCtxts_727_);
lean_inc(v_scopes_726_);
lean_inc(v_env_725_);
lean_dec(v___x_724_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_825_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_env_725_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_scopes_726_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_usedQuotCtxts_727_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v_nextMacroScope_728_);
lean_ctor_set(v_reuseFailAlloc_824_, 5, v_maxRecDepth_729_);
lean_ctor_set(v_reuseFailAlloc_824_, 6, v_ngen_730_);
lean_ctor_set(v_reuseFailAlloc_824_, 7, v_auxDeclNGen_731_);
lean_ctor_set(v_reuseFailAlloc_824_, 8, v_infoState_732_);
lean_ctor_set(v_reuseFailAlloc_824_, 9, v_traceState_733_);
lean_ctor_set(v_reuseFailAlloc_824_, 10, v_snapshotTasks_734_);
lean_ctor_set(v_reuseFailAlloc_824_, 11, v_prevLinterStates_735_);
lean_ctor_set(v_reuseFailAlloc_824_, 12, v_codeQualityEntryTasks_736_);
v___x_743_ = v_reuseFailAlloc_824_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v_fileName_745_; lean_object* v_fileMap_746_; lean_object* v_currRecDepth_747_; lean_object* v_cmdPos_748_; lean_object* v_macroStack_749_; lean_object* v_quotContext_x3f_750_; lean_object* v_currMacroScope_751_; lean_object* v_ref_752_; lean_object* v_cancelTk_x3f_753_; uint8_t v_suppressElabErrors_754_; uint8_t v_checkDeprecated_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_744_ = lean_st_ref_put(v_a_717_, v___x_743_);
v_fileName_745_ = lean_ctor_get(v_a_716_, 0);
v_fileMap_746_ = lean_ctor_get(v_a_716_, 1);
v_currRecDepth_747_ = lean_ctor_get(v_a_716_, 2);
v_cmdPos_748_ = lean_ctor_get(v_a_716_, 3);
v_macroStack_749_ = lean_ctor_get(v_a_716_, 4);
v_quotContext_x3f_750_ = lean_ctor_get(v_a_716_, 5);
v_currMacroScope_751_ = lean_ctor_get(v_a_716_, 6);
v_ref_752_ = lean_ctor_get(v_a_716_, 7);
v_cancelTk_x3f_753_ = lean_ctor_get(v_a_716_, 9);
v_suppressElabErrors_754_ = lean_ctor_get_uint8(v_a_716_, sizeof(void*)*10);
v_checkDeprecated_755_ = lean_ctor_get_uint8(v_a_716_, sizeof(void*)*10 + 1);
v___x_756_ = lean_box(0);
lean_inc(v_cancelTk_x3f_753_);
lean_inc(v_ref_752_);
lean_inc(v_currMacroScope_751_);
lean_inc(v_quotContext_x3f_750_);
lean_inc(v_macroStack_749_);
lean_inc(v_cmdPos_748_);
lean_inc(v_currRecDepth_747_);
lean_inc_ref(v_fileMap_746_);
lean_inc_ref(v_fileName_745_);
v___x_757_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_757_, 0, v_fileName_745_);
lean_ctor_set(v___x_757_, 1, v_fileMap_746_);
lean_ctor_set(v___x_757_, 2, v_currRecDepth_747_);
lean_ctor_set(v___x_757_, 3, v_cmdPos_748_);
lean_ctor_set(v___x_757_, 4, v_macroStack_749_);
lean_ctor_set(v___x_757_, 5, v_quotContext_x3f_750_);
lean_ctor_set(v___x_757_, 6, v_currMacroScope_751_);
lean_ctor_set(v___x_757_, 7, v_ref_752_);
lean_ctor_set(v___x_757_, 8, v___x_756_);
lean_ctor_set(v___x_757_, 9, v_cancelTk_x3f_753_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*10, v_suppressElabErrors_754_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*10 + 1, v_checkDeprecated_755_);
v___x_758_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_715_, v___x_757_, v_a_717_);
lean_dec_ref_known(v___x_757_, 10);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_812_; 
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v___x_758_, 0);
lean_dec(v_unused_813_);
v___x_760_ = v___x_758_;
v_isShared_761_ = v_isSharedCheck_812_;
goto v_resetjp_759_;
}
else
{
lean_dec(v___x_758_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_812_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_messages_764_; lean_object* v___y_766_; lean_object* v_snapshotTasks_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_762_ = lean_st_ref_get(v_a_717_);
v___x_763_ = lean_st_ref_get(v_a_717_);
v_messages_764_ = lean_ctor_get(v___x_762_, 1);
lean_inc_ref(v_messages_764_);
lean_dec(v___x_762_);
v_snapshotTasks_805_ = lean_ctor_get(v___x_763_, 10);
lean_inc_ref(v_snapshotTasks_805_);
lean_dec(v___x_763_);
v___x_806_ = l_Lean_MessageLog_empty;
v___x_807_ = lean_array_get_size(v_snapshotTasks_805_);
v___x_808_ = lean_nat_dec_lt(v___x_740_, v___x_807_);
if (v___x_808_ == 0)
{
lean_dec_ref(v_snapshotTasks_805_);
v___y_766_ = v___x_806_;
goto v___jp_765_;
}
else
{
size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((size_t)0ULL);
v___x_810_ = lean_usize_of_nat(v___x_807_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_805_, v___x_809_, v___x_810_, v___x_806_);
lean_dec_ref(v_snapshotTasks_805_);
v___y_766_ = v___x_811_;
goto v___jp_765_;
}
v___jp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_env_769_; lean_object* v_scopes_770_; lean_object* v_usedQuotCtxts_771_; lean_object* v_nextMacroScope_772_; lean_object* v_maxRecDepth_773_; lean_object* v_ngen_774_; lean_object* v_auxDeclNGen_775_; lean_object* v_infoState_776_; lean_object* v_traceState_777_; lean_object* v_prevLinterStates_778_; lean_object* v_codeQualityEntryTasks_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_802_; 
v___x_767_ = l_Lean_MessageLog_append(v_messages_764_, v___y_766_);
v___x_768_ = lean_st_ref_take(v_a_717_);
v_env_769_ = lean_ctor_get(v___x_768_, 0);
v_scopes_770_ = lean_ctor_get(v___x_768_, 2);
v_usedQuotCtxts_771_ = lean_ctor_get(v___x_768_, 3);
v_nextMacroScope_772_ = lean_ctor_get(v___x_768_, 4);
v_maxRecDepth_773_ = lean_ctor_get(v___x_768_, 5);
v_ngen_774_ = lean_ctor_get(v___x_768_, 6);
v_auxDeclNGen_775_ = lean_ctor_get(v___x_768_, 7);
v_infoState_776_ = lean_ctor_get(v___x_768_, 8);
v_traceState_777_ = lean_ctor_get(v___x_768_, 9);
v_prevLinterStates_778_ = lean_ctor_get(v___x_768_, 11);
v_codeQualityEntryTasks_779_ = lean_ctor_get(v___x_768_, 12);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; lean_object* v_unused_804_; 
v_unused_803_ = lean_ctor_get(v___x_768_, 10);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v___x_768_, 1);
lean_dec(v_unused_804_);
v___x_781_ = v___x_768_;
v_isShared_782_ = v_isSharedCheck_802_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_codeQualityEntryTasks_779_);
lean_inc(v_prevLinterStates_778_);
lean_inc(v_traceState_777_);
lean_inc(v_infoState_776_);
lean_inc(v_auxDeclNGen_775_);
lean_inc(v_ngen_774_);
lean_inc(v_maxRecDepth_773_);
lean_inc(v_nextMacroScope_772_);
lean_inc(v_usedQuotCtxts_771_);
lean_inc(v_scopes_770_);
lean_inc(v_env_769_);
lean_dec(v___x_768_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_802_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3));
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 10, v___x_783_);
lean_ctor_set(v___x_781_, 1, v___x_741_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_env_769_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_scopes_770_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_usedQuotCtxts_771_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v_nextMacroScope_772_);
lean_ctor_set(v_reuseFailAlloc_801_, 5, v_maxRecDepth_773_);
lean_ctor_set(v_reuseFailAlloc_801_, 6, v_ngen_774_);
lean_ctor_set(v_reuseFailAlloc_801_, 7, v_auxDeclNGen_775_);
lean_ctor_set(v_reuseFailAlloc_801_, 8, v_infoState_776_);
lean_ctor_set(v_reuseFailAlloc_801_, 9, v_traceState_777_);
lean_ctor_set(v_reuseFailAlloc_801_, 10, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_801_, 11, v_prevLinterStates_778_);
lean_ctor_set(v_reuseFailAlloc_801_, 12, v_codeQualityEntryTasks_779_);
v___x_785_ = v_reuseFailAlloc_801_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_786_ = lean_st_ref_put(v_a_717_, v___x_785_);
v___x_787_ = l_Lean_MessageLog_toArray(v___x_767_);
lean_dec_ref(v___x_767_);
lean_inc_ref(v___x_787_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_787_);
v___x_789_ = v___x_760_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_800_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_717_, v_messages_720_, v_trees_723_, v___x_790_);
lean_dec_ref_known(v___x_790_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_799_);
v___x_793_ = v___x_791_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_dec(v___x_791_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_787_);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_787_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
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
lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_a_814_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_758_, 1);
v___x_815_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_717_, v_messages_720_, v_trees_723_, v___x_756_);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_815_, 0);
lean_dec(v_unused_823_);
v___x_817_ = v___x_815_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_dec(v___x_815_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set_tag(v___x_817_, 1);
lean_ctor_set(v___x_817_, 0, v_a_814_);
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_814_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___boxed(lean_object* v_cmd_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v_cmd_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(lean_object* v_type_832_, lean_object* v_e_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
uint8_t v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; 
v___x_839_ = 1;
v___x_840_ = 1;
v___x_841_ = l_Lean_Meta_evalExpr___redArg(v_type_832_, v_e_833_, v___x_839_, v___x_840_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1___boxed(lean_object* v_type_842_, lean_object* v_e_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(v_type_842_, v_e_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(lean_object* v_e_850_, lean_object* v___y_851_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = l_Lean_Expr_hasMVar(v_e_850_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_e_850_);
return v___x_854_;
}
else
{
lean_object* v___x_855_; lean_object* v_mctx_856_; lean_object* v___x_857_; lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v___x_860_; lean_object* v_cache_861_; lean_object* v_zetaDeltaFVarIds_862_; lean_object* v_postponed_863_; lean_object* v_diag_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
v___x_855_ = lean_st_ref_get(v___y_851_);
v_mctx_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc_ref(v_mctx_856_);
lean_dec(v___x_855_);
v___x_857_ = l_Lean_instantiateMVarsCore(v_mctx_856_, v_e_850_);
v_fst_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_fst_858_);
v_snd_859_ = lean_ctor_get(v___x_857_, 1);
lean_inc(v_snd_859_);
lean_dec_ref(v___x_857_);
v___x_860_ = lean_st_ref_take(v___y_851_);
v_cache_861_ = lean_ctor_get(v___x_860_, 1);
v_zetaDeltaFVarIds_862_ = lean_ctor_get(v___x_860_, 2);
v_postponed_863_ = lean_ctor_get(v___x_860_, 3);
v_diag_864_ = lean_ctor_get(v___x_860_, 4);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v___x_860_, 0);
lean_dec(v_unused_874_);
v___x_866_ = v___x_860_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_diag_864_);
lean_inc(v_postponed_863_);
lean_inc(v_zetaDeltaFVarIds_862_);
lean_inc(v_cache_861_);
lean_dec(v___x_860_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_snd_859_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_snd_859_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_cache_861_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_zetaDeltaFVarIds_862_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_postponed_863_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v_diag_864_);
v___x_869_ = v_reuseFailAlloc_872_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_st_ref_put(v___y_851_, v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_fst_858_);
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg___boxed(lean_object* v_e_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_875_, v___y_876_);
lean_dec(v___y_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(lean_object* v_e_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_879_, v___y_883_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___boxed(lean_object* v_e_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(v_e_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_896_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(0);
v___x_898_ = l_Lean_Elab_abortTermExceptionId;
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg(){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___boxed(lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(lean_object* v_00_u03b1_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___boxed(lean_object* v_00_u03b1_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(v_00_u03b1_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(lean_object* v___x_923_, lean_object* v___x_924_, uint8_t v___x_925_, lean_object* v___x_926_, uint8_t v___x_927_, lean_object* v___x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_923_, v___x_924_, v___x_925_, v___x_925_, v___x_926_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_927_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; uint8_t v___x_981_; 
lean_dec_ref_known(v___x_938_, 1);
v___x_939_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_a_937_, v___y_932_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref(v___x_939_);
v___x_981_ = l_Lean_Expr_hasSyntheticSorry(v_a_940_);
if (v___x_981_ == 0)
{
v___y_942_ = v___y_929_;
v___y_943_ = v___y_930_;
v___y_944_ = v___y_931_;
v___y_945_ = v___y_932_;
v___y_946_ = v___y_933_;
v___y_947_ = v___y_934_;
goto v___jp_941_;
}
else
{
lean_object* v___x_982_; lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_a_940_);
lean_dec_ref(v___x_928_);
v___x_982_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
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
v___jp_941_:
{
lean_object* v___x_948_; 
lean_inc(v_a_940_);
v___x_948_ = l_Lean_Meta_getMVars(v_a_940_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = lean_box(0);
v___x_951_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_949_, v___x_950_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v_a_949_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; uint8_t v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_unbox(v_a_952_);
lean_dec(v_a_952_);
if (v___x_953_ == 0)
{
uint8_t v___x_954_; lean_object* v___x_955_; 
v___x_954_ = 1;
v___x_955_ = l_Lean_Meta_evalExpr___redArg(v___x_928_, v_a_940_, v___x_954_, v___x_925_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v_a_940_);
lean_dec_ref(v___x_928_);
v___x_956_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec(v_a_940_);
lean_dec_ref(v___x_928_);
v_a_965_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_951_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_951_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_a_940_);
lean_dec_ref(v___x_928_);
v_a_973_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_948_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_948_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_a_937_);
lean_dec_ref(v___x_928_);
v_a_991_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_938_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_938_);
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
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v___x_928_);
v_a_999_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_936_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_936_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed(lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v___x_5797__boxed_1020_; uint8_t v___x_5799__boxed_1021_; lean_object* v_res_1022_; 
v___x_5797__boxed_1020_ = lean_unbox(v___x_1009_);
v___x_5799__boxed_1021_ = lean_unbox(v___x_1011_);
v_res_1022_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(v___x_1007_, v___x_1008_, v___x_5797__boxed_1020_, v___x_1010_, v___x_5799__boxed_1021_, v___x_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1022_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_1029_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
lean_ctor_set(v___x_1029_, 2, v___x_1028_);
lean_ctor_set(v___x_1029_, 3, v___x_1028_);
lean_ctor_set(v___x_1029_, 4, v___x_1028_);
lean_ctor_set(v___x_1029_, 5, v___x_1028_);
lean_ctor_set(v___x_1029_, 6, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(lean_object* v_env_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v_nextMacroScope_1035_; lean_object* v_ngen_1036_; lean_object* v_auxDeclNGen_1037_; lean_object* v_traceState_1038_; lean_object* v_recordedDeps_1039_; lean_object* v_messages_1040_; lean_object* v_infoState_1041_; lean_object* v_snapshotTasks_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1068_; 
v___x_1034_ = lean_st_ref_take(v___y_1032_);
v_nextMacroScope_1035_ = lean_ctor_get(v___x_1034_, 1);
v_ngen_1036_ = lean_ctor_get(v___x_1034_, 2);
v_auxDeclNGen_1037_ = lean_ctor_get(v___x_1034_, 3);
v_traceState_1038_ = lean_ctor_get(v___x_1034_, 4);
v_recordedDeps_1039_ = lean_ctor_get(v___x_1034_, 6);
v_messages_1040_ = lean_ctor_get(v___x_1034_, 7);
v_infoState_1041_ = lean_ctor_get(v___x_1034_, 8);
v_snapshotTasks_1042_ = lean_ctor_get(v___x_1034_, 9);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; lean_object* v_unused_1070_; 
v_unused_1069_ = lean_ctor_get(v___x_1034_, 5);
lean_dec(v_unused_1069_);
v_unused_1070_ = lean_ctor_get(v___x_1034_, 0);
lean_dec(v_unused_1070_);
v___x_1044_ = v___x_1034_;
v_isShared_1045_ = v_isSharedCheck_1068_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_snapshotTasks_1042_);
lean_inc(v_infoState_1041_);
lean_inc(v_messages_1040_);
lean_inc(v_recordedDeps_1039_);
lean_inc(v_traceState_1038_);
lean_inc(v_auxDeclNGen_1037_);
lean_inc(v_ngen_1036_);
lean_inc(v_nextMacroScope_1035_);
lean_dec(v___x_1034_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1068_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 5, v___x_1046_);
lean_ctor_set(v___x_1044_, 0, v_env_1030_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_env_1030_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_nextMacroScope_1035_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_ngen_1036_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_auxDeclNGen_1037_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v_traceState_1038_);
lean_ctor_set(v_reuseFailAlloc_1067_, 5, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1067_, 6, v_recordedDeps_1039_);
lean_ctor_set(v_reuseFailAlloc_1067_, 7, v_messages_1040_);
lean_ctor_set(v_reuseFailAlloc_1067_, 8, v_infoState_1041_);
lean_ctor_set(v_reuseFailAlloc_1067_, 9, v_snapshotTasks_1042_);
v___x_1048_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_mctx_1051_; lean_object* v_zetaDeltaFVarIds_1052_; lean_object* v_postponed_1053_; lean_object* v_diag_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1065_; 
v___x_1049_ = lean_st_ref_put(v___y_1032_, v___x_1048_);
v___x_1050_ = lean_st_ref_take(v___y_1031_);
v_mctx_1051_ = lean_ctor_get(v___x_1050_, 0);
v_zetaDeltaFVarIds_1052_ = lean_ctor_get(v___x_1050_, 2);
v_postponed_1053_ = lean_ctor_get(v___x_1050_, 3);
v_diag_1054_ = lean_ctor_get(v___x_1050_, 4);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v___x_1050_, 1);
lean_dec(v_unused_1066_);
v___x_1056_ = v___x_1050_;
v_isShared_1057_ = v_isSharedCheck_1065_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_diag_1054_);
lean_inc(v_postponed_1053_);
lean_inc(v_zetaDeltaFVarIds_1052_);
lean_inc(v_mctx_1051_);
lean_dec(v___x_1050_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1065_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_mctx_1051_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_zetaDeltaFVarIds_1052_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_postponed_1053_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_diag_1054_);
v___x_1061_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_st_ref_put(v___y_1031_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1058_);
return v___x_1063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___boxed(lean_object* v_env_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(lean_object* v_env_1076_, lean_object* v_x_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v_env_1086_; lean_object* v_a_1088_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1085_ = lean_st_ref_get(v___y_1083_);
v_env_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_env_1086_);
lean_dec(v___x_1085_);
v___x_1098_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1076_, v___y_1081_, v___y_1083_);
lean_dec_ref(v___x_1098_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
v___x_1099_ = lean_apply_7(v_x_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1086_, v___y_1081_, v___y_1083_);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; 
v_unused_1109_ = lean_ctor_get(v___x_1101_, 0);
lean_dec(v_unused_1109_);
v___x_1103_ = v___x_1101_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v___x_1101_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v_a_1100_);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1100_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1099_, 1);
v_a_1088_ = v_a_1110_;
goto v___jp_1087_;
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v___x_1089_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1086_, v___y_1081_, v___y_1083_);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1089_, 0);
lean_dec(v_unused_1097_);
v___x_1091_ = v___x_1089_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v___x_1089_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
lean_ctor_set(v___x_1091_, 0, v_a_1088_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1088_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg___boxed(lean_object* v_env_1111_, lean_object* v_x_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1111_, v_x_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1120_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10));
v___x_1142_ = l_String_toRawSubstring_x27(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24));
v___x_1171_ = l_String_toRawSubstring_x27(v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34));
v___x_1194_ = l_String_toRawSubstring_x27(v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37));
v___x_1210_ = l_Lean_mkConst(v___x_1209_, v___x_1208_);
return v___x_1210_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41);
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(lean_object* v_post_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_toCold_1221_; lean_object* v_ref_1222_; lean_object* v_quotContext_1223_; lean_object* v_currMacroScope_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v_env_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_toCold_1221_ = lean_ctor_get(v_a_1218_, 0);
v_ref_1222_ = lean_ctor_get(v_a_1218_, 2);
v_quotContext_1223_ = lean_ctor_get(v_toCold_1221_, 8);
v_currMacroScope_1224_ = lean_ctor_get(v_toCold_1221_, 9);
v___x_1225_ = 0;
v___x_1226_ = l_Lean_SourceInfo_fromRef(v_ref_1222_, v___x_1225_);
v___x_1227_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3));
v___x_1228_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4));
lean_inc_n(v___x_1226_, 14);
v___x_1229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1226_);
lean_ctor_set(v___x_1229_, 1, v___x_1227_);
v___x_1230_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7));
v___x_1231_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9));
v___x_1232_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11);
v___x_1233_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13));
lean_inc_n(v_currMacroScope_1224_, 3);
lean_inc_n(v_quotContext_1223_, 3);
v___x_1234_ = l_Lean_addMacroScope(v_quotContext_1223_, v___x_1233_, v_currMacroScope_1224_);
v___x_1235_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15));
v___x_1236_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1226_);
lean_ctor_set(v___x_1236_, 1, v___x_1232_);
lean_ctor_set(v___x_1236_, 2, v___x_1234_);
lean_ctor_set(v___x_1236_, 3, v___x_1235_);
v___x_1237_ = l_Lean_Syntax_node1(v___x_1226_, v___x_1231_, v___x_1236_);
v___x_1238_ = l_Lean_Syntax_node1(v___x_1226_, v___x_1230_, v___x_1237_);
v___x_1239_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16));
v___x_1240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1226_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18));
v___x_1242_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20));
v___x_1243_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21));
v___x_1244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1226_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23));
v___x_1246_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Lean_addMacroScope(v_quotContext_1223_, v___x_1247_, v_currMacroScope_1224_);
v___x_1249_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32));
v___x_1250_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1226_);
lean_ctor_set(v___x_1250_, 1, v___x_1246_);
lean_ctor_set(v___x_1250_, 2, v___x_1248_);
lean_ctor_set(v___x_1250_, 3, v___x_1249_);
v___x_1251_ = l_Lean_Syntax_node1(v___x_1226_, v___x_1245_, v___x_1250_);
v___x_1252_ = l_Lean_Syntax_node2(v___x_1226_, v___x_1242_, v___x_1244_, v___x_1251_);
v___x_1253_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33));
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1226_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35);
v___x_1256_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36));
v___x_1257_ = l_Lean_addMacroScope(v_quotContext_1223_, v___x_1256_, v_currMacroScope_1224_);
v___x_1258_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39));
v___x_1259_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1226_);
lean_ctor_set(v___x_1259_, 1, v___x_1255_);
lean_ctor_set(v___x_1259_, 2, v___x_1257_);
lean_ctor_set(v___x_1259_, 3, v___x_1258_);
v___x_1260_ = l_Lean_Syntax_node1(v___x_1226_, v___x_1231_, v___x_1259_);
v___x_1261_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40));
v___x_1262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1226_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_Lean_Syntax_node5(v___x_1226_, v___x_1241_, v___x_1252_, v_post_1213_, v___x_1254_, v___x_1260_, v___x_1262_);
v___x_1264_ = l_Lean_Syntax_node4(v___x_1226_, v___x_1228_, v___x_1229_, v___x_1238_, v___x_1240_, v___x_1263_);
v___x_1265_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41);
v___x_1266_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42);
v___x_1267_ = 1;
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_box(v___x_1267_);
v___x_1270_ = lean_box(v___x_1225_);
v___f_1271_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1271_, 0, v___x_1264_);
lean_closure_set(v___f_1271_, 1, v___x_1266_);
lean_closure_set(v___f_1271_, 2, v___x_1269_);
lean_closure_set(v___f_1271_, 3, v___x_1268_);
lean_closure_set(v___f_1271_, 4, v___x_1270_);
lean_closure_set(v___f_1271_, 5, v___x_1265_);
v___x_1272_ = lean_st_ref_get(v_a_1219_);
v_env_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc_ref(v_env_1273_);
lean_dec(v___x_1272_);
v___x_1274_ = l_Lean_Environment_unlockAsync(v_env_1273_);
v___x_1275_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v___x_1274_, v___f_1271_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___boxed(lean_object* v_post_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(lean_object* v_env_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1285_, v___y_1289_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___boxed(lean_object* v_env_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(v_env_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(lean_object* v_00_u03b1_1303_, lean_object* v_env_1304_, lean_object* v_x_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1304_, v_x_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___boxed(lean_object* v_00_u03b1_1314_, lean_object* v_env_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(v_00_u03b1_1314_, v_env_1315_, v_x_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(lean_object* v_post_1325_, lean_object* v_x_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1325_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed(lean_object* v_post_1335_, lean_object* v_x_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(v_post_1335_, v_x_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v_x_1336_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(lean_object* v_a_1345_, lean_object* v_traceState_1346_, lean_object* v_a_x3f_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v_env_1350_; lean_object* v_messages_1351_; lean_object* v_scopes_1352_; lean_object* v_usedQuotCtxts_1353_; lean_object* v_nextMacroScope_1354_; lean_object* v_maxRecDepth_1355_; lean_object* v_ngen_1356_; lean_object* v_auxDeclNGen_1357_; lean_object* v_infoState_1358_; lean_object* v_snapshotTasks_1359_; lean_object* v_prevLinterStates_1360_; lean_object* v_codeQualityEntryTasks_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1371_; 
v___x_1349_ = lean_st_ref_take(v_a_1345_);
v_env_1350_ = lean_ctor_get(v___x_1349_, 0);
v_messages_1351_ = lean_ctor_get(v___x_1349_, 1);
v_scopes_1352_ = lean_ctor_get(v___x_1349_, 2);
v_usedQuotCtxts_1353_ = lean_ctor_get(v___x_1349_, 3);
v_nextMacroScope_1354_ = lean_ctor_get(v___x_1349_, 4);
v_maxRecDepth_1355_ = lean_ctor_get(v___x_1349_, 5);
v_ngen_1356_ = lean_ctor_get(v___x_1349_, 6);
v_auxDeclNGen_1357_ = lean_ctor_get(v___x_1349_, 7);
v_infoState_1358_ = lean_ctor_get(v___x_1349_, 8);
v_snapshotTasks_1359_ = lean_ctor_get(v___x_1349_, 10);
v_prevLinterStates_1360_ = lean_ctor_get(v___x_1349_, 11);
v_codeQualityEntryTasks_1361_ = lean_ctor_get(v___x_1349_, 12);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v___x_1349_, 9);
lean_dec(v_unused_1372_);
v___x_1363_ = v___x_1349_;
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1361_);
lean_inc(v_prevLinterStates_1360_);
lean_inc(v_snapshotTasks_1359_);
lean_inc(v_infoState_1358_);
lean_inc(v_auxDeclNGen_1357_);
lean_inc(v_ngen_1356_);
lean_inc(v_maxRecDepth_1355_);
lean_inc(v_nextMacroScope_1354_);
lean_inc(v_usedQuotCtxts_1353_);
lean_inc(v_scopes_1352_);
lean_inc(v_messages_1351_);
lean_inc(v_env_1350_);
lean_dec(v___x_1349_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1371_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_box(0);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 9, v_traceState_1346_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_env_1350_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_messages_1351_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_scopes_1352_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_usedQuotCtxts_1353_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_nextMacroScope_1354_);
lean_ctor_set(v_reuseFailAlloc_1370_, 5, v_maxRecDepth_1355_);
lean_ctor_set(v_reuseFailAlloc_1370_, 6, v_ngen_1356_);
lean_ctor_set(v_reuseFailAlloc_1370_, 7, v_auxDeclNGen_1357_);
lean_ctor_set(v_reuseFailAlloc_1370_, 8, v_infoState_1358_);
lean_ctor_set(v_reuseFailAlloc_1370_, 9, v_traceState_1346_);
lean_ctor_set(v_reuseFailAlloc_1370_, 10, v_snapshotTasks_1359_);
lean_ctor_set(v_reuseFailAlloc_1370_, 11, v_prevLinterStates_1360_);
lean_ctor_set(v_reuseFailAlloc_1370_, 12, v_codeQualityEntryTasks_1361_);
v___x_1367_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_st_ref_put(v_a_1345_, v___x_1367_);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1365_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1___boxed(lean_object* v_a_1373_, lean_object* v_traceState_1374_, lean_object* v_a_x3f_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1373_, v_traceState_1374_, v_a_x3f_1375_);
lean_dec(v_a_x3f_1375_);
lean_dec(v_a_1373_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(lean_object* v_a_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_apply_4(v_a_1378_, v___y_1379_, v___y_1380_, v___y_1381_, lean_box(0));
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed(lean_object* v_a_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(v_a_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object* v_post_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___f_1394_; lean_object* v___x_1395_; lean_object* v_traceState_1396_; lean_object* v_r_1397_; 
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1394_, 0, v_post_1390_);
v___x_1395_ = lean_st_ref_get(v_a_1392_);
v_traceState_1396_ = lean_ctor_get(v___x_1395_, 9);
lean_inc_ref(v_traceState_1396_);
lean_dec(v___x_1395_);
v_r_1397_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_1394_, v_a_1391_, v_a_1392_);
if (lean_obj_tag(v_r_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1415_; 
v_a_1398_ = lean_ctor_get(v_r_1397_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_r_1397_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1400_ = v_r_1397_;
v_isShared_1401_ = v_isSharedCheck_1415_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v_r_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1415_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___f_1402_; lean_object* v___x_1404_; 
lean_inc(v_a_1398_);
v___f_1402_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed), 5, 1);
lean_closure_set(v___f_1402_, 0, v_a_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 1);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1398_);
v___x_1404_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v___x_1405_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1392_, v_traceState_1396_, v___x_1404_);
lean_dec_ref(v___x_1404_);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v___x_1405_, 0);
lean_dec(v_unused_1413_);
v___x_1407_ = v___x_1405_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v___x_1405_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___f_1402_);
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___f_1402_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_a_1416_ = lean_ctor_get(v_r_1397_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v_r_1397_, 1);
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1392_, v_traceState_1396_, v___x_1417_);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1418_, 0);
lean_dec(v_unused_1426_);
v___x_1420_ = v___x_1418_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_dec(v___x_1418_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 1);
lean_ctor_set(v___x_1420_, 0, v_a_1416_);
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1416_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___boxed(lean_object* v_post_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1427_, v_a_1428_, v_a_1429_);
lean_dec(v_a_1429_);
lean_dec_ref(v_a_1428_);
return v_res_1431_;
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
