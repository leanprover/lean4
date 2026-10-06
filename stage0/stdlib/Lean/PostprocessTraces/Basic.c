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
uint8_t v___x_242_; 
v___x_242_ = lean_nat_dec_le(v___x_240_, v___x_240_);
if (v___x_242_ == 0)
{
if (v___x_241_ == 0)
{
lean_dec_ref(v___x_239_);
v___y_236_ = v___x_233_;
goto v___jp_235_;
}
else
{
size_t v___x_243_; size_t v___x_244_; double v___x_245_; 
v___x_243_ = ((size_t)0ULL);
v___x_244_ = lean_usize_of_nat(v___x_240_);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_239_, v___x_243_, v___x_244_, v___x_233_);
lean_dec_ref(v___x_239_);
v___y_236_ = v___x_245_;
goto v___jp_235_;
}
}
else
{
size_t v___x_246_; size_t v___x_247_; double v___x_248_; 
v___x_246_ = ((size_t)0ULL);
v___x_247_ = lean_usize_of_nat(v___x_240_);
v___x_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_selfElapsed_spec__0(v___x_239_, v___x_246_, v___x_247_, v___x_233_);
lean_dec_ref(v___x_239_);
v___y_236_ = v___x_248_;
goto v___jp_235_;
}
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
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_selfElapsed___boxed(lean_object* v_t_249_){
_start:
{
double v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_249_);
lean_dec_ref(v_t_249_);
v_r_251_ = lean_box_float(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText(lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v_data_255_; lean_object* v_msg_256_; lean_object* v_wrap_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_result_x3f_260_; 
v_data_255_ = lean_ctor_get(v_x_253_, 0);
lean_inc_ref(v_data_255_);
v_msg_256_ = lean_ctor_get(v_x_253_, 1);
lean_inc_ref(v_msg_256_);
v_wrap_257_ = lean_ctor_get(v_x_253_, 3);
lean_inc_ref(v_wrap_257_);
lean_dec_ref_known(v_x_253_, 4);
v___x_258_ = lean_apply_1(v_wrap_257_, v_msg_256_);
v___x_259_ = l_Lean_MessageData_toString(v___x_258_);
v_result_x3f_260_ = lean_ctor_get(v_data_255_, 1);
lean_inc(v_result_x3f_260_);
lean_dec_ref(v_data_255_);
if (lean_obj_tag(v_result_x3f_260_) == 0)
{
return v___x_259_;
}
else
{
lean_object* v_val_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_val_261_ = lean_ctor_get(v_result_x3f_260_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v_result_x3f_260_, 1);
v___x_262_ = lean_unbox(v_val_261_);
lean_dec(v_val_261_);
v___x_263_ = l_Lean_TraceResult_toEmoji(v___x_262_);
v___x_264_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_headText___closed__0));
v___x_265_ = lean_string_append(v___x_263_, v___x_264_);
v___x_266_ = lean_string_append(v___x_265_, v___x_259_);
lean_dec_ref(v___x_259_);
return v___x_266_;
}
}
else
{
lean_object* v_msg_267_; lean_object* v___x_268_; 
v_msg_267_ = lean_ctor_get(v_x_253_, 0);
lean_inc_ref(v_msg_267_);
lean_dec_ref_known(v_x_253_, 1);
v___x_268_ = l_Lean_MessageData_toString(v_msg_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_headText___boxed(lean_object* v_x_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_PostprocessTraces_TraceTree_headText(v_x_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f(lean_object* v_t_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_PostprocessTraces_TraceTree_data_x3f(v_t_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_box(0);
return v___x_274_;
}
else
{
lean_object* v_val_275_; lean_object* v_result_x3f_276_; 
v_val_275_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_val_275_);
lean_dec_ref_known(v___x_273_, 1);
v_result_x3f_276_ = lean_ctor_get(v_val_275_, 1);
lean_inc(v_result_x3f_276_);
lean_dec(v_val_275_);
return v_result_x3f_276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_result_x3f___boxed(lean_object* v_t_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_277_);
lean_dec_ref(v_t_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees(lean_object* v_p_279_, lean_object* v_t_280_, lean_object* v_acc_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_285_; 
lean_inc_ref(v_p_279_);
lean_inc(v_a_283_);
lean_inc_ref(v_a_282_);
lean_inc_ref(v_t_280_);
v___x_285_ = lean_apply_4(v_p_279_, v_t_280_, v_a_282_, v_a_283_, lean_box(0));
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_312_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_312_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_312_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_312_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___x_290_; 
v___x_290_ = lean_unbox(v_a_286_);
lean_dec(v_a_286_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_291_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_280_);
lean_dec_ref(v_t_280_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v___x_291_);
v___x_294_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_296_; 
lean_dec_ref(v___x_291_);
lean_dec_ref(v_p_279_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_acc_281_);
v___x_296_ = v___x_288_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_acc_281_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
uint8_t v___x_298_; 
v___x_298_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_298_ == 0)
{
if (v___x_294_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v___x_291_);
lean_dec_ref(v_p_279_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v_acc_281_);
v___x_300_ = v___x_288_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_acc_281_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
else
{
size_t v___x_302_; size_t v___x_303_; lean_object* v___x_304_; 
lean_del_object(v___x_288_);
v___x_302_ = ((size_t)0ULL);
v___x_303_ = lean_usize_of_nat(v___x_293_);
v___x_304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_279_, v___x_291_, v___x_302_, v___x_303_, v_acc_281_, v_a_282_, v_a_283_);
lean_dec_ref(v___x_291_);
return v___x_304_;
}
}
else
{
size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; 
lean_del_object(v___x_288_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = lean_usize_of_nat(v___x_293_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_279_, v___x_291_, v___x_305_, v___x_306_, v_acc_281_, v_a_282_, v_a_283_);
lean_dec_ref(v___x_291_);
return v___x_307_;
}
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_310_; 
lean_dec_ref(v_p_279_);
v___x_308_ = lean_array_push(v_acc_281_, v_t_280_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_308_);
v___x_310_ = v___x_288_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v_acc_281_);
lean_dec_ref(v_t_280_);
lean_dec_ref(v_p_279_);
v_a_313_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_285_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_285_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(lean_object* v_p_321_, lean_object* v_as_322_, size_t v_i_323_, size_t v_stop_324_, lean_object* v_b_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_323_, v_stop_324_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_array_uget_borrowed(v_as_322_, v_i_323_);
lean_inc(v___x_330_);
lean_inc_ref(v_p_321_);
v___x_331_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_321_, v___x_330_, v_b_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; size_t v___x_333_; size_t v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_add(v_i_323_, v___x_333_);
v_i_323_ = v___x_334_;
v_b_325_ = v_a_332_;
goto _start;
}
else
{
lean_dec_ref(v_p_321_);
return v___x_331_;
}
}
else
{
lean_object* v___x_336_; 
lean_dec_ref(v_p_321_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v_b_325_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0___boxed(lean_object* v_p_337_, lean_object* v_as_338_, lean_object* v_i_339_, lean_object* v_stop_340_, lean_object* v_b_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
size_t v_i_boxed_345_; size_t v_stop_boxed_346_; lean_object* v_res_347_; 
v_i_boxed_345_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_stop_boxed_346_ = lean_unbox_usize(v_stop_340_);
lean_dec(v_stop_340_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_TraceTree_collectSubtrees_spec__0(v_p_337_, v_as_338_, v_i_boxed_345_, v_stop_boxed_346_, v_b_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec_ref(v_as_338_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_collectSubtrees___boxed(lean_object* v_p_348_, lean_object* v_t_349_, lean_object* v_acc_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_348_, v_t_349_, v_acc_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(lean_object* v_p_355_, lean_object* v_as_356_, lean_object* v_start_357_, lean_object* v_stop_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_children___closed__0));
v___x_363_ = lean_nat_dec_lt(v_start_357_, v_stop_358_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v_p_355_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = lean_array_get_size(v_as_356_);
v___x_366_ = lean_nat_dec_le(v_stop_358_, v___x_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = lean_nat_dec_lt(v_start_357_, v___x_365_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec_ref(v_p_355_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_362_);
return v___x_368_;
}
else
{
size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_usize_of_nat(v_start_357_);
v___x_370_ = lean_usize_of_nat(v___x_365_);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_355_, v_as_356_, v___x_369_, v___x_370_, v___x_362_, v___y_359_, v___y_360_);
return v___x_371_;
}
}
else
{
size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_usize_of_nat(v_start_357_);
v___x_373_ = lean_usize_of_nat(v_stop_358_);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_355_, v_as_356_, v___x_372_, v___x_373_, v___x_362_, v___y_359_, v___y_360_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees(lean_object* v_p_375_, lean_object* v_t_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_380_; 
lean_inc_ref(v_p_375_);
lean_inc(v_a_378_);
lean_inc_ref(v_a_377_);
lean_inc_ref(v_t_376_);
v___x_380_ = lean_apply_4(v_p_375_, v_t_376_, v_a_377_, v_a_378_, lean_box(0));
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_418_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_418_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_418_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_418_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; 
v___x_385_ = lean_unbox(v_a_381_);
lean_dec(v_a_381_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_del_object(v___x_383_);
v___x_386_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_376_);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_array_get_size(v___x_386_);
v___x_389_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_375_, v___x_386_, v___x_387_, v___x_388_, v_a_377_, v_a_378_);
lean_dec_ref(v___x_386_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_405_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_405_ == 0)
{
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_405_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_405_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_get_size(v_a_390_);
v___x_395_ = lean_nat_dec_eq(v___x_394_, v___x_387_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_376_, v_a_390_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_397_);
v___x_399_ = v___x_392_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_403_; 
lean_dec(v_a_390_);
lean_dec_ref(v_t_376_);
v___x_401_ = lean_box(0);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_401_);
v___x_403_ = v___x_392_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec_ref(v_t_376_);
v_a_406_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_389_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_389_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec_ref(v_p_375_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v_t_376_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_414_);
v___x_416_ = v___x_383_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_t_376_);
lean_dec_ref(v_p_375_);
v_a_419_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_380_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_380_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(lean_object* v_p_427_, lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_, lean_object* v_b_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_a_436_; uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
lean_inc(v___x_441_);
lean_inc_ref(v_p_427_);
v___x_442_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_427_, v___x_441_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
if (lean_obj_tag(v_a_443_) == 0)
{
v_a_436_ = v_b_431_;
goto v___jp_435_;
}
else
{
lean_object* v_val_444_; lean_object* v___x_445_; 
v_val_444_ = lean_ctor_get(v_a_443_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_a_443_, 1);
v___x_445_ = lean_array_push(v_b_431_, v_val_444_);
v_a_436_ = v___x_445_;
goto v___jp_435_;
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v_b_431_);
lean_dec_ref(v_p_427_);
v_a_446_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_442_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_442_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
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
else
{
lean_object* v___x_454_; 
lean_dec_ref(v_p_427_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_b_431_);
return v___x_454_;
}
v___jp_435_:
{
size_t v___x_437_; size_t v___x_438_; 
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_add(v_i_429_, v___x_437_);
v_i_429_ = v___x_438_;
v_b_431_ = v_a_436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0___boxed(lean_object* v_p_455_, lean_object* v_as_456_, lean_object* v_i_457_, lean_object* v_stop_458_, lean_object* v_b_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
size_t v_i_boxed_463_; size_t v_stop_boxed_464_; lean_object* v_res_465_; 
v_i_boxed_463_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_stop_boxed_464_ = lean_unbox_usize(v_stop_458_);
lean_dec(v_stop_458_);
v_res_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0_spec__0(v_p_455_, v_as_456_, v_i_boxed_463_, v_stop_boxed_464_, v_b_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec_ref(v_as_456_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0___boxed(lean_object* v_p_466_, lean_object* v_as_467_, lean_object* v_start_468_, lean_object* v_stop_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_TraceTree_filterSubtrees_spec__0(v_p_466_, v_as_467_, v_start_468_, v_stop_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v_stop_469_);
lean_dec(v_start_468_);
lean_dec_ref(v_as_467_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_TraceTree_filterSubtrees___boxed(lean_object* v_p_474_, lean_object* v_t_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_474_, v_t_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2(lean_object* v_data_480_, lean_object* v_msg_481_, lean_object* v_a_482_, lean_object* v_wrap_483_, lean_object* v_children_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_485_, 0, v_data_480_);
lean_ctor_set(v___x_485_, 1, v_msg_481_);
lean_ctor_set(v___x_485_, 2, v_children_484_);
v___x_486_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_486_, 0, v_a_482_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_apply_1(v_wrap_483_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(lean_object* v_wrap_491_, lean_object* v_a_492_){
_start:
{
switch(lean_obj_tag(v_a_492_))
{
case 3:
{
lean_object* v_a_493_; lean_object* v_a_494_; lean_object* v___f_495_; 
v_a_493_ = lean_ctor_get(v_a_492_, 0);
lean_inc_ref(v_a_493_);
v_a_494_ = lean_ctor_get(v_a_492_, 1);
lean_inc_ref(v_a_494_);
lean_dec_ref_known(v_a_492_, 2);
v___f_495_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__0), 3, 2);
lean_closure_set(v___f_495_, 0, v_a_493_);
lean_closure_set(v___f_495_, 1, v_wrap_491_);
v_wrap_491_ = v___f_495_;
v_a_492_ = v_a_494_;
goto _start;
}
case 4:
{
lean_object* v_a_497_; lean_object* v_a_498_; lean_object* v___f_499_; 
v_a_497_ = lean_ctor_get(v_a_492_, 0);
lean_inc_ref(v_a_497_);
v_a_498_ = lean_ctor_get(v_a_492_, 1);
lean_inc_ref(v_a_498_);
lean_dec_ref_known(v_a_492_, 2);
v___f_499_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_PostprocessTraces_TraceTree_ofMessageData_go___lam__1), 3, 2);
lean_closure_set(v___f_499_, 0, v_a_497_);
lean_closure_set(v___f_499_, 1, v_wrap_491_);
v_wrap_491_ = v___f_499_;
v_a_492_ = v_a_498_;
goto _start;
}
case 8:
{
lean_object* v_a_501_; 
v_a_501_ = lean_ctor_get(v_a_492_, 1);
lean_inc_ref(v_a_501_);
if (lean_obj_tag(v_a_501_) == 9)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_517_; 
v_a_502_ = lean_ctor_get(v_a_492_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_492_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_a_492_, 1);
lean_dec(v_unused_518_);
v___x_504_ = v_a_492_;
v_isShared_505_ = v_isSharedCheck_517_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v_a_492_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_517_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_data_506_; lean_object* v_msg_507_; lean_object* v_children_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_data_506_ = lean_ctor_get(v_a_501_, 0);
lean_inc_ref(v_data_506_);
v_msg_507_ = lean_ctor_get(v_a_501_, 1);
lean_inc_ref(v_msg_507_);
v_children_508_ = lean_ctor_get(v_a_501_, 2);
lean_inc_ref(v_children_508_);
lean_dec_ref_known(v_a_501_, 3);
v___x_509_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___closed__1));
v___x_510_ = lean_name_eq(v_a_502_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v_children_508_);
lean_dec_ref(v_msg_507_);
lean_dec_ref(v_data_506_);
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
lean_dec_ref(v_wrap_491_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
else
{
lean_object* v___f_512_; lean_object* v___x_514_; 
v___f_512_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go___lam__2), 5, 4);
lean_closure_set(v___f_512_, 0, v_data_506_);
lean_closure_set(v___f_512_, 1, v_msg_507_);
lean_closure_set(v___f_512_, 2, v_a_502_);
lean_closure_set(v___f_512_, 3, v_wrap_491_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 0);
lean_ctor_set(v___x_504_, 1, v_children_508_);
lean_ctor_set(v___x_504_, 0, v___f_512_);
v___x_514_ = v___x_504_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___f_512_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_children_508_);
v___x_514_ = v_reuseFailAlloc_516_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
}
else
{
lean_object* v___x_519_; 
lean_dec_ref_known(v_a_492_, 2);
lean_dec_ref(v_a_501_);
lean_dec_ref(v_wrap_491_);
v___x_519_ = lean_box(0);
return v___x_519_;
}
}
default: 
{
lean_object* v___x_520_; 
lean_dec_ref(v_a_492_);
lean_dec_ref(v_wrap_491_);
v___x_520_ = lean_box(0);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_traceContainer_x3f(lean_object* v_data_521_){
_start:
{
lean_object* v___f_522_; lean_object* v___x_523_; 
v___f_522_ = ((lean_object*)(l_Lean_PostprocessTraces_TraceTree_ofMessageData___closed__0));
v___x_523_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_traceContainer_x3f_go(v___f_522_, v_data_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(size_t v_sz_524_, size_t v_i_525_, lean_object* v_bs_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_lt(v_i_525_, v_sz_524_);
if (v___x_527_ == 0)
{
return v_bs_526_;
}
else
{
lean_object* v_v_528_; lean_object* v___x_529_; lean_object* v_bs_x27_530_; lean_object* v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v_v_528_ = lean_array_uget(v_bs_526_, v_i_525_);
v___x_529_ = lean_unsigned_to_nat(0u);
v_bs_x27_530_ = lean_array_uset(v_bs_526_, v_i_525_, v___x_529_);
v___x_531_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData(v_v_528_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_525_, v___x_532_);
v___x_534_ = lean_array_uset(v_bs_x27_530_, v_i_525_, v___x_531_);
v_i_525_ = v___x_533_;
v_bs_526_ = v___x_534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0___boxed(lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_bs_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_boxed_539_, v_i_boxed_540_, v_bs_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage(lean_object* v_post_542_, lean_object* v_msg_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_fileName_547_; lean_object* v_pos_548_; lean_object* v_endPos_549_; uint8_t v_keepFullRange_550_; uint8_t v_severity_551_; uint8_t v_isSilent_552_; lean_object* v_caption_553_; lean_object* v_data_554_; lean_object* v___x_555_; 
v_fileName_547_ = lean_ctor_get(v_msg_543_, 0);
v_pos_548_ = lean_ctor_get(v_msg_543_, 1);
v_endPos_549_ = lean_ctor_get(v_msg_543_, 2);
v_keepFullRange_550_ = lean_ctor_get_uint8(v_msg_543_, sizeof(void*)*5);
v_severity_551_ = lean_ctor_get_uint8(v_msg_543_, sizeof(void*)*5 + 1);
v_isSilent_552_ = lean_ctor_get_uint8(v_msg_543_, sizeof(void*)*5 + 2);
v_caption_553_ = lean_ctor_get(v_msg_543_, 3);
v_data_554_ = lean_ctor_get(v_msg_543_, 4);
lean_inc(v_data_554_);
v___x_555_ = l_Lean_Elab_PostprocessTraces_traceContainer_x3f(v_data_554_);
if (lean_obj_tag(v___x_555_) == 1)
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_602_; 
lean_inc_ref(v_caption_553_);
lean_inc(v_endPos_549_);
lean_inc_ref(v_pos_548_);
lean_inc_ref(v_fileName_547_);
v_isSharedCheck_602_ = !lean_is_exclusive(v_msg_543_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; lean_object* v_unused_604_; lean_object* v_unused_605_; lean_object* v_unused_606_; lean_object* v_unused_607_; 
v_unused_603_ = lean_ctor_get(v_msg_543_, 4);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_msg_543_, 3);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_msg_543_, 2);
lean_dec(v_unused_605_);
v_unused_606_ = lean_ctor_get(v_msg_543_, 1);
lean_dec(v_unused_606_);
v_unused_607_ = lean_ctor_get(v_msg_543_, 0);
lean_dec(v_unused_607_);
v___x_557_ = v_msg_543_;
v_isShared_558_ = v_isSharedCheck_602_;
goto v_resetjp_556_;
}
else
{
lean_dec(v_msg_543_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_602_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_val_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_601_; 
v_val_559_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_601_ == 0)
{
v___x_561_ = v___x_555_;
v_isShared_562_ = v_isSharedCheck_601_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_val_559_);
lean_dec(v___x_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_601_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_fst_563_; lean_object* v_snd_564_; size_t v_sz_565_; size_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_fst_563_ = lean_ctor_get(v_val_559_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v_val_559_, 1);
lean_inc(v_snd_564_);
lean_dec(v_val_559_);
v_sz_565_ = lean_array_size(v_snd_564_);
v___x_566_ = ((size_t)0ULL);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_PostprocessTraces_postprocessMessage_spec__0(v_sz_565_, v___x_566_, v_snd_564_);
lean_inc(v_a_545_);
lean_inc_ref(v_a_544_);
v___x_568_ = lean_apply_4(v_post_542_, v___x_567_, v_a_544_, v_a_545_, lean_box(0));
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_592_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_592_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_592_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_592_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = lean_array_get_size(v_a_569_);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_nat_dec_eq(v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
size_t v_sz_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v_sz_576_ = lean_array_size(v_a_569_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_TraceTree_toMessageData_spec__0(v_sz_576_, v___x_566_, v_a_569_);
v___x_578_ = lean_apply_1(v_fst_563_, v___x_577_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 4, v___x_578_);
v___x_580_ = v___x_557_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_fileName_547_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_pos_548_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_endPos_549_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_caption_553_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v___x_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_587_, sizeof(void*)*5, v_keepFullRange_550_);
lean_ctor_set_uint8(v_reuseFailAlloc_587_, sizeof(void*)*5 + 1, v_severity_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_587_, sizeof(void*)*5 + 2, v_isSilent_552_);
v___x_580_ = v_reuseFailAlloc_587_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_580_);
v___x_582_ = v___x_561_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_582_);
v___x_584_ = v___x_571_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_590_; 
lean_dec(v_a_569_);
lean_dec(v_fst_563_);
lean_del_object(v___x_561_);
lean_del_object(v___x_557_);
lean_dec_ref(v_caption_553_);
lean_dec(v_endPos_549_);
lean_dec_ref(v_pos_548_);
lean_dec_ref(v_fileName_547_);
v___x_588_ = lean_box(0);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_588_);
v___x_590_ = v___x_571_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v_fst_563_);
lean_del_object(v___x_561_);
lean_del_object(v___x_557_);
lean_dec_ref(v_caption_553_);
lean_dec(v_endPos_549_);
lean_dec_ref(v_pos_548_);
lean_dec_ref(v_fileName_547_);
v_a_593_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_568_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_568_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v___x_555_);
lean_dec_ref(v_post_542_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v_msg_543_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed(lean_object* v_post_610_, lean_object* v_msg_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Elab_PostprocessTraces_postprocessMessage(v_post_610_, v_msg_611_, v_a_612_, v_a_613_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(lean_object* v_a_616_, lean_object* v_messages_617_, lean_object* v_trees_618_, lean_object* v_a_x3f_619_){
_start:
{
lean_object* v___x_621_; lean_object* v_infoState_622_; lean_object* v_env_623_; lean_object* v_messages_624_; lean_object* v_scopes_625_; lean_object* v_usedQuotCtxts_626_; lean_object* v_nextMacroScope_627_; lean_object* v_maxRecDepth_628_; lean_object* v_ngen_629_; lean_object* v_auxDeclNGen_630_; lean_object* v_traceState_631_; lean_object* v_snapshotTasks_632_; lean_object* v_prevLinterStates_633_; lean_object* v_codeQualityEntryTasks_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_657_; 
v___x_621_ = lean_st_ref_take(v_a_616_);
v_infoState_622_ = lean_ctor_get(v___x_621_, 8);
v_env_623_ = lean_ctor_get(v___x_621_, 0);
v_messages_624_ = lean_ctor_get(v___x_621_, 1);
v_scopes_625_ = lean_ctor_get(v___x_621_, 2);
v_usedQuotCtxts_626_ = lean_ctor_get(v___x_621_, 3);
v_nextMacroScope_627_ = lean_ctor_get(v___x_621_, 4);
v_maxRecDepth_628_ = lean_ctor_get(v___x_621_, 5);
v_ngen_629_ = lean_ctor_get(v___x_621_, 6);
v_auxDeclNGen_630_ = lean_ctor_get(v___x_621_, 7);
v_traceState_631_ = lean_ctor_get(v___x_621_, 9);
v_snapshotTasks_632_ = lean_ctor_get(v___x_621_, 10);
v_prevLinterStates_633_ = lean_ctor_get(v___x_621_, 11);
v_codeQualityEntryTasks_634_ = lean_ctor_get(v___x_621_, 12);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_657_ == 0)
{
v___x_636_ = v___x_621_;
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_codeQualityEntryTasks_634_);
lean_inc(v_prevLinterStates_633_);
lean_inc(v_snapshotTasks_632_);
lean_inc(v_traceState_631_);
lean_inc(v_infoState_622_);
lean_inc(v_auxDeclNGen_630_);
lean_inc(v_ngen_629_);
lean_inc(v_maxRecDepth_628_);
lean_inc(v_nextMacroScope_627_);
lean_inc(v_usedQuotCtxts_626_);
lean_inc(v_scopes_625_);
lean_inc(v_messages_624_);
lean_inc(v_env_623_);
lean_dec(v___x_621_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
uint8_t v_enabled_638_; lean_object* v_assignment_639_; lean_object* v_lazyAssignment_640_; lean_object* v_trees_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_656_; 
v_enabled_638_ = lean_ctor_get_uint8(v_infoState_622_, sizeof(void*)*3);
v_assignment_639_ = lean_ctor_get(v_infoState_622_, 0);
v_lazyAssignment_640_ = lean_ctor_get(v_infoState_622_, 1);
v_trees_641_ = lean_ctor_get(v_infoState_622_, 2);
v_isSharedCheck_656_ = !lean_is_exclusive(v_infoState_622_);
if (v_isSharedCheck_656_ == 0)
{
v___x_643_ = v_infoState_622_;
v_isShared_644_ = v_isSharedCheck_656_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_trees_641_);
lean_inc(v_lazyAssignment_640_);
lean_inc(v_assignment_639_);
lean_dec(v_infoState_622_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_656_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_645_ = lean_box(0);
v___x_646_ = l_Lean_MessageLog_append(v_messages_617_, v_messages_624_);
v___x_647_ = l_Lean_PersistentArray_append___redArg(v_trees_618_, v_trees_641_);
lean_dec_ref(v_trees_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 2, v___x_647_);
v___x_649_ = v___x_643_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_assignment_639_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_lazyAssignment_640_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v___x_647_);
lean_ctor_set_uint8(v_reuseFailAlloc_655_, sizeof(void*)*3, v_enabled_638_);
v___x_649_ = v_reuseFailAlloc_655_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 8, v___x_649_);
lean_ctor_set(v___x_636_, 1, v___x_646_);
v___x_651_ = v___x_636_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_env_623_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_scopes_625_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_usedQuotCtxts_626_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v_nextMacroScope_627_);
lean_ctor_set(v_reuseFailAlloc_654_, 5, v_maxRecDepth_628_);
lean_ctor_set(v_reuseFailAlloc_654_, 6, v_ngen_629_);
lean_ctor_set(v_reuseFailAlloc_654_, 7, v_auxDeclNGen_630_);
lean_ctor_set(v_reuseFailAlloc_654_, 8, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_654_, 9, v_traceState_631_);
lean_ctor_set(v_reuseFailAlloc_654_, 10, v_snapshotTasks_632_);
lean_ctor_set(v_reuseFailAlloc_654_, 11, v_prevLinterStates_633_);
lean_ctor_set(v_reuseFailAlloc_654_, 12, v_codeQualityEntryTasks_634_);
v___x_651_ = v_reuseFailAlloc_654_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_st_ref_put(v_a_616_, v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_645_);
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
lean_object* v___x_736_; lean_object* v_messages_737_; lean_object* v___x_738_; lean_object* v_infoState_739_; lean_object* v_trees_740_; lean_object* v___x_741_; lean_object* v_env_742_; lean_object* v_scopes_743_; lean_object* v_usedQuotCtxts_744_; lean_object* v_nextMacroScope_745_; lean_object* v_maxRecDepth_746_; lean_object* v_ngen_747_; lean_object* v_auxDeclNGen_748_; lean_object* v_infoState_749_; lean_object* v_traceState_750_; lean_object* v_snapshotTasks_751_; lean_object* v_prevLinterStates_752_; lean_object* v_codeQualityEntryTasks_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_845_; 
v___x_736_ = lean_st_ref_get(v_a_734_);
v_messages_737_ = lean_ctor_get(v___x_736_, 1);
lean_inc_ref(v_messages_737_);
lean_dec(v___x_736_);
v___x_738_ = lean_st_ref_get(v_a_734_);
v_infoState_739_ = lean_ctor_get(v___x_738_, 8);
lean_inc_ref(v_infoState_739_);
lean_dec(v___x_738_);
v_trees_740_ = lean_ctor_get(v_infoState_739_, 2);
lean_inc_ref(v_trees_740_);
lean_dec_ref(v_infoState_739_);
v___x_741_ = lean_st_ref_take(v_a_734_);
v_env_742_ = lean_ctor_get(v___x_741_, 0);
v_scopes_743_ = lean_ctor_get(v___x_741_, 2);
v_usedQuotCtxts_744_ = lean_ctor_get(v___x_741_, 3);
v_nextMacroScope_745_ = lean_ctor_get(v___x_741_, 4);
v_maxRecDepth_746_ = lean_ctor_get(v___x_741_, 5);
v_ngen_747_ = lean_ctor_get(v___x_741_, 6);
v_auxDeclNGen_748_ = lean_ctor_get(v___x_741_, 7);
v_infoState_749_ = lean_ctor_get(v___x_741_, 8);
v_traceState_750_ = lean_ctor_get(v___x_741_, 9);
v_snapshotTasks_751_ = lean_ctor_get(v___x_741_, 10);
v_prevLinterStates_752_ = lean_ctor_get(v___x_741_, 11);
v_codeQualityEntryTasks_753_ = lean_ctor_get(v___x_741_, 12);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v___x_741_, 1);
lean_dec(v_unused_846_);
v___x_755_ = v___x_741_;
v_isShared_756_ = v_isSharedCheck_845_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_codeQualityEntryTasks_753_);
lean_inc(v_prevLinterStates_752_);
lean_inc(v_snapshotTasks_751_);
lean_inc(v_traceState_750_);
lean_inc(v_infoState_749_);
lean_inc(v_auxDeclNGen_748_);
lean_inc(v_ngen_747_);
lean_inc(v_maxRecDepth_746_);
lean_inc(v_nextMacroScope_745_);
lean_inc(v_usedQuotCtxts_744_);
lean_inc(v_scopes_743_);
lean_inc(v_env_742_);
lean_dec(v___x_741_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_845_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2, &l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2_once, _init_l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__2);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_758_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_env_742_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_scopes_743_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v_usedQuotCtxts_744_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v_nextMacroScope_745_);
lean_ctor_set(v_reuseFailAlloc_844_, 5, v_maxRecDepth_746_);
lean_ctor_set(v_reuseFailAlloc_844_, 6, v_ngen_747_);
lean_ctor_set(v_reuseFailAlloc_844_, 7, v_auxDeclNGen_748_);
lean_ctor_set(v_reuseFailAlloc_844_, 8, v_infoState_749_);
lean_ctor_set(v_reuseFailAlloc_844_, 9, v_traceState_750_);
lean_ctor_set(v_reuseFailAlloc_844_, 10, v_snapshotTasks_751_);
lean_ctor_set(v_reuseFailAlloc_844_, 11, v_prevLinterStates_752_);
lean_ctor_set(v_reuseFailAlloc_844_, 12, v_codeQualityEntryTasks_753_);
v___x_760_ = v_reuseFailAlloc_844_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v_fileName_762_; lean_object* v_fileMap_763_; lean_object* v_currRecDepth_764_; lean_object* v_cmdPos_765_; lean_object* v_macroStack_766_; lean_object* v_quotContext_x3f_767_; lean_object* v_currMacroScope_768_; lean_object* v_ref_769_; lean_object* v_cancelTk_x3f_770_; uint8_t v_suppressElabErrors_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_761_ = lean_st_ref_put(v_a_734_, v___x_760_);
v_fileName_762_ = lean_ctor_get(v_a_733_, 0);
v_fileMap_763_ = lean_ctor_get(v_a_733_, 1);
v_currRecDepth_764_ = lean_ctor_get(v_a_733_, 2);
v_cmdPos_765_ = lean_ctor_get(v_a_733_, 3);
v_macroStack_766_ = lean_ctor_get(v_a_733_, 4);
v_quotContext_x3f_767_ = lean_ctor_get(v_a_733_, 5);
v_currMacroScope_768_ = lean_ctor_get(v_a_733_, 6);
v_ref_769_ = lean_ctor_get(v_a_733_, 7);
v_cancelTk_x3f_770_ = lean_ctor_get(v_a_733_, 9);
v_suppressElabErrors_771_ = lean_ctor_get_uint8(v_a_733_, sizeof(void*)*10);
v___x_772_ = lean_box(0);
lean_inc(v_cancelTk_x3f_770_);
lean_inc(v_ref_769_);
lean_inc(v_currMacroScope_768_);
lean_inc(v_quotContext_x3f_767_);
lean_inc(v_macroStack_766_);
lean_inc(v_cmdPos_765_);
lean_inc(v_currRecDepth_764_);
lean_inc_ref(v_fileMap_763_);
lean_inc_ref(v_fileName_762_);
v___x_773_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_773_, 0, v_fileName_762_);
lean_ctor_set(v___x_773_, 1, v_fileMap_763_);
lean_ctor_set(v___x_773_, 2, v_currRecDepth_764_);
lean_ctor_set(v___x_773_, 3, v_cmdPos_765_);
lean_ctor_set(v___x_773_, 4, v_macroStack_766_);
lean_ctor_set(v___x_773_, 5, v_quotContext_x3f_767_);
lean_ctor_set(v___x_773_, 6, v_currMacroScope_768_);
lean_ctor_set(v___x_773_, 7, v_ref_769_);
lean_ctor_set(v___x_773_, 8, v___x_772_);
lean_ctor_set(v___x_773_, 9, v_cancelTk_x3f_770_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*10, v_suppressElabErrors_771_);
v___x_774_ = l_Lean_Elab_Command_elabCommandTopLevel(v_cmd_732_, v___x_773_, v_a_734_);
lean_dec_ref_known(v___x_773_, 10);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_832_; 
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v___x_774_, 0);
lean_dec(v_unused_833_);
v___x_776_ = v___x_774_;
v_isShared_777_ = v_isSharedCheck_832_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_774_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_832_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_messages_780_; lean_object* v___y_782_; lean_object* v_snapshotTasks_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_778_ = lean_st_ref_get(v_a_734_);
v___x_779_ = lean_st_ref_get(v_a_734_);
v_messages_780_ = lean_ctor_get(v___x_778_, 1);
lean_inc_ref(v_messages_780_);
lean_dec(v___x_778_);
v_snapshotTasks_821_ = lean_ctor_get(v___x_779_, 10);
lean_inc_ref(v_snapshotTasks_821_);
lean_dec(v___x_779_);
v___x_822_ = l_Lean_MessageLog_empty;
v___x_823_ = lean_array_get_size(v_snapshotTasks_821_);
v___x_824_ = lean_nat_dec_lt(v___x_757_, v___x_823_);
if (v___x_824_ == 0)
{
lean_dec_ref(v_snapshotTasks_821_);
v___y_782_ = v___x_822_;
goto v___jp_781_;
}
else
{
uint8_t v___x_825_; 
v___x_825_ = lean_nat_dec_le(v___x_823_, v___x_823_);
if (v___x_825_ == 0)
{
if (v___x_824_ == 0)
{
lean_dec_ref(v_snapshotTasks_821_);
v___y_782_ = v___x_822_;
goto v___jp_781_;
}
else
{
size_t v___x_826_; size_t v___x_827_; lean_object* v___x_828_; 
v___x_826_ = ((size_t)0ULL);
v___x_827_ = lean_usize_of_nat(v___x_823_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_821_, v___x_826_, v___x_827_, v___x_822_);
lean_dec_ref(v_snapshotTasks_821_);
v___y_782_ = v___x_828_;
goto v___jp_781_;
}
}
else
{
size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; 
v___x_829_ = ((size_t)0ULL);
v___x_830_ = lean_usize_of_nat(v___x_823_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_runAndCollectMessages_spec__1(v_snapshotTasks_821_, v___x_829_, v___x_830_, v___x_822_);
lean_dec_ref(v_snapshotTasks_821_);
v___y_782_ = v___x_831_;
goto v___jp_781_;
}
}
v___jp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_env_785_; lean_object* v_scopes_786_; lean_object* v_usedQuotCtxts_787_; lean_object* v_nextMacroScope_788_; lean_object* v_maxRecDepth_789_; lean_object* v_ngen_790_; lean_object* v_auxDeclNGen_791_; lean_object* v_infoState_792_; lean_object* v_traceState_793_; lean_object* v_prevLinterStates_794_; lean_object* v_codeQualityEntryTasks_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_818_; 
v___x_783_ = l_Lean_MessageLog_append(v_messages_780_, v___y_782_);
v___x_784_ = lean_st_ref_take(v_a_734_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
v_scopes_786_ = lean_ctor_get(v___x_784_, 2);
v_usedQuotCtxts_787_ = lean_ctor_get(v___x_784_, 3);
v_nextMacroScope_788_ = lean_ctor_get(v___x_784_, 4);
v_maxRecDepth_789_ = lean_ctor_get(v___x_784_, 5);
v_ngen_790_ = lean_ctor_get(v___x_784_, 6);
v_auxDeclNGen_791_ = lean_ctor_get(v___x_784_, 7);
v_infoState_792_ = lean_ctor_get(v___x_784_, 8);
v_traceState_793_ = lean_ctor_get(v___x_784_, 9);
v_prevLinterStates_794_ = lean_ctor_get(v___x_784_, 11);
v_codeQualityEntryTasks_795_ = lean_ctor_get(v___x_784_, 12);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_819_ = lean_ctor_get(v___x_784_, 10);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v___x_784_, 1);
lean_dec(v_unused_820_);
v___x_797_ = v___x_784_;
v_isShared_798_ = v_isSharedCheck_818_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_codeQualityEntryTasks_795_);
lean_inc(v_prevLinterStates_794_);
lean_inc(v_traceState_793_);
lean_inc(v_infoState_792_);
lean_inc(v_auxDeclNGen_791_);
lean_inc(v_ngen_790_);
lean_inc(v_maxRecDepth_789_);
lean_inc(v_nextMacroScope_788_);
lean_inc(v_usedQuotCtxts_787_);
lean_inc(v_scopes_786_);
lean_inc(v_env_785_);
lean_dec(v___x_784_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_818_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_runAndCollectMessages___closed__3));
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 10, v___x_799_);
lean_ctor_set(v___x_797_, 1, v___x_758_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_env_785_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_scopes_786_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_usedQuotCtxts_787_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_nextMacroScope_788_);
lean_ctor_set(v_reuseFailAlloc_817_, 5, v_maxRecDepth_789_);
lean_ctor_set(v_reuseFailAlloc_817_, 6, v_ngen_790_);
lean_ctor_set(v_reuseFailAlloc_817_, 7, v_auxDeclNGen_791_);
lean_ctor_set(v_reuseFailAlloc_817_, 8, v_infoState_792_);
lean_ctor_set(v_reuseFailAlloc_817_, 9, v_traceState_793_);
lean_ctor_set(v_reuseFailAlloc_817_, 10, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_817_, 11, v_prevLinterStates_794_);
lean_ctor_set(v_reuseFailAlloc_817_, 12, v_codeQualityEntryTasks_795_);
v___x_801_ = v_reuseFailAlloc_817_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = lean_st_ref_put(v_a_734_, v___x_801_);
v___x_803_ = l_Lean_MessageLog_toArray(v___x_783_);
lean_dec_ref(v___x_783_);
lean_inc_ref(v___x_803_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_803_);
v___x_805_ = v___x_776_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_816_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
v___x_807_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_734_, v_messages_737_, v_trees_740_, v___x_806_);
lean_dec_ref_known(v___x_806_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_807_, 0);
lean_dec(v_unused_815_);
v___x_809_ = v___x_807_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_dec(v___x_807_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_803_);
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_803_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
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
lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_834_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_774_, 1);
v___x_835_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages___lam__0(v_a_734_, v_messages_737_, v_trees_740_, v___x_772_);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v___x_835_, 0);
lean_dec(v_unused_843_);
v___x_837_ = v___x_835_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_dec(v___x_835_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 1);
lean_ctor_set(v___x_837_, 0, v_a_834_);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_834_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages___boxed(lean_object* v_cmd_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v_cmd_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(lean_object* v_type_852_, lean_object* v_e_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
uint8_t v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = 1;
v___x_860_ = 1;
v___x_861_ = l_Lean_Meta_evalExpr___redArg(v_type_852_, v_e_853_, v___x_859_, v___x_860_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1___boxed(lean_object* v_type_862_, lean_object* v_e_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_unsafe__1(v_type_862_, v_e_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(lean_object* v_e_870_, lean_object* v___y_871_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_Expr_hasMVar(v_e_870_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_e_870_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; lean_object* v_mctx_876_; lean_object* v___x_877_; lean_object* v_fst_878_; lean_object* v_snd_879_; lean_object* v___x_880_; lean_object* v_cache_881_; lean_object* v_zetaDeltaFVarIds_882_; lean_object* v_postponed_883_; lean_object* v_diag_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_893_; 
v___x_875_ = lean_st_ref_get(v___y_871_);
v_mctx_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc_ref(v_mctx_876_);
lean_dec(v___x_875_);
v___x_877_ = l_Lean_instantiateMVarsCore(v_mctx_876_, v_e_870_);
v_fst_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_fst_878_);
v_snd_879_ = lean_ctor_get(v___x_877_, 1);
lean_inc(v_snd_879_);
lean_dec_ref(v___x_877_);
v___x_880_ = lean_st_ref_take(v___y_871_);
v_cache_881_ = lean_ctor_get(v___x_880_, 1);
v_zetaDeltaFVarIds_882_ = lean_ctor_get(v___x_880_, 2);
v_postponed_883_ = lean_ctor_get(v___x_880_, 3);
v_diag_884_ = lean_ctor_get(v___x_880_, 4);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_880_, 0);
lean_dec(v_unused_894_);
v___x_886_ = v___x_880_;
v_isShared_887_ = v_isSharedCheck_893_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_diag_884_);
lean_inc(v_postponed_883_);
lean_inc(v_zetaDeltaFVarIds_882_);
lean_inc(v_cache_881_);
lean_dec(v___x_880_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_893_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_snd_879_);
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_snd_879_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_cache_881_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_zetaDeltaFVarIds_882_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_postponed_883_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_diag_884_);
v___x_889_ = v_reuseFailAlloc_892_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_st_ref_put(v___y_871_, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v_fst_878_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg___boxed(lean_object* v_e_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_895_, v___y_896_);
lean_dec(v___y_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(lean_object* v_e_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_e_899_, v___y_903_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___boxed(lean_object* v_e_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0(v_e_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_916_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(0);
v___x_918_ = l_Lean_Elab_abortTermExceptionId;
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___x_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg(){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___closed__0);
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg___boxed(lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(lean_object* v_00_u03b1_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___boxed(lean_object* v_00_u03b1_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1(v_00_u03b1_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(lean_object* v___x_943_, lean_object* v___x_944_, uint8_t v___x_945_, lean_object* v___x_946_, uint8_t v___x_947_, lean_object* v___x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_943_, v___x_944_, v___x_945_, v___x_945_, v___x_946_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_958_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_947_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; lean_object* v_a_960_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; uint8_t v___x_1001_; 
lean_dec_ref_known(v___x_958_, 1);
v___x_959_ = l_Lean_instantiateMVars___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__0___redArg(v_a_957_, v___y_952_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v___x_1001_ = l_Lean_Expr_hasSyntheticSorry(v_a_960_);
if (v___x_1001_ == 0)
{
v___y_962_ = v___y_949_;
v___y_963_ = v___y_950_;
v___y_964_ = v___y_951_;
v___y_965_ = v___y_952_;
v___y_966_ = v___y_953_;
v___y_967_ = v___y_954_;
goto v___jp_961_;
}
else
{
lean_object* v___x_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_a_960_);
lean_dec_ref(v___x_948_);
v___x_1002_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
v___jp_961_:
{
lean_object* v___x_968_; 
lean_inc(v_a_960_);
v___x_968_ = l_Lean_Meta_getMVars(v_a_960_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = lean_box(0);
v___x_971_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_969_, v___x_970_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v_a_969_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; uint8_t v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = lean_unbox(v_a_972_);
lean_dec(v_a_972_);
if (v___x_973_ == 0)
{
uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_974_ = 1;
v___x_975_ = l_Lean_Meta_evalExpr___redArg(v___x_948_, v_a_960_, v___x_974_, v___x_945_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_a_960_);
lean_dec_ref(v___x_948_);
v___x_976_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__1___redArg();
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_a_960_);
lean_dec_ref(v___x_948_);
v_a_985_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_971_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_971_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_a_960_);
lean_dec_ref(v___x_948_);
v_a_993_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_968_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_968_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_a_957_);
lean_dec_ref(v___x_948_);
v_a_1011_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_958_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_958_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v___x_948_);
v_a_1019_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_956_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_956_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed(lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v___x_5858__boxed_1040_; uint8_t v___x_5860__boxed_1041_; lean_object* v_res_1042_; 
v___x_5858__boxed_1040_ = lean_unbox(v___x_1029_);
v___x_5860__boxed_1041_ = lean_unbox(v___x_1031_);
v_res_1042_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0(v___x_1027_, v___x_1028_, v___x_5858__boxed_1040_, v___x_1030_, v___x_5860__boxed_1041_, v___x_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1042_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__0);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__1);
v___x_1049_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
lean_ctor_set(v___x_1049_, 2, v___x_1048_);
lean_ctor_set(v___x_1049_, 3, v___x_1048_);
lean_ctor_set(v___x_1049_, 4, v___x_1048_);
lean_ctor_set(v___x_1049_, 5, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(lean_object* v_env_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; lean_object* v_nextMacroScope_1055_; lean_object* v_ngen_1056_; lean_object* v_auxDeclNGen_1057_; lean_object* v_traceState_1058_; lean_object* v_recordedDeps_1059_; lean_object* v_messages_1060_; lean_object* v_infoState_1061_; lean_object* v_snapshotTasks_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1088_; 
v___x_1054_ = lean_st_ref_take(v___y_1052_);
v_nextMacroScope_1055_ = lean_ctor_get(v___x_1054_, 1);
v_ngen_1056_ = lean_ctor_get(v___x_1054_, 2);
v_auxDeclNGen_1057_ = lean_ctor_get(v___x_1054_, 3);
v_traceState_1058_ = lean_ctor_get(v___x_1054_, 4);
v_recordedDeps_1059_ = lean_ctor_get(v___x_1054_, 6);
v_messages_1060_ = lean_ctor_get(v___x_1054_, 7);
v_infoState_1061_ = lean_ctor_get(v___x_1054_, 8);
v_snapshotTasks_1062_ = lean_ctor_get(v___x_1054_, 9);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1089_ = lean_ctor_get(v___x_1054_, 5);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v___x_1054_, 0);
lean_dec(v_unused_1090_);
v___x_1064_ = v___x_1054_;
v_isShared_1065_ = v_isSharedCheck_1088_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_snapshotTasks_1062_);
lean_inc(v_infoState_1061_);
lean_inc(v_messages_1060_);
lean_inc(v_recordedDeps_1059_);
lean_inc(v_traceState_1058_);
lean_inc(v_auxDeclNGen_1057_);
lean_inc(v_ngen_1056_);
lean_inc(v_nextMacroScope_1055_);
lean_dec(v___x_1054_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1088_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__2);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 5, v___x_1066_);
lean_ctor_set(v___x_1064_, 0, v_env_1050_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_env_1050_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_nextMacroScope_1055_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_ngen_1056_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_auxDeclNGen_1057_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v_traceState_1058_);
lean_ctor_set(v_reuseFailAlloc_1087_, 5, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1087_, 6, v_recordedDeps_1059_);
lean_ctor_set(v_reuseFailAlloc_1087_, 7, v_messages_1060_);
lean_ctor_set(v_reuseFailAlloc_1087_, 8, v_infoState_1061_);
lean_ctor_set(v_reuseFailAlloc_1087_, 9, v_snapshotTasks_1062_);
v___x_1068_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v_mctx_1071_; lean_object* v_zetaDeltaFVarIds_1072_; lean_object* v_postponed_1073_; lean_object* v_diag_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1085_; 
v___x_1069_ = lean_st_ref_put(v___y_1052_, v___x_1068_);
v___x_1070_ = lean_st_ref_take(v___y_1051_);
v_mctx_1071_ = lean_ctor_get(v___x_1070_, 0);
v_zetaDeltaFVarIds_1072_ = lean_ctor_get(v___x_1070_, 2);
v_postponed_1073_ = lean_ctor_get(v___x_1070_, 3);
v_diag_1074_ = lean_ctor_get(v___x_1070_, 4);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v___x_1070_, 1);
lean_dec(v_unused_1086_);
v___x_1076_ = v___x_1070_;
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_diag_1074_);
lean_inc(v_postponed_1073_);
lean_inc(v_zetaDeltaFVarIds_1072_);
lean_inc(v_mctx_1071_);
lean_dec(v___x_1070_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1085_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___closed__3);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1079_);
v___x_1081_ = v___x_1076_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_mctx_1071_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_zetaDeltaFVarIds_1072_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v_postponed_1073_);
lean_ctor_set(v_reuseFailAlloc_1084_, 4, v_diag_1074_);
v___x_1081_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_st_ref_put(v___y_1051_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1078_);
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg___boxed(lean_object* v_env_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec(v___y_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(lean_object* v_env_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v_env_1106_; lean_object* v_a_1108_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1105_ = lean_st_ref_get(v___y_1103_);
v_env_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_ref(v_env_1106_);
lean_dec(v___x_1105_);
v___x_1118_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1096_, v___y_1101_, v___y_1103_);
lean_dec_ref(v___x_1118_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
v___x_1119_ = lean_apply_7(v_x_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, lean_box(0));
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1106_, v___y_1101_, v___y_1103_);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1129_);
v___x_1123_ = v___x_1121_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v___x_1121_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v_a_1120_);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1120_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1130_; 
v_a_1130_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1119_, 1);
v_a_1108_ = v_a_1130_;
goto v___jp_1107_;
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v___x_1109_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1106_, v___y_1101_, v___y_1103_);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v___x_1109_, 0);
lean_dec(v_unused_1117_);
v___x_1111_ = v___x_1109_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v___x_1109_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 1);
lean_ctor_set(v___x_1111_, 0, v_a_1108_);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1108_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg___boxed(lean_object* v_env_1131_, lean_object* v_x_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1131_, v_x_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1140_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__10));
v___x_1162_ = l_String_toRawSubstring_x27(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__24));
v___x_1191_ = l_String_toRawSubstring_x27(v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__34));
v___x_1214_ = l_String_toRawSubstring_x27(v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__37));
v___x_1230_ = l_Lean_mkConst(v___x_1229_, v___x_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41);
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(lean_object* v_post_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_toCold_1241_; lean_object* v_ref_1242_; lean_object* v_quotContext_1243_; lean_object* v_currMacroScope_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v_env_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_toCold_1241_ = lean_ctor_get(v_a_1238_, 0);
v_ref_1242_ = lean_ctor_get(v_a_1238_, 2);
v_quotContext_1243_ = lean_ctor_get(v_toCold_1241_, 8);
v_currMacroScope_1244_ = lean_ctor_get(v_toCold_1241_, 9);
v___x_1245_ = 0;
v___x_1246_ = l_Lean_SourceInfo_fromRef(v_ref_1242_, v___x_1245_);
v___x_1247_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__3));
v___x_1248_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__4));
lean_inc_n(v___x_1246_, 14);
v___x_1249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1246_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
v___x_1250_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__7));
v___x_1251_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__9));
v___x_1252_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__11);
v___x_1253_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__13));
lean_inc_n(v_currMacroScope_1244_, 3);
lean_inc_n(v_quotContext_1243_, 3);
v___x_1254_ = l_Lean_addMacroScope(v_quotContext_1243_, v___x_1253_, v_currMacroScope_1244_);
v___x_1255_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__15));
v___x_1256_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1246_);
lean_ctor_set(v___x_1256_, 1, v___x_1252_);
lean_ctor_set(v___x_1256_, 2, v___x_1254_);
lean_ctor_set(v___x_1256_, 3, v___x_1255_);
v___x_1257_ = l_Lean_Syntax_node1(v___x_1246_, v___x_1251_, v___x_1256_);
v___x_1258_ = l_Lean_Syntax_node1(v___x_1246_, v___x_1250_, v___x_1257_);
v___x_1259_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__16));
v___x_1260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1246_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__18));
v___x_1262_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__20));
v___x_1263_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__21));
v___x_1264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1246_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__23));
v___x_1266_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__25);
v___x_1267_ = lean_box(0);
v___x_1268_ = l_Lean_addMacroScope(v_quotContext_1243_, v___x_1267_, v_currMacroScope_1244_);
v___x_1269_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__32));
v___x_1270_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1246_);
lean_ctor_set(v___x_1270_, 1, v___x_1266_);
lean_ctor_set(v___x_1270_, 2, v___x_1268_);
lean_ctor_set(v___x_1270_, 3, v___x_1269_);
v___x_1271_ = l_Lean_Syntax_node1(v___x_1246_, v___x_1265_, v___x_1270_);
v___x_1272_ = l_Lean_Syntax_node2(v___x_1246_, v___x_1262_, v___x_1264_, v___x_1271_);
v___x_1273_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__33));
v___x_1274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1246_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__35);
v___x_1276_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__36));
v___x_1277_ = l_Lean_addMacroScope(v_quotContext_1243_, v___x_1276_, v_currMacroScope_1244_);
v___x_1278_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__39));
v___x_1279_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1246_);
lean_ctor_set(v___x_1279_, 1, v___x_1275_);
lean_ctor_set(v___x_1279_, 2, v___x_1277_);
lean_ctor_set(v___x_1279_, 3, v___x_1278_);
v___x_1280_ = l_Lean_Syntax_node1(v___x_1246_, v___x_1251_, v___x_1279_);
v___x_1281_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__40));
v___x_1282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1246_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l_Lean_Syntax_node5(v___x_1246_, v___x_1261_, v___x_1272_, v_post_1233_, v___x_1274_, v___x_1280_, v___x_1282_);
v___x_1284_ = l_Lean_Syntax_node4(v___x_1246_, v___x_1248_, v___x_1249_, v___x_1258_, v___x_1260_, v___x_1283_);
v___x_1285_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__41);
v___x_1286_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42, &l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42_once, _init_l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___closed__42);
v___x_1287_ = 1;
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_box(v___x_1287_);
v___x_1290_ = lean_box(v___x_1245_);
v___f_1291_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1291_, 0, v___x_1284_);
lean_closure_set(v___f_1291_, 1, v___x_1286_);
lean_closure_set(v___f_1291_, 2, v___x_1289_);
lean_closure_set(v___f_1291_, 3, v___x_1288_);
lean_closure_set(v___f_1291_, 4, v___x_1290_);
lean_closure_set(v___f_1291_, 5, v___x_1285_);
v___x_1292_ = lean_st_ref_get(v_a_1239_);
v_env_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc_ref(v_env_1293_);
lean_dec(v___x_1292_);
v___x_1294_ = l_Lean_Environment_unlockAsync(v_env_1293_);
v___x_1295_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v___x_1294_, v___f_1291_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor___boxed(lean_object* v_post_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(lean_object* v_env_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___redArg(v_env_1305_, v___y_1309_, v___y_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2___boxed(lean_object* v_env_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2_spec__2(v_env_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(lean_object* v_00_u03b1_1323_, lean_object* v_env_1324_, lean_object* v_x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___redArg(v_env_1324_, v_x_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2___boxed(lean_object* v_00_u03b1_1334_, lean_object* v_env_1335_, lean_object* v_x_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_withEnv___at___00__private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor_spec__2(v_00_u03b1_1334_, v_env_1335_, v_x_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(lean_object* v_post_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Lean_PostprocessTraces_Basic_0__Lean_Elab_PostprocessTraces_evalPostprocessor(v_post_1345_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed(lean_object* v_post_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0(v_post_1355_, v_x_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec_ref(v_x_1356_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(lean_object* v_a_1365_, lean_object* v_traceState_1366_, lean_object* v_a_x3f_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v_env_1370_; lean_object* v_messages_1371_; lean_object* v_scopes_1372_; lean_object* v_usedQuotCtxts_1373_; lean_object* v_nextMacroScope_1374_; lean_object* v_maxRecDepth_1375_; lean_object* v_ngen_1376_; lean_object* v_auxDeclNGen_1377_; lean_object* v_infoState_1378_; lean_object* v_snapshotTasks_1379_; lean_object* v_prevLinterStates_1380_; lean_object* v_codeQualityEntryTasks_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
v___x_1369_ = lean_st_ref_take(v_a_1365_);
v_env_1370_ = lean_ctor_get(v___x_1369_, 0);
v_messages_1371_ = lean_ctor_get(v___x_1369_, 1);
v_scopes_1372_ = lean_ctor_get(v___x_1369_, 2);
v_usedQuotCtxts_1373_ = lean_ctor_get(v___x_1369_, 3);
v_nextMacroScope_1374_ = lean_ctor_get(v___x_1369_, 4);
v_maxRecDepth_1375_ = lean_ctor_get(v___x_1369_, 5);
v_ngen_1376_ = lean_ctor_get(v___x_1369_, 6);
v_auxDeclNGen_1377_ = lean_ctor_get(v___x_1369_, 7);
v_infoState_1378_ = lean_ctor_get(v___x_1369_, 8);
v_snapshotTasks_1379_ = lean_ctor_get(v___x_1369_, 10);
v_prevLinterStates_1380_ = lean_ctor_get(v___x_1369_, 11);
v_codeQualityEntryTasks_1381_ = lean_ctor_get(v___x_1369_, 12);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v___x_1369_, 9);
lean_dec(v_unused_1392_);
v___x_1383_ = v___x_1369_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1381_);
lean_inc(v_prevLinterStates_1380_);
lean_inc(v_snapshotTasks_1379_);
lean_inc(v_infoState_1378_);
lean_inc(v_auxDeclNGen_1377_);
lean_inc(v_ngen_1376_);
lean_inc(v_maxRecDepth_1375_);
lean_inc(v_nextMacroScope_1374_);
lean_inc(v_usedQuotCtxts_1373_);
lean_inc(v_scopes_1372_);
lean_inc(v_messages_1371_);
lean_inc(v_env_1370_);
lean_dec(v___x_1369_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = lean_box(0);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 9, v_traceState_1366_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_env_1370_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_messages_1371_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_scopes_1372_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_usedQuotCtxts_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_nextMacroScope_1374_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v_maxRecDepth_1375_);
lean_ctor_set(v_reuseFailAlloc_1390_, 6, v_ngen_1376_);
lean_ctor_set(v_reuseFailAlloc_1390_, 7, v_auxDeclNGen_1377_);
lean_ctor_set(v_reuseFailAlloc_1390_, 8, v_infoState_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 9, v_traceState_1366_);
lean_ctor_set(v_reuseFailAlloc_1390_, 10, v_snapshotTasks_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 11, v_prevLinterStates_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 12, v_codeQualityEntryTasks_1381_);
v___x_1387_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_st_ref_put(v_a_1365_, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1385_);
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1___boxed(lean_object* v_a_1393_, lean_object* v_traceState_1394_, lean_object* v_a_x3f_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1393_, v_traceState_1394_, v_a_x3f_1395_);
lean_dec(v_a_x3f_1395_);
lean_dec(v_a_1393_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(lean_object* v_a_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_apply_4(v_a_1398_, v___y_1399_, v___y_1400_, v___y_1401_, lean_box(0));
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed(lean_object* v_a_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2(v_a_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object* v_post_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v_traceState_1416_; lean_object* v_r_1417_; 
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1414_, 0, v_post_1410_);
v___x_1415_ = lean_st_ref_get(v_a_1412_);
v_traceState_1416_ = lean_ctor_get(v___x_1415_, 9);
lean_inc_ref(v_traceState_1416_);
lean_dec(v___x_1415_);
v_r_1417_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_1414_, v_a_1411_, v_a_1412_);
if (lean_obj_tag(v_r_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1435_; 
v_a_1418_ = lean_ctor_get(v_r_1417_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_r_1417_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1420_ = v_r_1417_;
v_isShared_1421_ = v_isSharedCheck_1435_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v_r_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1435_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___f_1422_; lean_object* v___x_1424_; 
lean_inc(v_a_1418_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__2___boxed), 5, 1);
lean_closure_set(v___f_1422_, 0, v_a_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 1);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1418_);
v___x_1424_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v___x_1425_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1412_, v_traceState_1416_, v___x_1424_);
lean_dec_ref(v___x_1424_);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v___x_1425_, 0);
lean_dec(v_unused_1433_);
v___x_1427_ = v___x_1425_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_dec(v___x_1425_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___f_1422_);
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___f_1422_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_a_1436_ = lean_ctor_get(v_r_1417_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v_r_1417_, 1);
v___x_1437_ = lean_box(0);
v___x_1438_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___lam__1(v_a_1412_, v_traceState_1416_, v___x_1437_);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1446_);
v___x_1440_ = v___x_1438_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_dec(v___x_1438_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 1);
lean_ctor_set(v___x_1440_, 0, v_a_1436_);
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1436_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel___boxed(lean_object* v_post_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1451_;
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
