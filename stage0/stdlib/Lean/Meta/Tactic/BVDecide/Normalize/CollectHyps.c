// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.LitValues
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqcs(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqBoolTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqBoolFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Platform"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numBits"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__1_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 13, 33, 186, 170, 198, 65, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getBitVecValue_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getUInt64Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getInt64Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__3_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__5_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__9_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__13_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__15_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__17_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__19_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__21_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__23_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__25_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__26_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getUInt8Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__27_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getUInt16Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__28_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getUInt32Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__29_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getInt8Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__30_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getInt16Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__31_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getInt32Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__32_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Collected initial hypotheses"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__9___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___boxed(lean_object**);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___redArg(lean_object* v_hyp_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_st_ref_take(v_a_2_);
v___x_5_ = lean_array_push(v___x_4_, v_hyp_1_);
v___x_6_ = lean_st_ref_set(v_a_2_, v___x_5_);
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___redArg___boxed(lean_object* v_hyp_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___redArg(v_hyp_9_, v_a_10_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp(lean_object* v_hyp_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_26_ = lean_st_ref_take(v_a_14_);
v___x_27_ = lean_array_push(v___x_26_, v_hyp_13_);
v___x_28_ = lean_st_ref_set(v_a_14_, v___x_27_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___boxed(lean_object* v_hyp_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp(v_hyp_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
lean_dec(v_a_33_);
lean_dec(v_a_32_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(uint8_t v___x_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
else
{
lean_object* v_head_48_; lean_object* v_tail_49_; lean_object* v___x_50_; 
v_head_48_ = lean_ctor_get(v_x_46_, 0);
lean_inc_n(v_head_48_, 2);
v_tail_49_ = lean_ctor_get(v_x_46_, 1);
lean_inc(v_tail_49_);
lean_dec_ref_known(v_x_46_, 2);
v___x_50_ = l_Lean_Meta_Sym_getNatValue_x3f(v_head_48_);
if (lean_obj_tag(v___x_50_) == 0)
{
if (v___x_45_ == 0)
{
lean_dec(v_head_48_);
v_x_46_ = v_tail_49_;
goto _start;
}
else
{
lean_object* v___x_52_; 
lean_dec(v_tail_49_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_head_48_);
return v___x_52_;
}
}
else
{
lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
lean_dec(v_tail_49_);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; 
v_unused_60_ = lean_ctor_get(v___x_50_, 0);
lean_dec(v_unused_60_);
v___x_54_ = v___x_50_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_dec(v___x_50_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v_head_48_);
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_head_48_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0___boxed(lean_object* v___x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v___x_9114__boxed_63_; lean_object* v_res_64_; 
v___x_9114__boxed_63_ = lean_unbox(v___x_61_);
v_res_64_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(v___x_9114__boxed_63_, v_x_62_);
return v_res_64_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__4(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_box(0);
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__3));
v___x_74_ = l_Lean_mkConst(v___x_73_, v___x_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits(lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___closed__4);
v___x_88_ = l_Lean_Meta_Sym_shareCommonInc(v___x_87_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_151_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_151_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_151_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_151_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_93_ = lean_st_ref_get(v_a_76_);
v___x_94_ = 0;
lean_inc(v_a_89_);
v___x_95_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_93_, v_a_89_, v___x_94_);
lean_dec(v___x_93_);
v___x_96_ = l_List_isEmpty___redArg(v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(v___x_96_, v___x_95_);
if (lean_obj_tag(v___x_97_) == 1)
{
lean_object* v_val_98_; lean_object* v___x_99_; 
lean_del_object(v___x_91_);
v_val_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_n(v_val_98_, 2);
lean_dec_ref_known(v___x_97_, 1);
lean_inc(v_a_89_);
v___x_99_ = l_Lean_Meta_mkEq(v_a_89_, v_val_98_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_101_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_99_, 1);
v___x_101_ = l_Lean_Meta_Sym_shareCommonInc(v_a_100_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
lean_inc(v_a_79_);
lean_inc_ref(v_a_78_);
lean_inc(v_a_77_);
lean_inc(v_a_76_);
v___x_103_ = lean_grind_mk_eq_proof(v_a_89_, v_val_98_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_118_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_118_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_118_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_118_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_108_ = lean_st_ref_take(v_a_75_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_box(4);
v___x_111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v_a_102_);
lean_ctor_set(v___x_111_, 2, v_a_104_);
lean_ctor_set(v___x_111_, 3, v___x_110_);
v___x_112_ = lean_array_push(v___x_108_, v___x_111_);
v___x_113_ = lean_st_ref_set(v_a_75_, v___x_112_);
v___x_114_ = lean_box(0);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_114_);
v___x_116_ = v___x_106_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
lean_dec(v_a_102_);
v_a_119_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_103_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_103_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_dec(v_val_98_);
lean_dec(v_a_89_);
v_a_127_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_101_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_101_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
lean_dec(v_val_98_);
lean_dec(v_a_89_);
v_a_135_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_99_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_99_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_145_; 
lean_dec(v___x_97_);
lean_dec(v_a_89_);
v___x_143_ = lean_box(0);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_143_);
v___x_145_ = v___x_91_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v___x_95_);
lean_dec(v_a_89_);
v___x_147_ = lean_box(0);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_147_);
v___x_149_ = v___x_91_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_88_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_88_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___boxed(lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits(v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec(v_a_161_);
lean_dec(v_a_160_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0___redArg(lean_object* v_getConst_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v___x_175_; 
lean_dec_ref(v_getConst_173_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_head_176_; lean_object* v_tail_177_; lean_object* v___x_178_; 
v_head_176_ = lean_ctor_get(v_x_174_, 0);
lean_inc_n(v_head_176_, 2);
v_tail_177_ = lean_ctor_get(v_x_174_, 1);
lean_inc(v_tail_177_);
lean_dec_ref_known(v_x_174_, 2);
lean_inc_ref(v_getConst_173_);
v___x_178_ = lean_apply_1(v_getConst_173_, v_head_176_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_dec(v_head_176_);
v_x_174_ = v_tail_177_;
goto _start;
}
else
{
lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v_tail_177_);
lean_dec_ref(v_getConst_173_);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v___x_178_, 0);
lean_dec(v_unused_187_);
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v_head_176_);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_head_176_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(lean_object* v_eqc_188_, lean_object* v_default_189_, lean_object* v_getConst_190_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0___redArg(v_getConst_190_, v_eqc_188_);
if (lean_obj_tag(v___x_192_) == 1)
{
lean_object* v___x_193_; 
lean_dec_ref(v_default_189_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v___x_192_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_default_189_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg___boxed(lean_object* v_eqc_196_, lean_object* v_default_197_, lean_object* v_getConst_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_196_, v_default_197_, v_getConst_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType(lean_object* v_00_u03b1_201_, lean_object* v_eqc_202_, lean_object* v_default_203_, lean_object* v_getConst_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_202_, v_default_203_, v_getConst_204_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___boxed(lean_object* v_00_u03b1_218_, lean_object* v_eqc_219_, lean_object* v_default_220_, lean_object* v_getConst_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType(v_00_u03b1_218_, v_eqc_219_, v_default_220_, v_getConst_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec(v_a_223_);
lean_dec(v_a_222_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0(lean_object* v_00_u03b1_235_, lean_object* v_getConst_236_, lean_object* v_x_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0___redArg(v_getConst_236_, v_x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(lean_object* v_x_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
else
{
lean_object* v_head_247_; lean_object* v_tail_248_; lean_object* v___x_249_; 
v_head_247_ = lean_ctor_get(v_x_239_, 0);
lean_inc_n(v_head_247_, 2);
v_tail_248_ = lean_ctor_get(v_x_239_, 1);
lean_inc(v_tail_248_);
lean_dec_ref_known(v_x_239_, 2);
v___x_249_ = l_Lean_Meta_isConstructorApp(v_head_247_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_260_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_260_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_260_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_260_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint8_t v___x_254_; 
v___x_254_ = lean_unbox(v_a_250_);
lean_dec(v_a_250_);
if (v___x_254_ == 0)
{
lean_del_object(v___x_252_);
lean_dec(v_head_247_);
v_x_239_ = v_tail_248_;
goto _start;
}
else
{
lean_object* v___x_256_; lean_object* v___x_258_; 
lean_dec(v_tail_248_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v_head_247_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_256_);
v___x_258_ = v___x_252_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_tail_248_);
lean_dec(v_head_247_);
v_a_261_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_249_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_249_);
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
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg___boxed(lean_object* v_x_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(v_x_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(lean_object* v_eqc_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; lean_object* v_elem_335_; lean_object* v___x_336_; 
v___x_334_ = l_Lean_instInhabitedExpr;
v_elem_335_ = l_List_head_x21___redArg(v___x_334_, v_eqc_321_);
lean_inc(v_elem_335_);
v___x_336_ = l_Lean_Meta_Grind_getRootENode___redArg(v_elem_335_, v_a_323_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
lean_inc(v_elem_335_);
v___x_338_ = l_Lean_Meta_Sym_inferType(v_elem_335_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_527_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_527_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_527_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_527_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; 
lean_inc(v_a_339_);
v___x_343_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_339_, v_a_330_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_518_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_518_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_518_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_518_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_self_348_; uint8_t v___y_350_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_self_348_ = lean_ctor_get(v_a_337_, 0);
lean_inc_ref(v_self_348_);
lean_dec(v_a_337_);
v___x_411_ = l_Lean_Expr_cleanupAnnotations(v_a_344_);
v___x_412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__4));
v___x_413_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__6));
v___x_415_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__8));
v___x_417_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__10));
v___x_419_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__12));
v___x_421_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__14));
v___x_423_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__16));
v___x_425_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__18));
v___x_427_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__20));
v___x_429_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__22));
v___x_431_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__24));
v___x_433_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_432_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
lean_dec(v_elem_335_);
v___x_434_ = l_Lean_Expr_isApp(v___x_411_);
if (v___x_434_ == 0)
{
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
v___y_358_ = v_a_322_;
v___y_359_ = v_a_323_;
v___y_360_ = v_a_324_;
v___y_361_ = v_a_325_;
v___y_362_ = v_a_326_;
v___y_363_ = v_a_327_;
v___y_364_ = v_a_328_;
v___y_365_ = v_a_329_;
v___y_366_ = v_a_330_;
v___y_367_ = v_a_331_;
v___y_368_ = v_a_332_;
goto v___jp_357_;
}
else
{
lean_object* v_arg_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_arg_435_ = lean_ctor_get(v___x_411_, 1);
lean_inc_ref(v_arg_435_);
v___x_436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_411_);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__26));
v___x_438_ = l_Lean_Expr_isConstOf(v___x_436_, v___x_437_);
lean_dec_ref(v___x_436_);
if (v___x_438_ == 0)
{
lean_dec_ref(v_arg_435_);
lean_del_object(v___x_346_);
v___y_358_ = v_a_322_;
v___y_359_ = v_a_323_;
v___y_360_ = v_a_324_;
v___y_361_ = v_a_325_;
v___y_362_ = v_a_326_;
v___y_363_ = v_a_327_;
v___y_364_ = v_a_328_;
v___y_365_ = v_a_329_;
v___y_366_ = v_a_330_;
v___y_367_ = v_a_331_;
v___y_368_ = v_a_332_;
goto v___jp_357_;
}
else
{
lean_object* v___x_439_; 
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
v___x_439_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_435_);
if (lean_obj_tag(v___x_439_) == 0)
{
v___y_350_ = v___x_433_;
goto v___jp_349_;
}
else
{
lean_dec_ref_known(v___x_439_, 1);
v___y_350_ = v___x_438_;
goto v___jp_349_;
}
}
}
}
else
{
lean_object* v___x_440_; 
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_eqc_321_);
lean_inc(v_elem_335_);
v___x_440_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_elem_335_, v_a_323_, v_a_327_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; uint8_t v___x_442_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = lean_unbox(v_a_441_);
lean_dec(v_a_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_elem_335_, v_a_323_, v_a_327_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_471_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_471_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_471_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_471_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; 
v___x_448_ = lean_unbox(v_a_444_);
lean_dec(v_a_444_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v_self_348_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
else
{
lean_object* v___x_453_; 
lean_del_object(v___x_446_);
lean_dec_ref(v_self_348_);
v___x_453_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_327_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_462_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_462_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_a_454_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_a_463_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_453_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_453_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_self_348_);
v_a_472_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_443_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_443_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
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
else
{
lean_object* v___x_480_; 
lean_dec_ref(v_self_348_);
lean_dec(v_elem_335_);
v___x_480_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_327_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v_a_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_a_490_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_480_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_480_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v_self_348_);
lean_dec(v_elem_335_);
v_a_498_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_440_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_440_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
v___x_506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__27));
v___x_507_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_506_);
return v___x_507_;
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
v___x_508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__28));
v___x_509_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_508_);
return v___x_509_;
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
v___x_510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__29));
v___x_511_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_510_);
return v___x_511_;
}
}
else
{
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
goto v___jp_405_;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
v___x_512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__30));
v___x_513_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_512_);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
v___x_514_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__31));
v___x_515_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_514_);
return v___x_515_;
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__32));
v___x_517_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_516_);
return v___x_517_;
}
}
else
{
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
goto v___jp_408_;
}
}
else
{
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
goto v___jp_405_;
}
}
else
{
lean_dec_ref(v___x_411_);
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_elem_335_);
goto v___jp_408_;
}
v___jp_349_:
{
if (v___y_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec_ref(v_self_348_);
lean_dec(v_eqc_321_);
v___x_351_ = lean_box(0);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_351_);
v___x_353_ = v___x_346_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_del_object(v___x_346_);
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0));
v___x_356_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_355_);
return v___x_356_;
}
}
v___jp_357_:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Expr_getAppFn_x27(v_a_339_);
lean_dec(v_a_339_);
if (lean_obj_tag(v___x_369_) == 4)
{
lean_object* v_declName_370_; lean_object* v___x_371_; 
lean_del_object(v___x_341_);
v_declName_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_declName_370_);
lean_dec_ref_known(v___x_369_, 2);
v___x_371_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_declName_370_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_392_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_392_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_392_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_392_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint8_t v___x_376_; 
v___x_376_ = lean_unbox(v_a_372_);
lean_dec(v_a_372_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_379_; 
lean_dec_ref(v_self_348_);
lean_dec(v_eqc_321_);
v___x_377_ = lean_box(0);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_377_);
v___x_379_ = v___x_374_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
else
{
lean_object* v___x_381_; 
lean_del_object(v___x_374_);
v___x_381_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(v_eqc_321_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
if (lean_obj_tag(v_a_382_) == 1)
{
lean_dec_ref_known(v_a_382_, 1);
lean_dec_ref(v_self_348_);
return v___x_381_;
}
else
{
lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_a_382_);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v___x_381_, 0);
lean_dec(v_unused_391_);
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v_self_348_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
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
}
}
else
{
lean_dec_ref(v_self_348_);
return v___x_381_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_self_348_);
lean_dec(v_eqc_321_);
v_a_393_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_371_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_371_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_403_; 
lean_dec_ref(v___x_369_);
lean_dec_ref(v_self_348_);
lean_dec(v_eqc_321_);
v___x_401_ = lean_box(0);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_401_);
v___x_403_ = v___x_341_;
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
v___jp_405_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1));
v___x_407_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_406_);
return v___x_407_;
}
v___jp_408_:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__2));
v___x_410_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_eqc_321_, v_self_348_, v___x_409_);
return v___x_410_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_341_);
lean_dec(v_a_339_);
lean_dec(v_a_337_);
lean_dec(v_elem_335_);
lean_dec(v_eqc_321_);
v_a_519_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_343_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_343_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_a_337_);
lean_dec(v_elem_335_);
lean_dec(v_eqc_321_);
v_a_528_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_338_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_338_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_elem_335_);
lean_dec(v_eqc_321_);
v_a_536_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_336_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_336_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___boxed(lean_object* v_eqc_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_eqc_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec(v_a_546_);
lean_dec(v_a_545_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0(lean_object* v_x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(v_x_558_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___boxed(lean_object* v_x_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0(v_x_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec(v___y_574_);
lean_dec(v___y_573_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(lean_object* v_val_586_, uint8_t v___y_587_, lean_object* v_as_x27_588_, lean_object* v_b_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
if (lean_obj_tag(v_as_x27_588_) == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v_val_586_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v_b_589_);
return v___x_602_;
}
else
{
lean_object* v_head_603_; lean_object* v_tail_604_; lean_object* v___x_605_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; uint8_t v___x_655_; 
v_head_603_ = lean_ctor_get(v_as_x27_588_, 0);
v_tail_604_ = lean_ctor_get(v_as_x27_588_, 1);
v___x_605_ = lean_box(0);
v___x_655_ = lean_expr_eqv(v_head_603_, v_val_586_);
if (v___x_655_ == 0)
{
if (v___y_587_ == 0)
{
lean_object* v___x_656_; 
lean_inc_ref(v_val_586_);
lean_inc(v_head_603_);
v___x_656_ = l_Lean_Meta_Grind_hasSameType(v_head_603_, v_val_586_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; uint8_t v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = lean_unbox(v_a_657_);
lean_dec(v_a_657_);
if (v___x_658_ == 0)
{
v_as_x27_588_ = v_tail_604_;
v_b_589_ = v___x_605_;
goto _start;
}
else
{
v___y_607_ = v___y_590_;
v___y_608_ = v___y_591_;
v___y_609_ = v___y_592_;
v___y_610_ = v___y_593_;
v___y_611_ = v___y_594_;
v___y_612_ = v___y_595_;
v___y_613_ = v___y_596_;
v___y_614_ = v___y_597_;
v___y_615_ = v___y_598_;
v___y_616_ = v___y_599_;
v___y_617_ = v___y_600_;
goto v___jp_606_;
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_val_586_);
v_a_660_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_656_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_656_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
else
{
v___y_607_ = v___y_590_;
v___y_608_ = v___y_591_;
v___y_609_ = v___y_592_;
v___y_610_ = v___y_593_;
v___y_611_ = v___y_594_;
v___y_612_ = v___y_595_;
v___y_613_ = v___y_596_;
v___y_614_ = v___y_597_;
v___y_615_ = v___y_598_;
v___y_616_ = v___y_599_;
v___y_617_ = v___y_600_;
goto v___jp_606_;
}
}
else
{
v_as_x27_588_ = v_tail_604_;
v_b_589_ = v___x_605_;
goto _start;
}
v___jp_606_:
{
lean_object* v___x_618_; 
lean_inc_ref(v_val_586_);
lean_inc(v_head_603_);
v___x_618_ = l_Lean_Meta_mkEq(v_head_603_, v_val_586_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = l_Lean_Meta_Sym_shareCommonInc(v_a_619_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v___y_615_);
lean_inc_ref(v___y_614_);
lean_inc(v___y_613_);
lean_inc_ref(v___y_612_);
lean_inc(v___y_611_);
lean_inc_ref(v___y_610_);
lean_inc(v___y_609_);
lean_inc(v___y_608_);
lean_inc_ref(v_val_586_);
lean_inc(v_head_603_);
v___x_622_ = lean_grind_mk_eq_proof(v_head_603_, v_val_586_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_st_ref_take(v___y_607_);
v___x_625_ = lean_box(0);
v___x_626_ = lean_box(4);
v___x_627_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v_a_621_);
lean_ctor_set(v___x_627_, 2, v_a_623_);
lean_ctor_set(v___x_627_, 3, v___x_626_);
v___x_628_ = lean_array_push(v___x_624_, v___x_627_);
v___x_629_ = lean_st_ref_set(v___y_607_, v___x_628_);
v_as_x27_588_ = v_tail_604_;
v_b_589_ = v___x_605_;
goto _start;
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_621_);
lean_dec_ref(v_val_586_);
v_a_631_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_622_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_622_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_val_586_);
v_a_639_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_620_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_620_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v_val_586_);
v_a_647_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_618_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_618_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg___boxed(lean_object* v_val_669_, lean_object* v___y_670_, lean_object* v_as_x27_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v___y_24581__boxed_685_; lean_object* v_res_686_; 
v___y_24581__boxed_685_ = lean_unbox(v___y_670_);
v_res_686_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_669_, v___y_24581__boxed_685_, v_as_x27_671_, v_b_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v_as_x27_671_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___redArg(lean_object* v_as_x27_687_, lean_object* v_b_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
if (lean_obj_tag(v_as_x27_687_) == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v_b_688_);
return v___x_701_;
}
else
{
lean_object* v_head_702_; lean_object* v_tail_703_; lean_object* v___x_704_; 
v_head_702_ = lean_ctor_get(v_as_x27_687_, 0);
v_tail_703_ = lean_ctor_get(v_as_x27_687_, 1);
lean_inc(v_head_702_);
v___x_704_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_head_702_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_box(0);
if (lean_obj_tag(v_a_705_) == 1)
{
lean_object* v_val_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_val_707_ = lean_ctor_get(v_a_705_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v_a_705_, 1);
v___x_708_ = l_Lean_instInhabitedExpr;
v___x_709_ = l_List_head_x21___redArg(v___x_708_, v_head_702_);
v___x_710_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_709_, v___y_690_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; uint8_t v___y_713_; uint8_t v_heqProofs_716_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v_heqProofs_716_ = lean_ctor_get_uint8(v_a_711_, sizeof(void*)*12 + 4);
lean_dec(v_a_711_);
if (v_heqProofs_716_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = 1;
v___y_713_ = v___x_717_;
goto v___jp_712_;
}
else
{
uint8_t v___x_718_; 
v___x_718_ = 0;
v___y_713_ = v___x_718_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_707_, v___y_713_, v_head_702_, v___x_706_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_dec_ref_known(v___x_714_, 1);
v_as_x27_687_ = v_tail_703_;
v_b_688_ = v___x_706_;
goto _start;
}
else
{
return v___x_714_;
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_val_707_);
v_a_719_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_710_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_710_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_dec(v_a_705_);
v_as_x27_687_ = v_tail_703_;
v_b_688_ = v___x_706_;
goto _start;
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_704_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_704_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___redArg___boxed(lean_object* v_as_x27_736_, lean_object* v_b_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___redArg(v_as_x27_736_, v_b_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v_as_x27_736_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_763_ = lean_st_ref_get(v_a_752_);
v___x_764_ = 0;
v___x_765_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_763_, v___x_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v___x_767_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___redArg(v___x_765_, v___x_766_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v___x_765_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_767_, 0);
lean_dec(v_unused_775_);
v___x_769_ = v___x_767_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_dec(v___x_767_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_766_);
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_766_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
else
{
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities___boxed(lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec(v_a_777_);
lean_dec(v_a_776_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(lean_object* v_val_789_, uint8_t v___y_790_, lean_object* v_as_791_, lean_object* v_as_x27_792_, lean_object* v_b_793_, lean_object* v_a_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_789_, v___y_790_, v_as_x27_792_, v_b_793_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___boxed(lean_object** _args){
lean_object* v_val_808_ = _args[0];
lean_object* v___y_809_ = _args[1];
lean_object* v_as_810_ = _args[2];
lean_object* v_as_x27_811_ = _args[3];
lean_object* v_b_812_ = _args[4];
lean_object* v_a_813_ = _args[5];
lean_object* v___y_814_ = _args[6];
lean_object* v___y_815_ = _args[7];
lean_object* v___y_816_ = _args[8];
lean_object* v___y_817_ = _args[9];
lean_object* v___y_818_ = _args[10];
lean_object* v___y_819_ = _args[11];
lean_object* v___y_820_ = _args[12];
lean_object* v___y_821_ = _args[13];
lean_object* v___y_822_ = _args[14];
lean_object* v___y_823_ = _args[15];
lean_object* v___y_824_ = _args[16];
lean_object* v___y_825_ = _args[17];
_start:
{
uint8_t v___y_24894__boxed_826_; lean_object* v_res_827_; 
v___y_24894__boxed_826_ = lean_unbox(v___y_809_);
v_res_827_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(v_val_808_, v___y_24894__boxed_826_, v_as_810_, v_as_x27_811_, v_b_812_, v_a_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec(v___y_815_);
lean_dec(v___y_814_);
lean_dec(v_as_x27_811_);
lean_dec(v_as_810_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(lean_object* v_as_828_, lean_object* v_as_x27_829_, lean_object* v_b_830_, lean_object* v_a_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___redArg(v_as_x27_829_, v_b_830_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___boxed(lean_object* v_as_845_, lean_object* v_as_x27_846_, lean_object* v_b_847_, lean_object* v_a_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(v_as_845_, v_as_x27_846_, v_b_847_, v_a_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec(v___y_850_);
lean_dec(v___y_849_);
lean_dec(v_as_x27_846_);
lean_dec(v_as_845_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(lean_object* v_a_862_, lean_object* v_as_x27_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
if (lean_obj_tag(v_as_x27_863_) == 0)
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v_b_864_);
return v___x_877_;
}
else
{
lean_object* v_head_878_; lean_object* v_tail_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_head_878_ = lean_ctor_get(v_as_x27_863_, 0);
v_tail_879_ = lean_ctor_get(v_as_x27_863_, 1);
v___x_880_ = lean_box(0);
v___x_881_ = lean_expr_eqv(v_head_878_, v_a_862_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_inc(v_head_878_);
v___x_882_ = l_Lean_mkNot(v_head_878_);
v___x_883_ = l_Lean_Meta_Sym_shareCommonInc(v___x_882_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
lean_inc(v_head_878_);
v___x_885_ = l_Lean_Meta_Grind_mkEqFalseProof(v_head_878_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = l_Lean_Meta_mkOfEqFalse(v_a_886_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = lean_st_ref_take(v___y_865_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_box(4);
v___x_892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v_a_884_);
lean_ctor_set(v___x_892_, 2, v_a_888_);
lean_ctor_set(v___x_892_, 3, v___x_891_);
v___x_893_ = lean_array_push(v___x_889_, v___x_892_);
v___x_894_ = lean_st_ref_set(v___y_865_, v___x_893_);
v_as_x27_863_ = v_tail_879_;
v_b_864_ = v___x_880_;
goto _start;
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_a_884_);
v_a_896_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_887_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_887_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_a_884_);
v_a_904_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_885_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_885_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v_a_912_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_883_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_883_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
v_as_x27_863_ = v_tail_879_;
v_b_864_ = v___x_880_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg___boxed(lean_object* v_a_921_, lean_object* v_as_x27_922_, lean_object* v_b_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_921_, v_as_x27_922_, v_b_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec(v___y_925_);
lean_dec(v___y_924_);
lean_dec(v_as_x27_922_);
lean_dec_ref(v_a_921_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_942_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc_n(v_a_950_, 2);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = lean_st_ref_get(v_a_938_);
v___x_952_ = 0;
v___x_953_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_951_, v_a_950_, v___x_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v___x_955_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_950_, v___x_953_, v___x_954_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v___x_953_);
lean_dec(v_a_950_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v___x_955_, 0);
lean_dec(v_unused_963_);
v___x_957_ = v___x_955_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_dec(v___x_955_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_954_);
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_954_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
return v___x_955_;
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_964_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_949_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_949_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse___boxed(lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec(v_a_973_);
lean_dec(v_a_972_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0(lean_object* v_a_985_, lean_object* v_as_986_, lean_object* v_as_x27_987_, lean_object* v_b_988_, lean_object* v_a_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_985_, v_as_x27_987_, v_b_988_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___boxed(lean_object** _args){
lean_object* v_a_1003_ = _args[0];
lean_object* v_as_1004_ = _args[1];
lean_object* v_as_x27_1005_ = _args[2];
lean_object* v_b_1006_ = _args[3];
lean_object* v_a_1007_ = _args[4];
lean_object* v___y_1008_ = _args[5];
lean_object* v___y_1009_ = _args[6];
lean_object* v___y_1010_ = _args[7];
lean_object* v___y_1011_ = _args[8];
lean_object* v___y_1012_ = _args[9];
lean_object* v___y_1013_ = _args[10];
lean_object* v___y_1014_ = _args[11];
lean_object* v___y_1015_ = _args[12];
lean_object* v___y_1016_ = _args[13];
lean_object* v___y_1017_ = _args[14];
lean_object* v___y_1018_ = _args[15];
lean_object* v___y_1019_ = _args[16];
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0(v_a_1003_, v_as_1004_, v_as_x27_1005_, v_b_1006_, v_a_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec(v_as_x27_1005_);
lean_dec(v_as_1004_);
lean_dec_ref(v_a_1003_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(lean_object* v_a_1021_, lean_object* v_as_x27_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
if (lean_obj_tag(v_as_x27_1022_) == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_b_1023_);
return v___x_1036_;
}
else
{
lean_object* v_head_1037_; lean_object* v_tail_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_head_1037_ = lean_ctor_get(v_as_x27_1022_, 0);
v_tail_1038_ = lean_ctor_get(v_as_x27_1022_, 1);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_expr_eqv(v_head_1037_, v_a_1021_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_inc(v_head_1037_);
v___x_1041_ = l_Lean_Meta_Grind_mkEqTrueProof(v_head_1037_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = l_Lean_Meta_mkOfEqTrue(v_a_1042_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = lean_st_ref_take(v___y_1024_);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_box(4);
lean_inc(v_head_1037_);
v___x_1048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v_head_1037_);
lean_ctor_set(v___x_1048_, 2, v_a_1044_);
lean_ctor_set(v___x_1048_, 3, v___x_1047_);
v___x_1049_ = lean_array_push(v___x_1045_, v___x_1048_);
v___x_1050_ = lean_st_ref_set(v___y_1024_, v___x_1049_);
v_as_x27_1022_ = v_tail_1038_;
v_b_1023_ = v___x_1039_;
goto _start;
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1043_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1043_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1041_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1041_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
v_as_x27_1022_ = v_tail_1038_;
v_b_1023_ = v___x_1039_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg___boxed(lean_object* v_a_1069_, lean_object* v_as_x27_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1069_, v_as_x27_1070_, v_b_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec(v_as_x27_1070_);
lean_dec_ref(v_a_1069_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1090_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_n(v_a_1098_, 2);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = lean_st_ref_get(v_a_1086_);
v___x_1100_ = 0;
v___x_1101_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1099_, v_a_1098_, v___x_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v___x_1103_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1098_, v___x_1101_, v___x_1102_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v___x_1101_);
lean_dec(v_a_1098_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v___x_1103_, 0);
lean_dec(v_unused_1111_);
v___x_1105_ = v___x_1103_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_dec(v___x_1103_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1102_);
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1102_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
else
{
return v___x_1103_;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_a_1112_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1097_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1097_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue___boxed(lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec(v_a_1120_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0(lean_object* v_a_1133_, lean_object* v_as_1134_, lean_object* v_as_x27_1135_, lean_object* v_b_1136_, lean_object* v_a_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1133_, v_as_x27_1135_, v_b_1136_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___boxed(lean_object** _args){
lean_object* v_a_1151_ = _args[0];
lean_object* v_as_1152_ = _args[1];
lean_object* v_as_x27_1153_ = _args[2];
lean_object* v_b_1154_ = _args[3];
lean_object* v_a_1155_ = _args[4];
lean_object* v___y_1156_ = _args[5];
lean_object* v___y_1157_ = _args[6];
lean_object* v___y_1158_ = _args[7];
lean_object* v___y_1159_ = _args[8];
lean_object* v___y_1160_ = _args[9];
lean_object* v___y_1161_ = _args[10];
lean_object* v___y_1162_ = _args[11];
lean_object* v___y_1163_ = _args[12];
lean_object* v___y_1164_ = _args[13];
lean_object* v___y_1165_ = _args[14];
lean_object* v___y_1166_ = _args[15];
lean_object* v___y_1167_ = _args[16];
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0(v_a_1151_, v_as_1152_, v_as_x27_1153_, v_b_1154_, v_a_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec(v_as_x27_1153_);
lean_dec(v_as_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1182_; 
lean_dec_ref_known(v___x_1181_, 1);
v___x_1182_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v___x_1183_; 
lean_dec_ref_known(v___x_1182_, 1);
v___x_1183_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref_known(v___x_1183_, 1);
v___x_1184_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits(v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
return v___x_1184_;
}
else
{
return v___x_1183_;
}
}
else
{
return v___x_1182_;
}
}
else
{
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go___boxed(lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec(v_a_1185_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0));
v___x_1212_ = lean_st_mk_ref(v___x_1211_);
v___x_1213_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(v___x_1212_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v___x_1213_, 0);
lean_dec(v_unused_1222_);
v___x_1215_ = v___x_1213_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_dec(v___x_1213_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_st_ref_get(v___x_1212_);
lean_dec(v___x_1212_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v___x_1212_);
v_a_1223_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1213_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1213_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___boxed(lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec(v_a_1231_);
return v_res_1242_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_unsigned_to_nat(32u);
v___x_1244_ = lean_mk_empty_array_with_capacity(v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1246_ = ((size_t)5ULL);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_unsigned_to_nat(32u);
v___x_1249_ = lean_mk_empty_array_with_capacity(v___x_1248_);
v___x_1250_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0);
v___x_1251_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v___x_1249_);
lean_ctor_set(v___x_1251_, 2, v___x_1247_);
lean_ctor_set(v___x_1251_, 3, v___x_1247_);
lean_ctor_set_usize(v___x_1251_, 4, v___x_1246_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; lean_object* v_traceState_1255_; lean_object* v_traces_1256_; lean_object* v___x_1257_; lean_object* v_traceState_1258_; lean_object* v_env_1259_; lean_object* v_nextMacroScope_1260_; lean_object* v_ngen_1261_; lean_object* v_auxDeclNGen_1262_; lean_object* v_cache_1263_; lean_object* v_messages_1264_; lean_object* v_infoState_1265_; lean_object* v_snapshotTasks_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1285_; 
v___x_1254_ = lean_st_ref_get(v___y_1252_);
v_traceState_1255_ = lean_ctor_get(v___x_1254_, 4);
lean_inc_ref(v_traceState_1255_);
lean_dec(v___x_1254_);
v_traces_1256_ = lean_ctor_get(v_traceState_1255_, 0);
lean_inc_ref(v_traces_1256_);
lean_dec_ref(v_traceState_1255_);
v___x_1257_ = lean_st_ref_take(v___y_1252_);
v_traceState_1258_ = lean_ctor_get(v___x_1257_, 4);
v_env_1259_ = lean_ctor_get(v___x_1257_, 0);
v_nextMacroScope_1260_ = lean_ctor_get(v___x_1257_, 1);
v_ngen_1261_ = lean_ctor_get(v___x_1257_, 2);
v_auxDeclNGen_1262_ = lean_ctor_get(v___x_1257_, 3);
v_cache_1263_ = lean_ctor_get(v___x_1257_, 5);
v_messages_1264_ = lean_ctor_get(v___x_1257_, 6);
v_infoState_1265_ = lean_ctor_get(v___x_1257_, 7);
v_snapshotTasks_1266_ = lean_ctor_get(v___x_1257_, 8);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1268_ = v___x_1257_;
v_isShared_1269_ = v_isSharedCheck_1285_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snapshotTasks_1266_);
lean_inc(v_infoState_1265_);
lean_inc(v_messages_1264_);
lean_inc(v_cache_1263_);
lean_inc(v_traceState_1258_);
lean_inc(v_auxDeclNGen_1262_);
lean_inc(v_ngen_1261_);
lean_inc(v_nextMacroScope_1260_);
lean_inc(v_env_1259_);
lean_dec(v___x_1257_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1285_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
uint64_t v_tid_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1283_; 
v_tid_1270_ = lean_ctor_get_uint64(v_traceState_1258_, sizeof(void*)*1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_traceState_1258_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v_traceState_1258_, 0);
lean_dec(v_unused_1284_);
v___x_1272_ = v_traceState_1258_;
v_isShared_1273_ = v_isSharedCheck_1283_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v_traceState_1258_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1283_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1274_);
lean_ctor_set_uint64(v_reuseFailAlloc_1282_, sizeof(void*)*1, v_tid_1270_);
v___x_1276_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v___x_1276_);
v___x_1278_ = v___x_1268_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_env_1259_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_nextMacroScope_1260_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_ngen_1261_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_auxDeclNGen_1262_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1281_, 5, v_cache_1263_);
lean_ctor_set(v_reuseFailAlloc_1281_, 6, v_messages_1264_);
lean_ctor_set(v_reuseFailAlloc_1281_, 7, v_infoState_1265_);
lean_ctor_set(v_reuseFailAlloc_1281_, 8, v_snapshotTasks_1266_);
v___x_1278_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_st_ref_set(v___y_1252_, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_traces_1256_);
return v___x_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___boxed(lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_1286_);
lean_dec(v___y_1286_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___boxed(lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
return v_res_1314_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(lean_object* v_opts_1315_, lean_object* v_opt_1316_){
_start:
{
lean_object* v_name_1317_; lean_object* v_defValue_1318_; lean_object* v_map_1319_; lean_object* v___x_1320_; 
v_name_1317_ = lean_ctor_get(v_opt_1316_, 0);
v_defValue_1318_ = lean_ctor_get(v_opt_1316_, 1);
v_map_1319_ = lean_ctor_get(v_opts_1315_, 0);
v___x_1320_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1319_, v_name_1317_);
if (lean_obj_tag(v___x_1320_) == 0)
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_unbox(v_defValue_1318_);
return v___x_1321_;
}
else
{
lean_object* v_val_1322_; 
v_val_1322_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v___x_1320_, 1);
if (lean_obj_tag(v_val_1322_) == 1)
{
uint8_t v_v_1323_; 
v_v_1323_ = lean_ctor_get_uint8(v_val_1322_, 0);
lean_dec_ref_known(v_val_1322_, 0);
return v_v_1323_;
}
else
{
uint8_t v___x_1324_; 
lean_dec(v_val_1322_);
v___x_1324_ = lean_unbox(v_defValue_1318_);
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3___boxed(lean_object* v_opts_1325_, lean_object* v_opt_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_1325_, v_opt_1326_);
lean_dec_ref(v_opt_1326_);
lean_dec_ref(v_opts_1325_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg___lam__0(lean_object* v_x_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
v___x_1342_ = lean_apply_12(v_x_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, lean_box(0));
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg___lam__0___boxed(lean_object* v_x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg___lam__0(v_x_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg(lean_object* v_mvarId_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___f_1371_; lean_object* v___x_1372_; 
lean_inc(v___y_1365_);
lean_inc_ref(v___y_1364_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc_ref(v___y_1359_);
v___f_1371_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1371_, 0, v_x_1358_);
lean_closure_set(v___f_1371_, 1, v___y_1359_);
lean_closure_set(v___f_1371_, 2, v___y_1360_);
lean_closure_set(v___f_1371_, 3, v___y_1361_);
lean_closure_set(v___f_1371_, 4, v___y_1362_);
lean_closure_set(v___f_1371_, 5, v___y_1363_);
lean_closure_set(v___f_1371_, 6, v___y_1364_);
lean_closure_set(v___f_1371_, 7, v___y_1365_);
v___x_1372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1357_, v___f_1371_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1372_) == 0)
{
return v___x_1372_;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg___boxed(lean_object* v_mvarId_1381_, lean_object* v_x_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg(v_mvarId_1381_, v_x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6(lean_object* v_00_u03b1_1396_, lean_object* v_mvarId_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg(v_mvarId_1397_, v_x_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___boxed(lean_object* v_00_u03b1_1412_, lean_object* v_mvarId_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6(v_00_u03b1_1412_, v_mvarId_1413_, v_x_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg___lam__0(lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
lean_inc(v___y_1433_);
lean_inc_ref(v___y_1432_);
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
v___x_1439_ = lean_apply_10(v_x_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, lean_box(0));
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg___lam__0___boxed(lean_object* v_x_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg___lam__0(v_x_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg(lean_object* v_mvarId_1452_, lean_object* v_x_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___f_1464_; lean_object* v___x_1465_; 
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc(v___y_1454_);
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1464_, 0, v_x_1453_);
lean_closure_set(v___f_1464_, 1, v___y_1454_);
lean_closure_set(v___f_1464_, 2, v___y_1455_);
lean_closure_set(v___f_1464_, 3, v___y_1456_);
lean_closure_set(v___f_1464_, 4, v___y_1457_);
lean_closure_set(v___f_1464_, 5, v___y_1458_);
v___x_1465_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1452_, v___f_1464_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1465_) == 0)
{
return v___x_1465_;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg___boxed(lean_object* v_mvarId_1474_, lean_object* v_x_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg(v_mvarId_1474_, v_x_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7(lean_object* v_00_u03b1_1487_, lean_object* v_mvarId_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg(v_mvarId_1488_, v_x_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_mvarId_1502_, lean_object* v_x_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7(v_00_u03b1_1501_, v_mvarId_1502_, v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
return v_res_1514_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(lean_object* v_x_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___boxed(lean_object* v_x_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(v_x_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec_ref(v_x_1533_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___redArg(size_t v_sz_1547_, size_t v_i_1548_, lean_object* v_bs_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_usize_dec_lt(v_i_1548_, v_sz_1547_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_bs_1549_);
return v___x_1558_;
}
else
{
lean_object* v_v_1559_; lean_object* v___x_1560_; 
v_v_1559_ = lean_array_uget(v_bs_1549_, v_i_1548_);
lean_inc(v_v_1559_);
v___x_1560_ = l_Lean_FVarId_getUserName___redArg(v_v_1559_, v___y_1552_, v___y_1554_, v___y_1555_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
lean_inc(v_v_1559_);
v___x_1562_ = l_Lean_FVarId_getType___redArg(v_v_1559_, v___y_1552_, v___y_1554_, v___y_1555_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_1563_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; lean_object* v_bs_x27_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; size_t v___x_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = lean_unsigned_to_nat(0u);
v_bs_x27_1567_ = lean_array_uset(v_bs_1549_, v_i_1548_, v___x_1566_);
lean_inc(v_v_1559_);
v___x_1568_ = l_Lean_mkFVar(v_v_1559_);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_v_1559_);
v___x_1570_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1570_, 0, v_a_1561_);
lean_ctor_set(v___x_1570_, 1, v_a_1565_);
lean_ctor_set(v___x_1570_, 2, v___x_1568_);
lean_ctor_set(v___x_1570_, 3, v___x_1569_);
v___x_1571_ = ((size_t)1ULL);
v___x_1572_ = lean_usize_add(v_i_1548_, v___x_1571_);
v___x_1573_ = lean_array_uset(v_bs_x27_1567_, v_i_1548_, v___x_1570_);
v_i_1548_ = v___x_1572_;
v_bs_1549_ = v___x_1573_;
goto _start;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_a_1561_);
lean_dec(v_v_1559_);
lean_dec_ref(v_bs_1549_);
v_a_1575_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1564_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1564_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_a_1561_);
lean_dec(v_v_1559_);
lean_dec_ref(v_bs_1549_);
v_a_1583_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1562_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1562_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_v_1559_);
lean_dec_ref(v_bs_1549_);
v_a_1591_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1560_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1560_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___redArg___boxed(lean_object* v_sz_1599_, lean_object* v_i_1600_, lean_object* v_bs_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_sz_boxed_1609_; size_t v_i_boxed_1610_; lean_object* v_res_1611_; 
v_sz_boxed_1609_ = lean_unbox_usize(v_sz_1599_);
lean_dec(v_sz_1599_);
v_i_boxed_1610_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___redArg(v_sz_boxed_1609_, v_i_boxed_1610_, v_bs_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__1(lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Meta_getPropHyps(v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; size_t v_sz_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_sz_1626_ = lean_array_size(v_a_1625_);
v___x_1627_ = ((size_t)0ULL);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___redArg(v_sz_1626_, v___x_1627_, v_a_1625_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1628_;
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_a_1629_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1624_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1624_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__1___boxed(lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__1(v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__2(lean_object* v_goal_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_st_mk_ref(v_goal_1650_);
v___x_1662_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(v___x_1661_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1672_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1672_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1672_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1667_ = lean_st_ref_get(v___x_1661_);
lean_dec(v___x_1661_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v_a_1663_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1668_);
v___x_1670_ = v___x_1665_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v___x_1661_);
v_a_1673_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1662_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1662_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__2___boxed(lean_object* v_goal_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__2(v_goal_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0_spec__0(lean_object* v_msgData_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; lean_object* v_env_1700_; lean_object* v___x_1701_; lean_object* v_mctx_1702_; lean_object* v_lctx_1703_; lean_object* v_options_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1699_ = lean_st_ref_get(v___y_1697_);
v_env_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc_ref(v_env_1700_);
lean_dec(v___x_1699_);
v___x_1701_ = lean_st_ref_get(v___y_1695_);
v_mctx_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc_ref(v_mctx_1702_);
lean_dec(v___x_1701_);
v_lctx_1703_ = lean_ctor_get(v___y_1694_, 2);
v_options_1704_ = lean_ctor_get(v___y_1696_, 2);
lean_inc_ref(v_options_1704_);
lean_inc_ref(v_lctx_1703_);
v___x_1705_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1705_, 0, v_env_1700_);
lean_ctor_set(v___x_1705_, 1, v_mctx_1702_);
lean_ctor_set(v___x_1705_, 2, v_lctx_1703_);
lean_ctor_set(v___x_1705_, 3, v_options_1704_);
v___x_1706_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v_msgData_1693_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0_spec__0___boxed(lean_object* v_msgData_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0_spec__0(v_msgData_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1714_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1715_; double v___x_1716_; 
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = lean_float_of_nat(v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(lean_object* v_cls_1720_, lean_object* v_msg_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_ref_1727_; lean_object* v___x_1728_; lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1773_; 
v_ref_1727_ = lean_ctor_get(v___y_1724_, 5);
v___x_1728_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0_spec__0(v_msg_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1773_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1773_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v_traceState_1734_; lean_object* v_env_1735_; lean_object* v_nextMacroScope_1736_; lean_object* v_ngen_1737_; lean_object* v_auxDeclNGen_1738_; lean_object* v_cache_1739_; lean_object* v_messages_1740_; lean_object* v_infoState_1741_; lean_object* v_snapshotTasks_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1772_; 
v___x_1733_ = lean_st_ref_take(v___y_1725_);
v_traceState_1734_ = lean_ctor_get(v___x_1733_, 4);
v_env_1735_ = lean_ctor_get(v___x_1733_, 0);
v_nextMacroScope_1736_ = lean_ctor_get(v___x_1733_, 1);
v_ngen_1737_ = lean_ctor_get(v___x_1733_, 2);
v_auxDeclNGen_1738_ = lean_ctor_get(v___x_1733_, 3);
v_cache_1739_ = lean_ctor_get(v___x_1733_, 5);
v_messages_1740_ = lean_ctor_get(v___x_1733_, 6);
v_infoState_1741_ = lean_ctor_get(v___x_1733_, 7);
v_snapshotTasks_1742_ = lean_ctor_get(v___x_1733_, 8);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1744_ = v___x_1733_;
v_isShared_1745_ = v_isSharedCheck_1772_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snapshotTasks_1742_);
lean_inc(v_infoState_1741_);
lean_inc(v_messages_1740_);
lean_inc(v_cache_1739_);
lean_inc(v_traceState_1734_);
lean_inc(v_auxDeclNGen_1738_);
lean_inc(v_ngen_1737_);
lean_inc(v_nextMacroScope_1736_);
lean_inc(v_env_1735_);
lean_dec(v___x_1733_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1772_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
uint64_t v_tid_1746_; lean_object* v_traces_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1771_; 
v_tid_1746_ = lean_ctor_get_uint64(v_traceState_1734_, sizeof(void*)*1);
v_traces_1747_ = lean_ctor_get(v_traceState_1734_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_traceState_1734_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1749_ = v_traceState_1734_;
v_isShared_1750_ = v_isSharedCheck_1771_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_traces_1747_);
lean_dec(v_traceState_1734_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1771_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; double v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0);
v___x_1753_ = 0;
v___x_1754_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1));
v___x_1755_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1755_, 0, v_cls_1720_);
lean_ctor_set(v___x_1755_, 1, v___x_1751_);
lean_ctor_set(v___x_1755_, 2, v___x_1754_);
lean_ctor_set_float(v___x_1755_, sizeof(void*)*3, v___x_1752_);
lean_ctor_set_float(v___x_1755_, sizeof(void*)*3 + 8, v___x_1752_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 16, v___x_1753_);
v___x_1756_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__2));
v___x_1757_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v_a_1729_);
lean_ctor_set(v___x_1757_, 2, v___x_1756_);
lean_inc(v_ref_1727_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_ref_1727_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = l_Lean_PersistentArray_push___redArg(v_traces_1747_, v___x_1758_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1759_);
v___x_1761_ = v___x_1749_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1759_);
lean_ctor_set_uint64(v_reuseFailAlloc_1770_, sizeof(void*)*1, v_tid_1746_);
v___x_1761_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 4, v___x_1761_);
v___x_1763_ = v___x_1744_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_env_1735_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_nextMacroScope_1736_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_ngen_1737_);
lean_ctor_set(v_reuseFailAlloc_1769_, 3, v_auxDeclNGen_1738_);
lean_ctor_set(v_reuseFailAlloc_1769_, 4, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1769_, 5, v_cache_1739_);
lean_ctor_set(v_reuseFailAlloc_1769_, 6, v_messages_1740_);
lean_ctor_set(v_reuseFailAlloc_1769_, 7, v_infoState_1741_);
lean_ctor_set(v_reuseFailAlloc_1769_, 8, v_snapshotTasks_1742_);
v___x_1763_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1764_ = lean_st_ref_set(v___y_1725_, v___x_1763_);
v___x_1765_ = lean_box(0);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1765_);
v___x_1767_ = v___x_1731_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___boxed(lean_object* v_cls_1774_, lean_object* v_msg_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v_cls_1774_, v_msg_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1781_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3));
v___x_1793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__5));
v___x_1794_ = l_Lean_Name_append(v___x_1793_, v___x_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2(lean_object* v_as_1795_, size_t v_i_1796_, size_t v_stop_1797_, lean_object* v_b_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_a_1812_; uint8_t v___x_1818_; 
v___x_1818_ = lean_usize_dec_eq(v_i_1796_, v_stop_1797_);
if (v___x_1818_ == 0)
{
lean_object* v_options_1819_; uint8_t v_hasTrace_1820_; 
v_options_1819_ = lean_ctor_get(v___y_1808_, 2);
v_hasTrace_1820_ = lean_ctor_get_uint8(v_options_1819_, sizeof(void*)*1);
if (v_hasTrace_1820_ == 0)
{
goto v___jp_1816_;
}
else
{
lean_object* v_inheritedTraceOptions_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_inheritedTraceOptions_1821_ = lean_ctor_get(v___y_1808_, 13);
v___x_1822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3));
v___x_1823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6);
v___x_1824_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1821_, v_options_1819_, v___x_1823_);
if (v___x_1824_ == 0)
{
goto v___jp_1816_;
}
else
{
lean_object* v___x_1825_; lean_object* v_type_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1825_ = lean_array_uget_borrowed(v_as_1795_, v_i_1796_);
v_type_1826_ = lean_ctor_get(v___x_1825_, 1);
lean_inc_ref(v_type_1826_);
v___x_1827_ = l_Lean_MessageData_ofExpr(v_type_1826_);
v___x_1828_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v___x_1822_, v___x_1827_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v_a_1812_ = v_a_1829_;
goto v___jp_1811_;
}
else
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_b_1798_);
return v___x_1830_;
}
v___jp_1811_:
{
size_t v___x_1813_; size_t v___x_1814_; 
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = lean_usize_add(v_i_1796_, v___x_1813_);
v_i_1796_ = v___x_1814_;
v_b_1798_ = v_a_1812_;
goto _start;
}
v___jp_1816_:
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_box(0);
v_a_1812_ = v___x_1817_;
goto v___jp_1811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___boxed(lean_object* v_as_1831_, lean_object* v_i_1832_, lean_object* v_stop_1833_, lean_object* v_b_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
size_t v_i_boxed_1847_; size_t v_stop_boxed_1848_; lean_object* v_res_1849_; 
v_i_boxed_1847_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_stop_boxed_1848_ = lean_unbox_usize(v_stop_1833_);
lean_dec(v_stop_1833_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2(v_as_1831_, v_i_boxed_1847_, v_stop_boxed_1848_, v_b_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v_as_1831_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(lean_object* v_as_1850_, size_t v_i_1851_, size_t v_stop_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_a_1867_; uint8_t v___x_1873_; 
v___x_1873_ = lean_usize_dec_eq(v_i_1851_, v_stop_1852_);
if (v___x_1873_ == 0)
{
lean_object* v_options_1874_; uint8_t v_hasTrace_1875_; 
v_options_1874_ = lean_ctor_get(v___y_1863_, 2);
v_hasTrace_1875_ = lean_ctor_get_uint8(v_options_1874_, sizeof(void*)*1);
if (v_hasTrace_1875_ == 0)
{
goto v___jp_1871_;
}
else
{
lean_object* v_inheritedTraceOptions_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_inheritedTraceOptions_1876_ = lean_ctor_get(v___y_1863_, 13);
v___x_1877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3));
v___x_1878_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6);
v___x_1879_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1876_, v_options_1874_, v___x_1878_);
if (v___x_1879_ == 0)
{
goto v___jp_1871_;
}
else
{
lean_object* v___x_1880_; lean_object* v_type_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1880_ = lean_array_uget_borrowed(v_as_1850_, v_i_1851_);
v_type_1881_ = lean_ctor_get(v___x_1880_, 1);
lean_inc_ref(v_type_1881_);
v___x_1882_ = l_Lean_MessageData_ofExpr(v_type_1881_);
v___x_1883_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v___x_1877_, v___x_1882_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_a_1867_ = v_a_1884_;
goto v___jp_1866_;
}
else
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v_b_1853_);
return v___x_1885_;
}
v___jp_1866_:
{
size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = ((size_t)1ULL);
v___x_1869_ = lean_usize_add(v_i_1851_, v___x_1868_);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2(v_as_1850_, v___x_1869_, v_stop_1852_, v_a_1867_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1870_;
}
v___jp_1871_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_box(0);
v_a_1867_ = v___x_1872_;
goto v___jp_1866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1___boxed(lean_object* v_as_1886_, lean_object* v_i_1887_, lean_object* v_stop_1888_, lean_object* v_b_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
size_t v_i_boxed_1902_; size_t v_stop_boxed_1903_; lean_object* v_res_1904_; 
v_i_boxed_1902_ = lean_unbox_usize(v_i_1887_);
lean_dec(v_i_1887_);
v_stop_boxed_1903_ = lean_unbox_usize(v_stop_1888_);
lean_dec(v_stop_1888_);
v_res_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_as_1886_, v_i_boxed_1902_, v_stop_boxed_1903_, v_b_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec_ref(v_as_1886_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6_spec__9(size_t v_sz_1905_, size_t v_i_1906_, lean_object* v_bs_1907_){
_start:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_usize_dec_lt(v_i_1906_, v_sz_1905_);
if (v___x_1908_ == 0)
{
return v_bs_1907_;
}
else
{
lean_object* v_v_1909_; lean_object* v_msg_1910_; lean_object* v___x_1911_; lean_object* v_bs_x27_1912_; size_t v___x_1913_; size_t v___x_1914_; lean_object* v___x_1915_; 
v_v_1909_ = lean_array_uget_borrowed(v_bs_1907_, v_i_1906_);
v_msg_1910_ = lean_ctor_get(v_v_1909_, 1);
lean_inc_ref(v_msg_1910_);
v___x_1911_ = lean_unsigned_to_nat(0u);
v_bs_x27_1912_ = lean_array_uset(v_bs_1907_, v_i_1906_, v___x_1911_);
v___x_1913_ = ((size_t)1ULL);
v___x_1914_ = lean_usize_add(v_i_1906_, v___x_1913_);
v___x_1915_ = lean_array_uset(v_bs_x27_1912_, v_i_1906_, v_msg_1910_);
v_i_1906_ = v___x_1914_;
v_bs_1907_ = v___x_1915_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6_spec__9___boxed(lean_object* v_sz_1917_, lean_object* v_i_1918_, lean_object* v_bs_1919_){
_start:
{
size_t v_sz_boxed_1920_; size_t v_i_boxed_1921_; lean_object* v_res_1922_; 
v_sz_boxed_1920_ = lean_unbox_usize(v_sz_1917_);
lean_dec(v_sz_1917_);
v_i_boxed_1921_ = lean_unbox_usize(v_i_1918_);
lean_dec(v_i_1918_);
v_res_1922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6_spec__9(v_sz_boxed_1920_, v_i_boxed_1921_, v_bs_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(lean_object* v_oldTraces_1923_, lean_object* v_data_1924_, lean_object* v_ref_1925_, lean_object* v_msg_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_fileName_1932_; lean_object* v_fileMap_1933_; lean_object* v_options_1934_; lean_object* v_currRecDepth_1935_; lean_object* v_maxRecDepth_1936_; lean_object* v_ref_1937_; lean_object* v_currNamespace_1938_; lean_object* v_openDecls_1939_; lean_object* v_initHeartbeats_1940_; lean_object* v_maxHeartbeats_1941_; lean_object* v_quotContext_1942_; lean_object* v_currMacroScope_1943_; uint8_t v_diag_1944_; lean_object* v_cancelTk_x3f_1945_; uint8_t v_suppressElabErrors_1946_; lean_object* v_inheritedTraceOptions_1947_; lean_object* v___x_1948_; lean_object* v_traceState_1949_; lean_object* v_traces_1950_; lean_object* v_ref_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; size_t v_sz_1954_; size_t v___x_1955_; lean_object* v___x_1956_; lean_object* v_msg_1957_; lean_object* v___x_1958_; lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1996_; 
v_fileName_1932_ = lean_ctor_get(v___y_1929_, 0);
v_fileMap_1933_ = lean_ctor_get(v___y_1929_, 1);
v_options_1934_ = lean_ctor_get(v___y_1929_, 2);
v_currRecDepth_1935_ = lean_ctor_get(v___y_1929_, 3);
v_maxRecDepth_1936_ = lean_ctor_get(v___y_1929_, 4);
v_ref_1937_ = lean_ctor_get(v___y_1929_, 5);
v_currNamespace_1938_ = lean_ctor_get(v___y_1929_, 6);
v_openDecls_1939_ = lean_ctor_get(v___y_1929_, 7);
v_initHeartbeats_1940_ = lean_ctor_get(v___y_1929_, 8);
v_maxHeartbeats_1941_ = lean_ctor_get(v___y_1929_, 9);
v_quotContext_1942_ = lean_ctor_get(v___y_1929_, 10);
v_currMacroScope_1943_ = lean_ctor_get(v___y_1929_, 11);
v_diag_1944_ = lean_ctor_get_uint8(v___y_1929_, sizeof(void*)*14);
v_cancelTk_x3f_1945_ = lean_ctor_get(v___y_1929_, 12);
v_suppressElabErrors_1946_ = lean_ctor_get_uint8(v___y_1929_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1947_ = lean_ctor_get(v___y_1929_, 13);
v___x_1948_ = lean_st_ref_get(v___y_1930_);
v_traceState_1949_ = lean_ctor_get(v___x_1948_, 4);
lean_inc_ref(v_traceState_1949_);
lean_dec(v___x_1948_);
v_traces_1950_ = lean_ctor_get(v_traceState_1949_, 0);
lean_inc_ref(v_traces_1950_);
lean_dec_ref(v_traceState_1949_);
v_ref_1951_ = l_Lean_replaceRef(v_ref_1925_, v_ref_1937_);
lean_inc_ref(v_inheritedTraceOptions_1947_);
lean_inc(v_cancelTk_x3f_1945_);
lean_inc(v_currMacroScope_1943_);
lean_inc(v_quotContext_1942_);
lean_inc(v_maxHeartbeats_1941_);
lean_inc(v_initHeartbeats_1940_);
lean_inc(v_openDecls_1939_);
lean_inc(v_currNamespace_1938_);
lean_inc(v_maxRecDepth_1936_);
lean_inc(v_currRecDepth_1935_);
lean_inc_ref(v_options_1934_);
lean_inc_ref(v_fileMap_1933_);
lean_inc_ref(v_fileName_1932_);
v___x_1952_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1952_, 0, v_fileName_1932_);
lean_ctor_set(v___x_1952_, 1, v_fileMap_1933_);
lean_ctor_set(v___x_1952_, 2, v_options_1934_);
lean_ctor_set(v___x_1952_, 3, v_currRecDepth_1935_);
lean_ctor_set(v___x_1952_, 4, v_maxRecDepth_1936_);
lean_ctor_set(v___x_1952_, 5, v_ref_1951_);
lean_ctor_set(v___x_1952_, 6, v_currNamespace_1938_);
lean_ctor_set(v___x_1952_, 7, v_openDecls_1939_);
lean_ctor_set(v___x_1952_, 8, v_initHeartbeats_1940_);
lean_ctor_set(v___x_1952_, 9, v_maxHeartbeats_1941_);
lean_ctor_set(v___x_1952_, 10, v_quotContext_1942_);
lean_ctor_set(v___x_1952_, 11, v_currMacroScope_1943_);
lean_ctor_set(v___x_1952_, 12, v_cancelTk_x3f_1945_);
lean_ctor_set(v___x_1952_, 13, v_inheritedTraceOptions_1947_);
lean_ctor_set_uint8(v___x_1952_, sizeof(void*)*14, v_diag_1944_);
lean_ctor_set_uint8(v___x_1952_, sizeof(void*)*14 + 1, v_suppressElabErrors_1946_);
v___x_1953_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1950_);
lean_dec_ref(v_traces_1950_);
v_sz_1954_ = lean_array_size(v___x_1953_);
v___x_1955_ = ((size_t)0ULL);
v___x_1956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6_spec__9(v_sz_1954_, v___x_1955_, v___x_1953_);
v_msg_1957_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1957_, 0, v_data_1924_);
lean_ctor_set(v_msg_1957_, 1, v_msg_1926_);
lean_ctor_set(v_msg_1957_, 2, v___x_1956_);
v___x_1958_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0_spec__0(v_msg_1957_, v___y_1927_, v___y_1928_, v___x_1952_, v___y_1930_);
lean_dec_ref_known(v___x_1952_, 14);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1996_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1996_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v_traceState_1964_; lean_object* v_env_1965_; lean_object* v_nextMacroScope_1966_; lean_object* v_ngen_1967_; lean_object* v_auxDeclNGen_1968_; lean_object* v_cache_1969_; lean_object* v_messages_1970_; lean_object* v_infoState_1971_; lean_object* v_snapshotTasks_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1995_; 
v___x_1963_ = lean_st_ref_take(v___y_1930_);
v_traceState_1964_ = lean_ctor_get(v___x_1963_, 4);
v_env_1965_ = lean_ctor_get(v___x_1963_, 0);
v_nextMacroScope_1966_ = lean_ctor_get(v___x_1963_, 1);
v_ngen_1967_ = lean_ctor_get(v___x_1963_, 2);
v_auxDeclNGen_1968_ = lean_ctor_get(v___x_1963_, 3);
v_cache_1969_ = lean_ctor_get(v___x_1963_, 5);
v_messages_1970_ = lean_ctor_get(v___x_1963_, 6);
v_infoState_1971_ = lean_ctor_get(v___x_1963_, 7);
v_snapshotTasks_1972_ = lean_ctor_get(v___x_1963_, 8);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1974_ = v___x_1963_;
v_isShared_1975_ = v_isSharedCheck_1995_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_snapshotTasks_1972_);
lean_inc(v_infoState_1971_);
lean_inc(v_messages_1970_);
lean_inc(v_cache_1969_);
lean_inc(v_traceState_1964_);
lean_inc(v_auxDeclNGen_1968_);
lean_inc(v_ngen_1967_);
lean_inc(v_nextMacroScope_1966_);
lean_inc(v_env_1965_);
lean_dec(v___x_1963_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1995_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
uint64_t v_tid_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1993_; 
v_tid_1976_ = lean_ctor_get_uint64(v_traceState_1964_, sizeof(void*)*1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_traceState_1964_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; 
v_unused_1994_ = lean_ctor_get(v_traceState_1964_, 0);
lean_dec(v_unused_1994_);
v___x_1978_ = v_traceState_1964_;
v_isShared_1979_ = v_isSharedCheck_1993_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v_traceState_1964_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1993_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_ref_1925_);
lean_ctor_set(v___x_1980_, 1, v_a_1959_);
v___x_1981_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1923_, v___x_1980_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1981_);
v___x_1983_ = v___x_1978_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1981_);
lean_ctor_set_uint64(v_reuseFailAlloc_1992_, sizeof(void*)*1, v_tid_1976_);
v___x_1983_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 4, v___x_1983_);
v___x_1985_ = v___x_1974_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_env_1965_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_nextMacroScope_1966_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_ngen_1967_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_auxDeclNGen_1968_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1991_, 5, v_cache_1969_);
lean_ctor_set(v_reuseFailAlloc_1991_, 6, v_messages_1970_);
lean_ctor_set(v_reuseFailAlloc_1991_, 7, v_infoState_1971_);
lean_ctor_set(v_reuseFailAlloc_1991_, 8, v_snapshotTasks_1972_);
v___x_1985_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1986_ = lean_st_ref_set(v___y_1930_, v___x_1985_);
v___x_1987_ = lean_box(0);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1987_);
v___x_1989_ = v___x_1961_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg___boxed(lean_object* v_oldTraces_1997_, lean_object* v_data_1998_, lean_object* v_ref_1999_, lean_object* v_msg_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_oldTraces_1997_, v_data_1998_, v_ref_1999_, v_msg_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(lean_object* v_e_2007_){
_start:
{
if (lean_obj_tag(v_e_2007_) == 0)
{
uint8_t v___x_2008_; 
v___x_2008_ = 2;
return v___x_2008_;
}
else
{
uint8_t v___x_2009_; 
v___x_2009_ = 0;
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8___boxed(lean_object* v_e_2010_){
_start:
{
uint8_t v_res_2011_; lean_object* v_r_2012_; 
v_res_2011_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_e_2010_);
lean_dec_ref(v_e_2010_);
v_r_2012_ = lean_box(v_res_2011_);
return v_r_2012_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___redArg(lean_object* v_x_2013_){
_start:
{
if (lean_obj_tag(v_x_2013_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
v_a_2015_ = lean_ctor_get(v_x_2013_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_2013_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v_x_2013_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v_x_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 1);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_a_2023_ = lean_ctor_get(v_x_2013_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_x_2013_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v_x_2013_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v_x_2013_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set_tag(v___x_2025_, 0);
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___redArg___boxed(lean_object* v_x_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___redArg(v_x_2031_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__9(lean_object* v_opts_2034_, lean_object* v_opt_2035_){
_start:
{
lean_object* v_name_2036_; lean_object* v_defValue_2037_; lean_object* v_map_2038_; lean_object* v___x_2039_; 
v_name_2036_ = lean_ctor_get(v_opt_2035_, 0);
v_defValue_2037_ = lean_ctor_get(v_opt_2035_, 1);
v_map_2038_ = lean_ctor_get(v_opts_2034_, 0);
v___x_2039_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2038_, v_name_2036_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_inc(v_defValue_2037_);
return v_defValue_2037_;
}
else
{
lean_object* v_val_2040_; 
v_val_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v___x_2039_, 1);
if (lean_obj_tag(v_val_2040_) == 3)
{
lean_object* v_v_2041_; 
v_v_2041_ = lean_ctor_get(v_val_2040_, 0);
lean_inc(v_v_2041_);
lean_dec_ref_known(v_val_2040_, 1);
return v_v_2041_;
}
else
{
lean_dec(v_val_2040_);
lean_inc(v_defValue_2037_);
return v_defValue_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__9___boxed(lean_object* v_opts_2042_, lean_object* v_opt_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__9(v_opts_2042_, v_opt_2043_);
lean_dec_ref(v_opt_2043_);
lean_dec_ref(v_opts_2042_);
return v_res_2044_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2048_; double v___x_2049_; 
v___x_2048_ = lean_unsigned_to_nat(1000u);
v___x_2049_ = lean_float_of_nat(v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(lean_object* v_cls_2050_, uint8_t v_collapsed_2051_, lean_object* v_tag_2052_, lean_object* v_opts_2053_, uint8_t v_clsEnabled_2054_, lean_object* v_oldTraces_2055_, lean_object* v_msg_2056_, lean_object* v_resStartStop_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v_data_2075_; lean_object* v_fst_2078_; lean_object* v_snd_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; lean_object* v___y_2083_; lean_object* v_a_2084_; uint8_t v___y_2099_; double v___y_2130_; 
v_fst_2070_ = lean_ctor_get(v_resStartStop_2057_, 0);
lean_inc(v_fst_2070_);
v_snd_2071_ = lean_ctor_get(v_resStartStop_2057_, 1);
lean_inc(v_snd_2071_);
lean_dec_ref(v_resStartStop_2057_);
v_fst_2078_ = lean_ctor_get(v_snd_2071_, 0);
lean_inc(v_fst_2078_);
v_snd_2079_ = lean_ctor_get(v_snd_2071_, 1);
lean_inc(v_snd_2079_);
lean_dec(v_snd_2071_);
v___x_2080_ = l_Lean_trace_profiler;
v___x_2081_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_2053_, v___x_2080_);
if (v___x_2081_ == 0)
{
v___y_2099_ = v___x_2081_;
goto v___jp_2098_;
}
else
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2136_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_2053_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; double v___x_2139_; double v___x_2140_; double v___x_2141_; 
v___x_2137_ = l_Lean_trace_profiler_threshold;
v___x_2138_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__9(v_opts_2053_, v___x_2137_);
v___x_2139_ = lean_float_of_nat(v___x_2138_);
v___x_2140_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2);
v___x_2141_ = lean_float_div(v___x_2139_, v___x_2140_);
v___y_2130_ = v___x_2141_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; double v___x_2144_; 
v___x_2142_ = l_Lean_trace_profiler_threshold;
v___x_2143_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__9(v_opts_2053_, v___x_2142_);
v___x_2144_ = lean_float_of_nat(v___x_2143_);
v___y_2130_ = v___x_2144_;
goto v___jp_2129_;
}
}
v___jp_2072_:
{
lean_object* v___x_2076_; 
lean_inc(v___y_2074_);
v___x_2076_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_oldTraces_2055_, v_data_2075_, v___y_2074_, v___y_2073_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2077_; 
lean_dec_ref_known(v___x_2076_, 1);
v___x_2077_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___redArg(v_fst_2070_);
return v___x_2077_;
}
else
{
lean_dec(v_fst_2070_);
return v___x_2076_;
}
}
v___jp_2082_:
{
uint8_t v_result_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; double v___x_2088_; lean_object* v_data_2089_; 
v_result_2085_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_fst_2070_);
v___x_2086_ = lean_box(v_result_2085_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
v___x_2088_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2052_);
lean_inc_ref(v___x_2087_);
lean_inc(v_cls_2050_);
v_data_2089_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2089_, 0, v_cls_2050_);
lean_ctor_set(v_data_2089_, 1, v___x_2087_);
lean_ctor_set(v_data_2089_, 2, v_tag_2052_);
lean_ctor_set_float(v_data_2089_, sizeof(void*)*3, v___x_2088_);
lean_ctor_set_float(v_data_2089_, sizeof(void*)*3 + 8, v___x_2088_);
lean_ctor_set_uint8(v_data_2089_, sizeof(void*)*3 + 16, v_collapsed_2051_);
if (v___x_2081_ == 0)
{
lean_dec_ref_known(v___x_2087_, 1);
lean_dec(v_snd_2079_);
lean_dec(v_fst_2078_);
lean_dec_ref(v_tag_2052_);
lean_dec(v_cls_2050_);
v___y_2073_ = v_a_2084_;
v___y_2074_ = v___y_2083_;
v_data_2075_ = v_data_2089_;
goto v___jp_2072_;
}
else
{
lean_object* v_data_2090_; double v___x_2091_; double v___x_2092_; 
lean_dec_ref_known(v_data_2089_, 3);
v_data_2090_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2090_, 0, v_cls_2050_);
lean_ctor_set(v_data_2090_, 1, v___x_2087_);
lean_ctor_set(v_data_2090_, 2, v_tag_2052_);
v___x_2091_ = lean_unbox_float(v_fst_2078_);
lean_dec(v_fst_2078_);
lean_ctor_set_float(v_data_2090_, sizeof(void*)*3, v___x_2091_);
v___x_2092_ = lean_unbox_float(v_snd_2079_);
lean_dec(v_snd_2079_);
lean_ctor_set_float(v_data_2090_, sizeof(void*)*3 + 8, v___x_2092_);
lean_ctor_set_uint8(v_data_2090_, sizeof(void*)*3 + 16, v_collapsed_2051_);
v___y_2073_ = v_a_2084_;
v___y_2074_ = v___y_2083_;
v_data_2075_ = v_data_2090_;
goto v___jp_2072_;
}
}
v___jp_2093_:
{
lean_object* v_ref_2094_; lean_object* v___x_2095_; 
v_ref_2094_ = lean_ctor_get(v___y_2067_, 5);
lean_inc(v___y_2068_);
lean_inc_ref(v___y_2067_);
lean_inc(v___y_2066_);
lean_inc_ref(v___y_2065_);
lean_inc(v___y_2064_);
lean_inc_ref(v___y_2063_);
lean_inc(v___y_2062_);
lean_inc_ref(v___y_2061_);
lean_inc(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v_fst_2070_);
v___x_2095_ = lean_apply_13(v_msg_2056_, v_fst_2070_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, lean_box(0));
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___y_2083_ = v_ref_2094_;
v_a_2084_ = v_a_2096_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2097_; 
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1);
v___y_2083_ = v_ref_2094_;
v_a_2084_ = v___x_2097_;
goto v___jp_2082_;
}
}
v___jp_2098_:
{
if (v_clsEnabled_2054_ == 0)
{
if (v___y_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v_traceState_2101_; lean_object* v_env_2102_; lean_object* v_nextMacroScope_2103_; lean_object* v_ngen_2104_; lean_object* v_auxDeclNGen_2105_; lean_object* v_cache_2106_; lean_object* v_messages_2107_; lean_object* v_infoState_2108_; lean_object* v_snapshotTasks_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_snd_2079_);
lean_dec(v_fst_2078_);
lean_dec_ref(v_msg_2056_);
lean_dec_ref(v_tag_2052_);
lean_dec(v_cls_2050_);
v___x_2100_ = lean_st_ref_take(v___y_2068_);
v_traceState_2101_ = lean_ctor_get(v___x_2100_, 4);
v_env_2102_ = lean_ctor_get(v___x_2100_, 0);
v_nextMacroScope_2103_ = lean_ctor_get(v___x_2100_, 1);
v_ngen_2104_ = lean_ctor_get(v___x_2100_, 2);
v_auxDeclNGen_2105_ = lean_ctor_get(v___x_2100_, 3);
v_cache_2106_ = lean_ctor_get(v___x_2100_, 5);
v_messages_2107_ = lean_ctor_get(v___x_2100_, 6);
v_infoState_2108_ = lean_ctor_get(v___x_2100_, 7);
v_snapshotTasks_2109_ = lean_ctor_get(v___x_2100_, 8);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2111_ = v___x_2100_;
v_isShared_2112_ = v_isSharedCheck_2128_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_snapshotTasks_2109_);
lean_inc(v_infoState_2108_);
lean_inc(v_messages_2107_);
lean_inc(v_cache_2106_);
lean_inc(v_traceState_2101_);
lean_inc(v_auxDeclNGen_2105_);
lean_inc(v_ngen_2104_);
lean_inc(v_nextMacroScope_2103_);
lean_inc(v_env_2102_);
lean_dec(v___x_2100_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2128_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
uint64_t v_tid_2113_; lean_object* v_traces_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2127_; 
v_tid_2113_ = lean_ctor_get_uint64(v_traceState_2101_, sizeof(void*)*1);
v_traces_2114_ = lean_ctor_get(v_traceState_2101_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_traceState_2101_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2116_ = v_traceState_2101_;
v_isShared_2117_ = v_isSharedCheck_2127_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_traces_2114_);
lean_dec(v_traceState_2101_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2127_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2055_, v_traces_2114_);
lean_dec_ref(v_traces_2114_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2118_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2118_);
lean_ctor_set_uint64(v_reuseFailAlloc_2126_, sizeof(void*)*1, v_tid_2113_);
v___x_2120_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 4, v___x_2120_);
v___x_2122_ = v___x_2111_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_env_2102_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_nextMacroScope_2103_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_ngen_2104_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_auxDeclNGen_2105_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2125_, 5, v_cache_2106_);
lean_ctor_set(v_reuseFailAlloc_2125_, 6, v_messages_2107_);
lean_ctor_set(v_reuseFailAlloc_2125_, 7, v_infoState_2108_);
lean_ctor_set(v_reuseFailAlloc_2125_, 8, v_snapshotTasks_2109_);
v___x_2122_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_st_ref_set(v___y_2068_, v___x_2122_);
v___x_2124_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___redArg(v_fst_2070_);
return v___x_2124_;
}
}
}
}
}
else
{
goto v___jp_2093_;
}
}
else
{
goto v___jp_2093_;
}
}
v___jp_2129_:
{
double v___x_2131_; double v___x_2132_; double v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = lean_unbox_float(v_snd_2079_);
v___x_2132_ = lean_unbox_float(v_fst_2078_);
v___x_2133_ = lean_float_sub(v___x_2131_, v___x_2132_);
v___x_2134_ = lean_float_decLt(v___y_2130_, v___x_2133_);
v___y_2099_ = v___x_2134_;
goto v___jp_2098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___boxed(lean_object** _args){
lean_object* v_cls_2145_ = _args[0];
lean_object* v_collapsed_2146_ = _args[1];
lean_object* v_tag_2147_ = _args[2];
lean_object* v_opts_2148_ = _args[3];
lean_object* v_clsEnabled_2149_ = _args[4];
lean_object* v_oldTraces_2150_ = _args[5];
lean_object* v_msg_2151_ = _args[6];
lean_object* v_resStartStop_2152_ = _args[7];
lean_object* v___y_2153_ = _args[8];
lean_object* v___y_2154_ = _args[9];
lean_object* v___y_2155_ = _args[10];
lean_object* v___y_2156_ = _args[11];
lean_object* v___y_2157_ = _args[12];
lean_object* v___y_2158_ = _args[13];
lean_object* v___y_2159_ = _args[14];
lean_object* v___y_2160_ = _args[15];
lean_object* v___y_2161_ = _args[16];
lean_object* v___y_2162_ = _args[17];
lean_object* v___y_2163_ = _args[18];
lean_object* v___y_2164_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_2165_; uint8_t v_clsEnabled_boxed_2166_; lean_object* v_res_2167_; 
v_collapsed_boxed_2165_ = lean_unbox(v_collapsed_2146_);
v_clsEnabled_boxed_2166_ = lean_unbox(v_clsEnabled_2149_);
v_res_2167_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v_cls_2145_, v_collapsed_boxed_2165_, v_tag_2147_, v_opts_2148_, v_clsEnabled_boxed_2166_, v_oldTraces_2150_, v_msg_2151_, v_resStartStop_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_opts_2148_);
return v_res_2167_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1(void){
_start:
{
lean_object* v___x_2169_; double v___x_2170_; 
v___x_2169_ = lean_unsigned_to_nat(1000000000u);
v___x_2170_ = lean_float_of_nat(v___x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___x_2209_; lean_object* v_target_2210_; lean_object* v___f_2211_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; uint8_t v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; uint8_t v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v_a_2232_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; uint8_t v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; uint8_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v_a_2264_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; uint8_t v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; uint8_t v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; uint8_t v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; uint8_t v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v_a_2316_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; uint8_t v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; uint8_t v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v_a_2345_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; uint8_t v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; uint8_t v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; uint8_t v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; uint8_t v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v_hypotheses_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; 
v___x_2209_ = lean_st_ref_get(v_a_2173_);
v_target_2210_ = lean_ctor_get(v___x_2209_, 4);
lean_inc_ref(v_target_2210_);
lean_dec(v___x_2209_);
v___f_2211_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0));
if (lean_obj_tag(v_target_2210_) == 0)
{
lean_object* v_mvar_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; 
v_mvar_2463_ = lean_ctor_get(v_target_2210_, 0);
lean_inc(v_mvar_2463_);
lean_dec_ref_known(v_target_2210_, 1);
v___f_2464_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__2));
v___x_2465_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__6___redArg(v_mvar_2463_, v___f_2464_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v_hypotheses_2422_ = v_a_2466_;
v___y_2423_ = v_a_2172_;
v___y_2424_ = v_a_2173_;
v___y_2425_ = v_a_2174_;
v___y_2426_ = v_a_2175_;
v___y_2427_ = v_a_2176_;
v___y_2428_ = v_a_2177_;
v___y_2429_ = v_a_2178_;
v___y_2430_ = v_a_2179_;
v___y_2431_ = v_a_2180_;
v___y_2432_ = v_a_2181_;
v___y_2433_ = v_a_2182_;
goto v___jp_2421_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2465_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2465_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_goal_2475_; lean_object* v_mvarId_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; 
v_goal_2475_ = lean_ctor_get(v_target_2210_, 0);
lean_inc_ref(v_goal_2475_);
lean_dec_ref_known(v_target_2210_, 1);
v_mvarId_2476_ = lean_ctor_get(v_goal_2475_, 1);
lean_inc(v_mvarId_2476_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2477_, 0, v_goal_2475_);
v___x_2478_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__7___redArg(v_mvarId_2476_, v___f_2477_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v_fst_2480_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v___x_2478_, 1);
v_fst_2480_ = lean_ctor_get(v_a_2479_, 0);
lean_inc(v_fst_2480_);
lean_dec(v_a_2479_);
v_hypotheses_2422_ = v_fst_2480_;
v___y_2423_ = v_a_2172_;
v___y_2424_ = v_a_2173_;
v___y_2425_ = v_a_2174_;
v___y_2426_ = v_a_2175_;
v___y_2427_ = v_a_2176_;
v___y_2428_ = v_a_2177_;
v___y_2429_ = v_a_2178_;
v___y_2430_ = v_a_2179_;
v___y_2431_ = v_a_2180_;
v___y_2432_ = v_a_2181_;
v___y_2433_ = v_a_2182_;
goto v___jp_2421_;
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
v_a_2481_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2478_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2478_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
v___jp_2184_:
{
lean_object* v___x_2187_; lean_object* v_rewriteSimpCache_2188_; lean_object* v_rewriteDSimpCache_2189_; lean_object* v_acCache_2190_; lean_object* v_typeAnalysis_2191_; lean_object* v_target_2192_; uint8_t v_didChange_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2203_; 
v___x_2187_ = lean_st_ref_take(v___y_2186_);
v_rewriteSimpCache_2188_ = lean_ctor_get(v___x_2187_, 0);
v_rewriteDSimpCache_2189_ = lean_ctor_get(v___x_2187_, 1);
v_acCache_2190_ = lean_ctor_get(v___x_2187_, 2);
v_typeAnalysis_2191_ = lean_ctor_get(v___x_2187_, 3);
v_target_2192_ = lean_ctor_get(v___x_2187_, 4);
v_didChange_2193_ = lean_ctor_get_uint8(v___x_2187_, sizeof(void*)*6);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; 
v_unused_2204_ = lean_ctor_get(v___x_2187_, 5);
lean_dec(v_unused_2204_);
v___x_2195_ = v___x_2187_;
v_isShared_2196_ = v_isSharedCheck_2203_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_target_2192_);
lean_inc(v_typeAnalysis_2191_);
lean_inc(v_acCache_2190_);
lean_inc(v_rewriteDSimpCache_2189_);
lean_inc(v_rewriteSimpCache_2188_);
lean_dec(v___x_2187_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2203_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 5, v___y_2185_);
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_rewriteSimpCache_2188_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_rewriteDSimpCache_2189_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_acCache_2190_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_typeAnalysis_2191_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_target_2192_);
lean_ctor_set(v_reuseFailAlloc_2202_, 5, v___y_2185_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*6, v_didChange_2193_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = lean_st_ref_set(v___y_2186_, v___x_2198_);
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
}
v___jp_2205_:
{
if (lean_obj_tag(v___y_2208_) == 0)
{
lean_dec_ref_known(v___y_2208_, 1);
v___y_2185_ = v___y_2206_;
v___y_2186_ = v___y_2207_;
goto v___jp_2184_;
}
else
{
lean_dec_ref(v___y_2206_);
return v___y_2208_;
}
}
v___jp_2212_:
{
lean_object* v___x_2233_; double v___x_2234_; double v___x_2235_; double v___x_2236_; double v___x_2237_; double v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2233_ = lean_io_mono_nanos_now();
v___x_2234_ = lean_float_of_nat(v___y_2223_);
v___x_2235_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1);
v___x_2236_ = lean_float_div(v___x_2234_, v___x_2235_);
v___x_2237_ = lean_float_of_nat(v___x_2233_);
v___x_2238_ = lean_float_div(v___x_2237_, v___x_2235_);
v___x_2239_ = lean_box_float(v___x_2236_);
v___x_2240_ = lean_box_float(v___x_2238_);
v___x_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2232_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
lean_inc_ref(v___y_2227_);
lean_inc(v___y_2217_);
v___x_2243_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v___y_2217_, v___y_2221_, v___y_2227_, v___y_2213_, v___y_2218_, v___y_2220_, v___f_2211_, v___x_2242_, v___y_2230_, v___y_2229_, v___y_2214_, v___y_2228_, v___y_2231_, v___y_2219_, v___y_2222_, v___y_2225_, v___y_2224_, v___y_2216_, v___y_2215_);
v___y_2206_ = v___y_2226_;
v___y_2207_ = v___y_2229_;
v___y_2208_ = v___x_2243_;
goto v___jp_2205_;
}
v___jp_2244_:
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_a_2264_);
v___y_2213_ = v___y_2245_;
v___y_2214_ = v___y_2246_;
v___y_2215_ = v___y_2247_;
v___y_2216_ = v___y_2248_;
v___y_2217_ = v___y_2249_;
v___y_2218_ = v___y_2250_;
v___y_2219_ = v___y_2251_;
v___y_2220_ = v___y_2252_;
v___y_2221_ = v___y_2253_;
v___y_2222_ = v___y_2254_;
v___y_2223_ = v___y_2255_;
v___y_2224_ = v___y_2256_;
v___y_2225_ = v___y_2257_;
v___y_2226_ = v___y_2260_;
v___y_2227_ = v___y_2259_;
v___y_2228_ = v___y_2258_;
v___y_2229_ = v___y_2261_;
v___y_2230_ = v___y_2262_;
v___y_2231_ = v___y_2263_;
v_a_2232_ = v___x_2265_;
goto v___jp_2212_;
}
v___jp_2266_:
{
if (lean_obj_tag(v___y_2286_) == 0)
{
lean_object* v_a_2287_; 
v_a_2287_ = lean_ctor_get(v___y_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___y_2286_, 1);
v___y_2245_ = v___y_2267_;
v___y_2246_ = v___y_2268_;
v___y_2247_ = v___y_2269_;
v___y_2248_ = v___y_2270_;
v___y_2249_ = v___y_2271_;
v___y_2250_ = v___y_2272_;
v___y_2251_ = v___y_2273_;
v___y_2252_ = v___y_2274_;
v___y_2253_ = v___y_2275_;
v___y_2254_ = v___y_2276_;
v___y_2255_ = v___y_2277_;
v___y_2256_ = v___y_2278_;
v___y_2257_ = v___y_2279_;
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___y_2281_;
v___y_2260_ = v___y_2280_;
v___y_2261_ = v___y_2283_;
v___y_2262_ = v___y_2284_;
v___y_2263_ = v___y_2285_;
v_a_2264_ = v_a_2287_;
goto v___jp_2244_;
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
v_a_2288_ = lean_ctor_get(v___y_2286_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___y_2286_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___y_2286_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___y_2286_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set_tag(v___x_2290_, 0);
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
v___y_2213_ = v___y_2267_;
v___y_2214_ = v___y_2268_;
v___y_2215_ = v___y_2269_;
v___y_2216_ = v___y_2270_;
v___y_2217_ = v___y_2271_;
v___y_2218_ = v___y_2272_;
v___y_2219_ = v___y_2273_;
v___y_2220_ = v___y_2274_;
v___y_2221_ = v___y_2275_;
v___y_2222_ = v___y_2276_;
v___y_2223_ = v___y_2277_;
v___y_2224_ = v___y_2278_;
v___y_2225_ = v___y_2279_;
v___y_2226_ = v___y_2280_;
v___y_2227_ = v___y_2281_;
v___y_2228_ = v___y_2282_;
v___y_2229_ = v___y_2283_;
v___y_2230_ = v___y_2284_;
v___y_2231_ = v___y_2285_;
v_a_2232_ = v___x_2293_;
goto v___jp_2212_;
}
}
}
}
v___jp_2296_:
{
lean_object* v___x_2317_; double v___x_2318_; double v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2317_ = lean_io_get_num_heartbeats();
v___x_2318_ = lean_float_of_nat(v___y_2297_);
v___x_2319_ = lean_float_of_nat(v___x_2317_);
v___x_2320_ = lean_box_float(v___x_2318_);
v___x_2321_ = lean_box_float(v___x_2319_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2316_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
lean_inc_ref(v___y_2311_);
lean_inc(v___y_2302_);
v___x_2324_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v___y_2302_, v___y_2306_, v___y_2311_, v___y_2298_, v___y_2303_, v___y_2305_, v___f_2211_, v___x_2323_, v___y_2314_, v___y_2313_, v___y_2299_, v___y_2312_, v___y_2315_, v___y_2304_, v___y_2307_, v___y_2309_, v___y_2308_, v___y_2301_, v___y_2300_);
v___y_2206_ = v___y_2310_;
v___y_2207_ = v___y_2313_;
v___y_2208_ = v___x_2324_;
goto v___jp_2205_;
}
v___jp_2325_:
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_a_2345_);
v___y_2297_ = v___y_2326_;
v___y_2298_ = v___y_2327_;
v___y_2299_ = v___y_2328_;
v___y_2300_ = v___y_2329_;
v___y_2301_ = v___y_2330_;
v___y_2302_ = v___y_2331_;
v___y_2303_ = v___y_2332_;
v___y_2304_ = v___y_2333_;
v___y_2305_ = v___y_2334_;
v___y_2306_ = v___y_2335_;
v___y_2307_ = v___y_2336_;
v___y_2308_ = v___y_2337_;
v___y_2309_ = v___y_2338_;
v___y_2310_ = v___y_2341_;
v___y_2311_ = v___y_2340_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v___y_2342_;
v___y_2314_ = v___y_2343_;
v___y_2315_ = v___y_2344_;
v_a_2316_ = v___x_2346_;
goto v___jp_2296_;
}
v___jp_2347_:
{
if (lean_obj_tag(v___y_2367_) == 0)
{
lean_object* v_a_2368_; 
v_a_2368_ = lean_ctor_get(v___y_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___y_2367_, 1);
v___y_2326_ = v___y_2348_;
v___y_2327_ = v___y_2349_;
v___y_2328_ = v___y_2350_;
v___y_2329_ = v___y_2351_;
v___y_2330_ = v___y_2352_;
v___y_2331_ = v___y_2353_;
v___y_2332_ = v___y_2354_;
v___y_2333_ = v___y_2355_;
v___y_2334_ = v___y_2356_;
v___y_2335_ = v___y_2357_;
v___y_2336_ = v___y_2358_;
v___y_2337_ = v___y_2359_;
v___y_2338_ = v___y_2360_;
v___y_2339_ = v___y_2363_;
v___y_2340_ = v___y_2362_;
v___y_2341_ = v___y_2361_;
v___y_2342_ = v___y_2364_;
v___y_2343_ = v___y_2365_;
v___y_2344_ = v___y_2366_;
v_a_2345_ = v_a_2368_;
goto v___jp_2325_;
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v___y_2367_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___y_2367_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___y_2367_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___y_2367_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 0);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
v___y_2297_ = v___y_2348_;
v___y_2298_ = v___y_2349_;
v___y_2299_ = v___y_2350_;
v___y_2300_ = v___y_2351_;
v___y_2301_ = v___y_2352_;
v___y_2302_ = v___y_2353_;
v___y_2303_ = v___y_2354_;
v___y_2304_ = v___y_2355_;
v___y_2305_ = v___y_2356_;
v___y_2306_ = v___y_2357_;
v___y_2307_ = v___y_2358_;
v___y_2308_ = v___y_2359_;
v___y_2309_ = v___y_2360_;
v___y_2310_ = v___y_2361_;
v___y_2311_ = v___y_2362_;
v___y_2312_ = v___y_2363_;
v___y_2313_ = v___y_2364_;
v___y_2314_ = v___y_2365_;
v___y_2315_ = v___y_2366_;
v_a_2316_ = v___x_2374_;
goto v___jp_2296_;
}
}
}
}
v___jp_2377_:
{
lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2397_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_2382_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2400_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v___y_2380_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2401_ = lean_io_mono_nanos_now();
v___x_2402_ = lean_box(0);
v___x_2403_ = lean_nat_dec_lt(v___y_2379_, v___y_2378_);
if (v___x_2403_ == 0)
{
lean_dec(v___y_2378_);
v___y_2245_ = v___y_2380_;
v___y_2246_ = v___y_2381_;
v___y_2247_ = v___y_2382_;
v___y_2248_ = v___y_2383_;
v___y_2249_ = v___y_2385_;
v___y_2250_ = v___y_2384_;
v___y_2251_ = v___y_2386_;
v___y_2252_ = v_a_2398_;
v___y_2253_ = v___y_2387_;
v___y_2254_ = v___y_2388_;
v___y_2255_ = v___x_2401_;
v___y_2256_ = v___y_2389_;
v___y_2257_ = v___y_2390_;
v___y_2258_ = v___y_2393_;
v___y_2259_ = v___y_2391_;
v___y_2260_ = v___y_2392_;
v___y_2261_ = v___y_2394_;
v___y_2262_ = v___y_2395_;
v___y_2263_ = v___y_2396_;
v_a_2264_ = v___x_2402_;
goto v___jp_2244_;
}
else
{
uint8_t v___x_2404_; 
v___x_2404_ = lean_nat_dec_le(v___y_2378_, v___y_2378_);
if (v___x_2404_ == 0)
{
if (v___x_2403_ == 0)
{
lean_dec(v___y_2378_);
v___y_2245_ = v___y_2380_;
v___y_2246_ = v___y_2381_;
v___y_2247_ = v___y_2382_;
v___y_2248_ = v___y_2383_;
v___y_2249_ = v___y_2385_;
v___y_2250_ = v___y_2384_;
v___y_2251_ = v___y_2386_;
v___y_2252_ = v_a_2398_;
v___y_2253_ = v___y_2387_;
v___y_2254_ = v___y_2388_;
v___y_2255_ = v___x_2401_;
v___y_2256_ = v___y_2389_;
v___y_2257_ = v___y_2390_;
v___y_2258_ = v___y_2393_;
v___y_2259_ = v___y_2391_;
v___y_2260_ = v___y_2392_;
v___y_2261_ = v___y_2394_;
v___y_2262_ = v___y_2395_;
v___y_2263_ = v___y_2396_;
v_a_2264_ = v___x_2402_;
goto v___jp_2244_;
}
else
{
size_t v___x_2405_; size_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = ((size_t)0ULL);
v___x_2406_ = lean_usize_of_nat(v___y_2378_);
lean_dec(v___y_2378_);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v___y_2392_, v___x_2405_, v___x_2406_, v___x_2402_, v___y_2395_, v___y_2394_, v___y_2381_, v___y_2393_, v___y_2396_, v___y_2386_, v___y_2388_, v___y_2390_, v___y_2389_, v___y_2383_, v___y_2382_);
v___y_2267_ = v___y_2380_;
v___y_2268_ = v___y_2381_;
v___y_2269_ = v___y_2382_;
v___y_2270_ = v___y_2383_;
v___y_2271_ = v___y_2385_;
v___y_2272_ = v___y_2384_;
v___y_2273_ = v___y_2386_;
v___y_2274_ = v_a_2398_;
v___y_2275_ = v___y_2387_;
v___y_2276_ = v___y_2388_;
v___y_2277_ = v___x_2401_;
v___y_2278_ = v___y_2389_;
v___y_2279_ = v___y_2390_;
v___y_2280_ = v___y_2392_;
v___y_2281_ = v___y_2391_;
v___y_2282_ = v___y_2393_;
v___y_2283_ = v___y_2394_;
v___y_2284_ = v___y_2395_;
v___y_2285_ = v___y_2396_;
v___y_2286_ = v___x_2407_;
goto v___jp_2266_;
}
}
else
{
size_t v___x_2408_; size_t v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = ((size_t)0ULL);
v___x_2409_ = lean_usize_of_nat(v___y_2378_);
lean_dec(v___y_2378_);
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v___y_2392_, v___x_2408_, v___x_2409_, v___x_2402_, v___y_2395_, v___y_2394_, v___y_2381_, v___y_2393_, v___y_2396_, v___y_2386_, v___y_2388_, v___y_2390_, v___y_2389_, v___y_2383_, v___y_2382_);
v___y_2267_ = v___y_2380_;
v___y_2268_ = v___y_2381_;
v___y_2269_ = v___y_2382_;
v___y_2270_ = v___y_2383_;
v___y_2271_ = v___y_2385_;
v___y_2272_ = v___y_2384_;
v___y_2273_ = v___y_2386_;
v___y_2274_ = v_a_2398_;
v___y_2275_ = v___y_2387_;
v___y_2276_ = v___y_2388_;
v___y_2277_ = v___x_2401_;
v___y_2278_ = v___y_2389_;
v___y_2279_ = v___y_2390_;
v___y_2280_ = v___y_2392_;
v___y_2281_ = v___y_2391_;
v___y_2282_ = v___y_2393_;
v___y_2283_ = v___y_2394_;
v___y_2284_ = v___y_2395_;
v___y_2285_ = v___y_2396_;
v___y_2286_ = v___x_2410_;
goto v___jp_2266_;
}
}
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2411_ = lean_io_get_num_heartbeats();
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_nat_dec_lt(v___y_2379_, v___y_2378_);
if (v___x_2413_ == 0)
{
lean_dec(v___y_2378_);
v___y_2326_ = v___x_2411_;
v___y_2327_ = v___y_2380_;
v___y_2328_ = v___y_2381_;
v___y_2329_ = v___y_2382_;
v___y_2330_ = v___y_2383_;
v___y_2331_ = v___y_2385_;
v___y_2332_ = v___y_2384_;
v___y_2333_ = v___y_2386_;
v___y_2334_ = v_a_2398_;
v___y_2335_ = v___y_2387_;
v___y_2336_ = v___y_2388_;
v___y_2337_ = v___y_2389_;
v___y_2338_ = v___y_2390_;
v___y_2339_ = v___y_2393_;
v___y_2340_ = v___y_2391_;
v___y_2341_ = v___y_2392_;
v___y_2342_ = v___y_2394_;
v___y_2343_ = v___y_2395_;
v___y_2344_ = v___y_2396_;
v_a_2345_ = v___x_2412_;
goto v___jp_2325_;
}
else
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_nat_dec_le(v___y_2378_, v___y_2378_);
if (v___x_2414_ == 0)
{
if (v___x_2413_ == 0)
{
lean_dec(v___y_2378_);
v___y_2326_ = v___x_2411_;
v___y_2327_ = v___y_2380_;
v___y_2328_ = v___y_2381_;
v___y_2329_ = v___y_2382_;
v___y_2330_ = v___y_2383_;
v___y_2331_ = v___y_2385_;
v___y_2332_ = v___y_2384_;
v___y_2333_ = v___y_2386_;
v___y_2334_ = v_a_2398_;
v___y_2335_ = v___y_2387_;
v___y_2336_ = v___y_2388_;
v___y_2337_ = v___y_2389_;
v___y_2338_ = v___y_2390_;
v___y_2339_ = v___y_2393_;
v___y_2340_ = v___y_2391_;
v___y_2341_ = v___y_2392_;
v___y_2342_ = v___y_2394_;
v___y_2343_ = v___y_2395_;
v___y_2344_ = v___y_2396_;
v_a_2345_ = v___x_2412_;
goto v___jp_2325_;
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_of_nat(v___y_2378_);
lean_dec(v___y_2378_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v___y_2392_, v___x_2415_, v___x_2416_, v___x_2412_, v___y_2395_, v___y_2394_, v___y_2381_, v___y_2393_, v___y_2396_, v___y_2386_, v___y_2388_, v___y_2390_, v___y_2389_, v___y_2383_, v___y_2382_);
v___y_2348_ = v___x_2411_;
v___y_2349_ = v___y_2380_;
v___y_2350_ = v___y_2381_;
v___y_2351_ = v___y_2382_;
v___y_2352_ = v___y_2383_;
v___y_2353_ = v___y_2385_;
v___y_2354_ = v___y_2384_;
v___y_2355_ = v___y_2386_;
v___y_2356_ = v_a_2398_;
v___y_2357_ = v___y_2387_;
v___y_2358_ = v___y_2388_;
v___y_2359_ = v___y_2389_;
v___y_2360_ = v___y_2390_;
v___y_2361_ = v___y_2392_;
v___y_2362_ = v___y_2391_;
v___y_2363_ = v___y_2393_;
v___y_2364_ = v___y_2394_;
v___y_2365_ = v___y_2395_;
v___y_2366_ = v___y_2396_;
v___y_2367_ = v___x_2417_;
goto v___jp_2347_;
}
}
else
{
size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = lean_usize_of_nat(v___y_2378_);
lean_dec(v___y_2378_);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v___y_2392_, v___x_2418_, v___x_2419_, v___x_2412_, v___y_2395_, v___y_2394_, v___y_2381_, v___y_2393_, v___y_2396_, v___y_2386_, v___y_2388_, v___y_2390_, v___y_2389_, v___y_2383_, v___y_2382_);
v___y_2348_ = v___x_2411_;
v___y_2349_ = v___y_2380_;
v___y_2350_ = v___y_2381_;
v___y_2351_ = v___y_2382_;
v___y_2352_ = v___y_2383_;
v___y_2353_ = v___y_2385_;
v___y_2354_ = v___y_2384_;
v___y_2355_ = v___y_2386_;
v___y_2356_ = v_a_2398_;
v___y_2357_ = v___y_2387_;
v___y_2358_ = v___y_2388_;
v___y_2359_ = v___y_2389_;
v___y_2360_ = v___y_2390_;
v___y_2361_ = v___y_2392_;
v___y_2362_ = v___y_2391_;
v___y_2363_ = v___y_2393_;
v___y_2364_ = v___y_2394_;
v___y_2365_ = v___y_2395_;
v___y_2366_ = v___y_2396_;
v___y_2367_ = v___x_2420_;
goto v___jp_2347_;
}
}
}
}
v___jp_2421_:
{
lean_object* v_options_2434_; lean_object* v_inheritedTraceOptions_2435_; uint8_t v_hasTrace_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_options_2434_ = lean_ctor_get(v___y_2432_, 2);
v_inheritedTraceOptions_2435_ = lean_ctor_get(v___y_2432_, 13);
v_hasTrace_2436_ = lean_ctor_get_uint8(v_options_2434_, sizeof(void*)*1);
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = lean_array_get_size(v_hypotheses_2422_);
if (v_hasTrace_2436_ == 0)
{
uint8_t v___x_2439_; 
v___x_2439_ = lean_nat_dec_lt(v___x_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
v___y_2185_ = v_hypotheses_2422_;
v___y_2186_ = v___y_2424_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = lean_box(0);
v___x_2441_ = lean_nat_dec_le(v___x_2438_, v___x_2438_);
if (v___x_2441_ == 0)
{
if (v___x_2439_ == 0)
{
v___y_2185_ = v_hypotheses_2422_;
v___y_2186_ = v___y_2424_;
goto v___jp_2184_;
}
else
{
size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = lean_usize_of_nat(v___x_2438_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_hypotheses_2422_, v___x_2442_, v___x_2443_, v___x_2440_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
v___y_2206_ = v_hypotheses_2422_;
v___y_2207_ = v___y_2424_;
v___y_2208_ = v___x_2444_;
goto v___jp_2205_;
}
}
else
{
size_t v___x_2445_; size_t v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = lean_usize_of_nat(v___x_2438_);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_hypotheses_2422_, v___x_2445_, v___x_2446_, v___x_2440_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
v___y_2206_ = v_hypotheses_2422_;
v___y_2207_ = v___y_2424_;
v___y_2208_ = v___x_2447_;
goto v___jp_2205_;
}
}
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__3));
v___x_2449_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1));
v___x_2450_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__2___closed__6);
v___x_2451_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2435_, v_options_2434_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2452_ = l_Lean_trace_profiler;
v___x_2453_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_options_2434_, v___x_2452_);
if (v___x_2453_ == 0)
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_nat_dec_lt(v___x_2437_, v___x_2438_);
if (v___x_2454_ == 0)
{
v___y_2185_ = v_hypotheses_2422_;
v___y_2186_ = v___y_2424_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_nat_dec_le(v___x_2438_, v___x_2438_);
if (v___x_2456_ == 0)
{
if (v___x_2454_ == 0)
{
v___y_2185_ = v_hypotheses_2422_;
v___y_2186_ = v___y_2424_;
goto v___jp_2184_;
}
else
{
size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = ((size_t)0ULL);
v___x_2458_ = lean_usize_of_nat(v___x_2438_);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_hypotheses_2422_, v___x_2457_, v___x_2458_, v___x_2455_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
v___y_2206_ = v_hypotheses_2422_;
v___y_2207_ = v___y_2424_;
v___y_2208_ = v___x_2459_;
goto v___jp_2205_;
}
}
else
{
size_t v___x_2460_; size_t v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = ((size_t)0ULL);
v___x_2461_ = lean_usize_of_nat(v___x_2438_);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_hypotheses_2422_, v___x_2460_, v___x_2461_, v___x_2455_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
v___y_2206_ = v_hypotheses_2422_;
v___y_2207_ = v___y_2424_;
v___y_2208_ = v___x_2462_;
goto v___jp_2205_;
}
}
}
else
{
v___y_2378_ = v___x_2438_;
v___y_2379_ = v___x_2437_;
v___y_2380_ = v_options_2434_;
v___y_2381_ = v___y_2425_;
v___y_2382_ = v___y_2433_;
v___y_2383_ = v___y_2432_;
v___y_2384_ = v___x_2451_;
v___y_2385_ = v___x_2448_;
v___y_2386_ = v___y_2428_;
v___y_2387_ = v_hasTrace_2436_;
v___y_2388_ = v___y_2429_;
v___y_2389_ = v___y_2431_;
v___y_2390_ = v___y_2430_;
v___y_2391_ = v___x_2449_;
v___y_2392_ = v_hypotheses_2422_;
v___y_2393_ = v___y_2426_;
v___y_2394_ = v___y_2424_;
v___y_2395_ = v___y_2423_;
v___y_2396_ = v___y_2427_;
goto v___jp_2377_;
}
}
else
{
v___y_2378_ = v___x_2438_;
v___y_2379_ = v___x_2437_;
v___y_2380_ = v_options_2434_;
v___y_2381_ = v___y_2425_;
v___y_2382_ = v___y_2433_;
v___y_2383_ = v___y_2432_;
v___y_2384_ = v___x_2451_;
v___y_2385_ = v___x_2448_;
v___y_2386_ = v___y_2428_;
v___y_2387_ = v_hasTrace_2436_;
v___y_2388_ = v___y_2429_;
v___y_2389_ = v___y_2431_;
v___y_2390_ = v___y_2430_;
v___y_2391_ = v___x_2449_;
v___y_2392_ = v_hypotheses_2422_;
v___y_2393_ = v___y_2426_;
v___y_2394_ = v___y_2424_;
v___y_2395_ = v___y_2423_;
v___y_2396_ = v___y_2427_;
goto v___jp_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___boxed(lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(lean_object* v_cls_2502_, lean_object* v_msg_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v_cls_2502_, v_msg_2503_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___boxed(lean_object* v_cls_2517_, lean_object* v_msg_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(v_cls_2517_, v_msg_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(lean_object* v_00_u03b1_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___redArg(v_x_2533_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2547_, lean_object* v_x_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(v_00_u03b1_2547_, v_x_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5(size_t v_sz_2562_, size_t v_i_2563_, lean_object* v_bs_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___redArg(v_sz_2562_, v_i_2563_, v_bs_2564_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5___boxed(lean_object* v_sz_2578_, lean_object* v_i_2579_, lean_object* v_bs_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
size_t v_sz_boxed_2593_; size_t v_i_boxed_2594_; lean_object* v_res_2595_; 
v_sz_boxed_2593_ = lean_unbox_usize(v_sz_2578_);
lean_dec(v_sz_2578_);
v_i_boxed_2594_ = lean_unbox_usize(v_i_2579_);
lean_dec(v_i_2579_);
v_res_2595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__5(v_sz_boxed_2593_, v_i_boxed_2594_, v_bs_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(lean_object* v_oldTraces_2596_, lean_object* v_data_2597_, lean_object* v_ref_2598_, lean_object* v_msg_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_oldTraces_2596_, v_data_2597_, v_ref_2598_, v_msg_2599_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___boxed(lean_object* v_oldTraces_2613_, lean_object* v_data_2614_, lean_object* v_ref_2615_, lean_object* v_msg_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(v_oldTraces_2613_, v_data_2614_, v_ref_2615_, v_msg_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2629_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
}
#ifdef __cplusplus
}
#endif
