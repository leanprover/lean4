// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic import Lean.Elab.Tactic.FalseOrByContra import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.LitValues import Lean.Meta.Sym.Util import Lean.Meta.Sym.Grind import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Sym.Intro import Lean.Meta.Tactic.Grind.Simp
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
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
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
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getExprs___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_introN(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Platform"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numBits"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 13, 33, 186, 170, 198, 65, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getInt64Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getUInt64Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getBitVecValue_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5___boxed(lean_object**);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4___boxed(lean_object**);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordLocalHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordLocalHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "`bv_decide` failed to introduce the negated goal"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "_private.Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps.0.Lean.Meta.Tactic.BVDecide.Normalize.symByContradiction"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Collected initial hypotheses"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___boxed(lean_object**);
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___redArg(lean_object* v_hyp_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_st_ref_take(v_a_2_);
v___x_5_ = lean_box(0);
v___x_6_ = lean_array_push(v___x_4_, v_hyp_1_);
v___x_7_ = lean_st_ref_put(v_a_2_, v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_5_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp(lean_object* v_hyp_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_27_ = lean_st_ref_take(v_a_15_);
v___x_28_ = lean_box(0);
v___x_29_ = lean_array_push(v___x_27_, v_hyp_13_);
v___x_30_ = lean_st_ref_put(v_a_15_, v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_28_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp___boxed(lean_object* v_hyp_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp(v_hyp_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec(v_a_35_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt___redArg(lean_object* v_x_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
uint8_t v_fixedInt_61_; 
v_fixedInt_61_ = lean_ctor_get_uint8(v_a_48_, sizeof(void*)*2 + 6);
if (v_fixedInt_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec_ref(v_x_47_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; 
lean_inc(v_a_59_);
lean_inc_ref(v_a_58_);
lean_inc(v_a_57_);
lean_inc_ref(v_a_56_);
lean_inc(v_a_55_);
lean_inc_ref(v_a_54_);
lean_inc(v_a_53_);
lean_inc_ref(v_a_52_);
lean_inc(v_a_51_);
lean_inc(v_a_50_);
lean_inc(v_a_49_);
lean_inc_ref(v_a_48_);
v___x_64_ = lean_apply_13(v_x_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, lean_box(0));
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt___redArg___boxed(lean_object* v_x_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt___redArg(v_x_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt(lean_object* v_00_u03b1_80_, lean_object* v_x_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
uint8_t v_fixedInt_95_; 
v_fixedInt_95_ = lean_ctor_get_uint8(v_a_82_, sizeof(void*)*2 + 6);
if (v_fixedInt_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec_ref(v_x_81_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
lean_inc(v_a_93_);
lean_inc_ref(v_a_92_);
lean_inc(v_a_91_);
lean_inc_ref(v_a_90_);
lean_inc(v_a_89_);
lean_inc_ref(v_a_88_);
lean_inc(v_a_87_);
lean_inc_ref(v_a_86_);
lean_inc(v_a_85_);
lean_inc(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
v___x_98_ = lean_apply_13(v_x_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, lean_box(0));
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt___boxed(lean_object* v_00_u03b1_99_, lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_withFixedInt(v_00_u03b1_99_, v_x_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(uint8_t v___x_115_, lean_object* v_x_116_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
else
{
lean_object* v_head_118_; lean_object* v_tail_119_; lean_object* v___x_120_; 
v_head_118_ = lean_ctor_get(v_x_116_, 0);
lean_inc_n(v_head_118_, 2);
v_tail_119_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_tail_119_);
lean_dec_ref_known(v_x_116_, 2);
v___x_120_ = l_Lean_Meta_Sym_getNatValue_x3f(v_head_118_);
if (lean_obj_tag(v___x_120_) == 0)
{
if (v___x_115_ == 0)
{
lean_dec(v_head_118_);
v_x_116_ = v_tail_119_;
goto _start;
}
else
{
lean_object* v___x_122_; 
lean_dec(v_tail_119_);
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v_head_118_);
return v___x_122_;
}
}
else
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec(v_tail_119_);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v___x_120_, 0);
lean_dec(v_unused_130_);
v___x_124_ = v___x_120_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_dec(v___x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v_head_118_);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_head_118_);
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
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0___boxed(lean_object* v___x_131_, lean_object* v_x_132_){
_start:
{
uint8_t v___x_10250__boxed_133_; lean_object* v_res_134_; 
v___x_10250__boxed_133_ = lean_unbox(v___x_131_);
v_res_134_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(v___x_10250__boxed_133_, v_x_132_);
return v_res_134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__4(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_box(0);
v___x_143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__3));
v___x_144_ = l_Lean_mkConst(v___x_143_, v___x_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg(lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___closed__4);
v___x_158_ = l_Lean_Meta_Sym_shareCommonInc(v___x_157_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_221_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_221_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_221_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_221_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_163_ = 0;
v___x_164_ = lean_st_ref_get(v_a_146_);
lean_inc(v_a_159_);
v___x_165_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_164_, v_a_159_, v___x_163_);
lean_dec(v___x_164_);
v___x_166_ = l_List_isEmpty___redArg(v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(v___x_166_, v___x_165_);
if (lean_obj_tag(v___x_167_) == 1)
{
lean_object* v_val_168_; lean_object* v___x_169_; 
lean_del_object(v___x_161_);
v_val_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc_n(v_val_168_, 2);
lean_dec_ref_known(v___x_167_, 1);
lean_inc(v_a_159_);
v___x_169_ = l_Lean_Meta_mkEq(v_a_159_, v_val_168_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_171_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_169_, 1);
v___x_171_ = l_Lean_Meta_Sym_shareCommonInc(v_a_170_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_173_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_171_, 1);
lean_inc(v_a_155_);
lean_inc_ref(v_a_154_);
lean_inc(v_a_153_);
lean_inc_ref(v_a_152_);
lean_inc(v_a_151_);
lean_inc_ref(v_a_150_);
lean_inc(v_a_149_);
lean_inc_ref(v_a_148_);
lean_inc(v_a_147_);
lean_inc(v_a_146_);
v___x_173_ = lean_grind_mk_eq_proof(v_a_159_, v_val_168_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_188_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_188_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_188_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_188_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_178_ = lean_box(0);
v___x_179_ = lean_box(4);
v___x_180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v_a_172_);
lean_ctor_set(v___x_180_, 2, v_a_174_);
lean_ctor_set(v___x_180_, 3, v___x_179_);
v___x_181_ = lean_st_ref_take(v_a_145_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_array_push(v___x_181_, v___x_180_);
v___x_184_ = lean_st_ref_put(v_a_145_, v___x_183_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_182_);
v___x_186_ = v___x_176_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_182_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec(v_a_172_);
v_a_189_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_173_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_173_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec(v_val_168_);
lean_dec(v_a_159_);
v_a_197_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_171_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_171_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec(v_val_168_);
lean_dec(v_a_159_);
v_a_205_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_169_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_169_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_dec(v___x_167_);
lean_dec(v_a_159_);
v___x_213_ = lean_box(0);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_213_);
v___x_215_ = v___x_161_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_219_; 
lean_dec(v___x_165_);
lean_dec(v_a_159_);
v___x_217_ = lean_box(0);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_217_);
v___x_219_ = v___x_161_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_a_222_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_158_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_158_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg___boxed(lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg(v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec(v_a_231_);
lean_dec(v_a_230_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits(lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg(v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___boxed(lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits(v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0___redArg(lean_object* v_getConst_271_, lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_272_) == 0)
{
lean_object* v___x_273_; 
lean_dec_ref(v_getConst_271_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
else
{
lean_object* v_head_274_; lean_object* v_tail_275_; lean_object* v___x_276_; 
v_head_274_ = lean_ctor_get(v_x_272_, 0);
lean_inc_n(v_head_274_, 2);
v_tail_275_ = lean_ctor_get(v_x_272_, 1);
lean_inc(v_tail_275_);
lean_dec_ref_known(v_x_272_, 2);
lean_inc_ref(v_getConst_271_);
v___x_276_ = lean_apply_1(v_getConst_271_, v_head_274_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_dec(v_head_274_);
v_x_272_ = v_tail_275_;
goto _start;
}
else
{
lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_tail_275_);
lean_dec_ref(v_getConst_271_);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v___x_276_, 0);
lean_dec(v_unused_285_);
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v_head_274_);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_head_274_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(lean_object* v_default_286_, lean_object* v_getConst_287_, lean_object* v_a_288_){
_start:
{
uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = 0;
v___x_291_ = lean_st_ref_get(v_a_288_);
lean_inc_ref(v_default_286_);
v___x_292_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_291_, v_default_286_, v___x_290_);
lean_dec(v___x_291_);
v___x_293_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0___redArg(v_getConst_287_, v___x_292_);
if (lean_obj_tag(v___x_293_) == 1)
{
lean_object* v___x_294_; 
lean_dec_ref(v_default_286_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v___x_293_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_default_286_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg___boxed(lean_object* v_default_297_, lean_object* v_getConst_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_default_297_, v_getConst_298_, v_a_299_);
lean_dec(v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType(lean_object* v_00_u03b1_302_, lean_object* v_default_303_, lean_object* v_getConst_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_default_303_, v_getConst_304_, v_a_307_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___boxed(lean_object* v_00_u03b1_319_, lean_object* v_default_320_, lean_object* v_getConst_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType(v_00_u03b1_319_, v_default_320_, v_getConst_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0(lean_object* v_00_u03b1_336_, lean_object* v_getConst_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType_spec__0___redArg(v_getConst_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(lean_object* v_x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_box(0);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
else
{
lean_object* v_head_348_; lean_object* v_tail_349_; lean_object* v___x_350_; 
v_head_348_ = lean_ctor_get(v_x_340_, 0);
lean_inc_n(v_head_348_, 2);
v_tail_349_ = lean_ctor_get(v_x_340_, 1);
lean_inc(v_tail_349_);
lean_dec_ref_known(v_x_340_, 2);
v___x_350_ = l_Lean_Meta_isConstructorApp(v_head_348_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_361_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_361_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_361_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_361_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
uint8_t v___x_355_; 
v___x_355_ = lean_unbox(v_a_351_);
lean_dec(v_a_351_);
if (v___x_355_ == 0)
{
lean_del_object(v___x_353_);
lean_dec(v_head_348_);
v_x_340_ = v_tail_349_;
goto _start;
}
else
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec(v_tail_349_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_head_348_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_357_);
v___x_359_ = v___x_353_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_tail_349_);
lean_dec(v_head_348_);
v_a_362_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_350_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_350_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg___boxed(lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(v_x_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(lean_object* v_root_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___x_452_; 
lean_inc_ref(v_root_422_);
v___x_452_ = l_Lean_Meta_Sym_inferType(v_root_422_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_656_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_656_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_656_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_656_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___x_509_; 
lean_inc(v_a_453_);
v___x_509_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_453_, v_a_432_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_647_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_647_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_647_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_647_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___y_515_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = l_Lean_Expr_cleanupAnnotations(v_a_510_);
v___x_523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__4));
v___x_524_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__6));
v___x_526_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__8));
v___x_528_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__10));
v___x_530_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__12));
v___x_532_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__14));
v___x_534_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__16));
v___x_536_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__18));
v___x_538_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__20));
v___x_540_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__22));
v___x_542_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__24));
v___x_544_ = l_Lean_Expr_isConstOf(v___x_522_, v___x_543_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = l_Lean_Expr_isApp(v___x_522_);
if (v___x_545_ == 0)
{
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
v___y_458_ = v_a_423_;
v___y_459_ = v_a_424_;
v___y_460_ = v_a_425_;
v___y_461_ = v_a_426_;
v___y_462_ = v_a_427_;
v___y_463_ = v_a_428_;
v___y_464_ = v_a_429_;
v___y_465_ = v_a_430_;
v___y_466_ = v_a_431_;
v___y_467_ = v_a_432_;
v___y_468_ = v_a_433_;
v___y_469_ = v_a_434_;
goto v___jp_457_;
}
else
{
lean_object* v_arg_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_arg_546_ = lean_ctor_get(v___x_522_, 1);
lean_inc_ref(v_arg_546_);
v___x_547_ = l_Lean_Expr_appFnCleanup___redArg(v___x_522_);
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__26));
v___x_549_ = l_Lean_Expr_isConstOf(v___x_547_, v___x_548_);
lean_dec_ref(v___x_547_);
if (v___x_549_ == 0)
{
lean_dec_ref(v_arg_546_);
lean_del_object(v___x_512_);
v___y_458_ = v_a_423_;
v___y_459_ = v_a_424_;
v___y_460_ = v_a_425_;
v___y_461_ = v_a_426_;
v___y_462_ = v_a_427_;
v___y_463_ = v_a_428_;
v___y_464_ = v_a_429_;
v___y_465_ = v_a_430_;
v___y_466_ = v_a_431_;
v___y_467_ = v_a_432_;
v___y_468_ = v_a_433_;
v___y_469_ = v_a_434_;
goto v___jp_457_;
}
else
{
lean_object* v___x_550_; 
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v___x_550_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_546_);
if (lean_obj_tag(v___x_550_) == 0)
{
v___y_515_ = v___x_544_;
goto v___jp_514_;
}
else
{
lean_dec_ref_known(v___x_550_, 1);
v___y_515_ = v___x_549_;
goto v___jp_514_;
}
}
}
}
else
{
lean_object* v___x_551_; 
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
lean_inc_ref(v_root_422_);
v___x_551_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_root_422_, v_a_425_, v_a_429_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; uint8_t v___x_553_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = lean_unbox(v_a_552_);
lean_dec(v_a_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_inc_ref(v_root_422_);
v___x_554_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_root_422_, v_a_425_, v_a_429_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_582_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_582_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_582_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_582_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v___x_559_; 
v___x_559_ = lean_unbox(v_a_555_);
lean_dec(v_a_555_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_root_422_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_560_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
lean_object* v___x_564_; 
lean_del_object(v___x_557_);
lean_dec_ref(v_root_422_);
v___x_564_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_429_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_a_574_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_564_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_564_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
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
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_root_422_);
v_a_583_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_554_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_554_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v___x_591_; 
lean_dec_ref(v_root_422_);
v___x_591_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_429_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v_a_592_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_a_601_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_591_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_591_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_root_422_);
v_a_609_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_551_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_551_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
else
{
uint8_t v_fixedInt_617_; 
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v_fixedInt_617_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec_ref(v_root_422_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__27));
v___x_621_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_620_, v_a_425_);
return v___x_621_;
}
}
}
else
{
uint8_t v_fixedInt_622_; 
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v_fixedInt_622_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
lean_dec_ref(v_root_422_);
v___x_623_ = lean_box(0);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__28));
v___x_626_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_625_, v_a_425_);
return v___x_626_;
}
}
}
else
{
uint8_t v_fixedInt_627_; 
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v_fixedInt_627_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref(v_root_422_);
v___x_628_ = lean_box(0);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__29));
v___x_631_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_630_, v_a_425_);
return v___x_631_;
}
}
}
else
{
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v___y_445_ = v_a_423_;
v___y_446_ = v_a_425_;
goto v___jp_444_;
}
}
else
{
uint8_t v_fixedInt_632_; 
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v_fixedInt_632_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec_ref(v_root_422_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__30));
v___x_636_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_635_, v_a_425_);
return v___x_636_;
}
}
}
else
{
uint8_t v_fixedInt_637_; 
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v_fixedInt_637_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec_ref(v_root_422_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__31));
v___x_641_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_640_, v_a_425_);
return v___x_641_;
}
}
}
else
{
uint8_t v_fixedInt_642_; 
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v_fixedInt_642_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec_ref(v_root_422_);
v___x_643_ = lean_box(0);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__32));
v___x_646_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_645_, v_a_425_);
return v___x_646_;
}
}
}
else
{
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v___y_437_ = v_a_423_;
v___y_438_ = v_a_425_;
goto v___jp_436_;
}
}
else
{
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v___y_445_ = v_a_423_;
v___y_446_ = v_a_425_;
goto v___jp_444_;
}
}
else
{
lean_dec_ref(v___x_522_);
lean_del_object(v___x_512_);
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
v___y_437_ = v_a_423_;
v___y_438_ = v_a_425_;
goto v___jp_436_;
}
v___jp_514_:
{
if (v___y_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec_ref(v_root_422_);
v___x_516_ = lean_box(0);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_del_object(v___x_512_);
v___x_520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__2));
v___x_521_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_520_, v_a_425_);
return v___x_521_;
}
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_del_object(v___x_455_);
lean_dec(v_a_453_);
lean_dec_ref(v_root_422_);
v_a_648_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_509_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_509_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
v___jp_457_:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Expr_getAppFn_x27(v_a_453_);
lean_dec(v_a_453_);
if (lean_obj_tag(v___x_470_) == 4)
{
lean_object* v_declName_471_; lean_object* v___x_472_; 
lean_del_object(v___x_455_);
v_declName_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_declName_471_);
lean_dec_ref_known(v___x_470_, 2);
v___x_472_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v___y_458_, v_declName_471_, v___y_468_, v___y_469_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_496_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_496_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_496_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_496_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_unbox(v_a_473_);
lean_dec(v_a_473_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_480_; 
lean_dec_ref(v_root_422_);
v___x_478_ = lean_box(0);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_478_);
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_del_object(v___x_475_);
v___x_482_ = 0;
v___x_483_ = lean_st_ref_get(v___y_460_);
lean_inc_ref(v_root_422_);
v___x_484_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_483_, v_root_422_, v___x_482_);
lean_dec(v___x_483_);
v___x_485_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(v___x_484_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
if (lean_obj_tag(v_a_486_) == 1)
{
lean_dec_ref_known(v_a_486_, 1);
lean_dec_ref(v_root_422_);
return v___x_485_;
}
else
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_a_486_);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_485_, 0);
lean_dec(v_unused_495_);
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
else
{
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_root_422_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_dec_ref(v_root_422_);
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v_root_422_);
v_a_497_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_472_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_472_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec_ref(v___x_470_);
lean_dec_ref(v_root_422_);
v___x_505_ = lean_box(0);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_505_);
v___x_507_ = v___x_455_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_root_422_);
v_a_657_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_452_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_452_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
v___jp_436_:
{
uint8_t v_fixedInt_439_; 
v_fixedInt_439_ = lean_ctor_get_uint8(v___y_437_, sizeof(void*)*2 + 6);
if (v_fixedInt_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec_ref(v_root_422_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0));
v___x_443_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_442_, v___y_438_);
return v___x_443_;
}
}
v___jp_444_:
{
uint8_t v_fixedInt_447_; 
v_fixedInt_447_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*2 + 6);
if (v_fixedInt_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref(v_root_422_);
v___x_448_ = lean_box(0);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1));
v___x_451_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_450_, v___y_446_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___boxed(lean_object* v_root_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_root_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0(lean_object* v_x_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(v_x_680_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___boxed(lean_object* v_x_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0(v_x_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(lean_object* v_val_710_, uint8_t v___y_711_, lean_object* v_as_x27_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
if (lean_obj_tag(v_as_x27_712_) == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v_val_710_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_b_713_);
return v___x_726_;
}
else
{
lean_object* v_head_727_; lean_object* v_tail_728_; lean_object* v___x_729_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; uint8_t v___x_779_; 
v_head_727_ = lean_ctor_get(v_as_x27_712_, 0);
v_tail_728_ = lean_ctor_get(v_as_x27_712_, 1);
v___x_729_ = lean_box(0);
v___x_779_ = lean_expr_eqv(v_head_727_, v_val_710_);
if (v___x_779_ == 0)
{
if (v___y_711_ == 0)
{
lean_object* v___x_780_; 
lean_inc_ref(v_val_710_);
lean_inc(v_head_727_);
v___x_780_ = l_Lean_Meta_Grind_hasSameType(v_head_727_, v_val_710_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; uint8_t v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = lean_unbox(v_a_781_);
lean_dec(v_a_781_);
if (v___x_782_ == 0)
{
v_as_x27_712_ = v_tail_728_;
v_b_713_ = v___x_729_;
goto _start;
}
else
{
v___y_731_ = v___y_714_;
v___y_732_ = v___y_715_;
v___y_733_ = v___y_716_;
v___y_734_ = v___y_717_;
v___y_735_ = v___y_718_;
v___y_736_ = v___y_719_;
v___y_737_ = v___y_720_;
v___y_738_ = v___y_721_;
v___y_739_ = v___y_722_;
v___y_740_ = v___y_723_;
v___y_741_ = v___y_724_;
goto v___jp_730_;
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_val_710_);
v_a_784_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_780_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_780_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
v___y_731_ = v___y_714_;
v___y_732_ = v___y_715_;
v___y_733_ = v___y_716_;
v___y_734_ = v___y_717_;
v___y_735_ = v___y_718_;
v___y_736_ = v___y_719_;
v___y_737_ = v___y_720_;
v___y_738_ = v___y_721_;
v___y_739_ = v___y_722_;
v___y_740_ = v___y_723_;
v___y_741_ = v___y_724_;
goto v___jp_730_;
}
}
else
{
v_as_x27_712_ = v_tail_728_;
v_b_713_ = v___x_729_;
goto _start;
}
v___jp_730_:
{
lean_object* v___x_742_; 
lean_inc_ref(v_val_710_);
lean_inc(v_head_727_);
v___x_742_ = l_Lean_Meta_mkEq(v_head_727_, v_val_710_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = l_Lean_Meta_Sym_shareCommonInc(v_a_743_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
lean_inc(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v_val_710_);
lean_inc(v_head_727_);
v___x_746_ = lean_grind_mk_eq_proof(v_head_727_, v_val_710_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = lean_box(0);
v___x_749_ = lean_box(4);
v___x_750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v_a_745_);
lean_ctor_set(v___x_750_, 2, v_a_747_);
lean_ctor_set(v___x_750_, 3, v___x_749_);
v___x_751_ = lean_st_ref_take(v___y_731_);
v___x_752_ = lean_array_push(v___x_751_, v___x_750_);
v___x_753_ = lean_st_ref_put(v___y_731_, v___x_752_);
v_as_x27_712_ = v_tail_728_;
v_b_713_ = v___x_729_;
goto _start;
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_745_);
lean_dec_ref(v_val_710_);
v_a_755_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_746_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_746_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v_val_710_);
v_a_763_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_744_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_744_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_val_710_);
v_a_771_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_742_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_742_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg___boxed(lean_object* v_val_793_, lean_object* v___y_794_, lean_object* v_as_x27_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
uint8_t v___y_46584__boxed_809_; lean_object* v_res_810_; 
v___y_46584__boxed_809_ = lean_unbox(v___y_794_);
v_res_810_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_793_, v___y_46584__boxed_809_, v_as_x27_795_, v_b_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v_as_x27_795_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5(lean_object* v_as_811_, size_t v_sz_812_, size_t v_i_813_, lean_object* v_b_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_lt(v_i_813_, v_sz_812_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v_b_814_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; lean_object* v_a_832_; lean_object* v___x_837_; lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_b_814_);
v___x_830_ = lean_box(0);
v___x_837_ = lean_box(0);
v_a_838_ = lean_array_uget_borrowed(v_as_811_, v_i_813_);
v___x_839_ = lean_st_ref_get(v___y_817_);
lean_inc(v_a_838_);
v___x_840_ = l_Lean_Meta_Grind_Goal_getENode(v___x_839_, v_a_838_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_841_);
if (v___x_842_ == 0)
{
lean_dec(v_a_841_);
v_a_832_ = v___x_837_;
goto v___jp_831_;
}
else
{
lean_object* v___x_843_; 
lean_inc(v_a_838_);
v___x_843_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_a_838_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
if (lean_obj_tag(v_a_844_) == 1)
{
lean_object* v_val_845_; uint8_t v___y_847_; uint8_t v_heqProofs_860_; 
v_val_845_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_val_845_);
lean_dec_ref_known(v_a_844_, 1);
v_heqProofs_860_ = lean_ctor_get_uint8(v_a_841_, sizeof(void*)*12 + 4);
lean_dec(v_a_841_);
if (v_heqProofs_860_ == 0)
{
v___y_847_ = v___x_842_;
goto v___jp_846_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = 0;
v___y_847_ = v___x_861_;
goto v___jp_846_;
}
v___jp_846_:
{
uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_848_ = 0;
v___x_849_ = lean_st_ref_get(v___y_817_);
lean_inc(v_a_838_);
v___x_850_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_849_, v_a_838_, v___x_848_);
lean_dec(v___x_849_);
v___x_851_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_845_, v___y_847_, v___x_850_, v___x_837_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___x_850_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec_ref_known(v___x_851_, 1);
v_a_832_ = v___x_837_;
goto v___jp_831_;
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
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
else
{
lean_dec(v_a_844_);
lean_dec(v_a_841_);
v_a_832_ = v___x_837_;
goto v___jp_831_;
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_841_);
v_a_862_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_843_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_843_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_840_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_840_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
v___jp_831_:
{
lean_object* v___x_833_; size_t v___x_834_; size_t v___x_835_; 
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_830_);
lean_ctor_set(v___x_833_, 1, v_a_832_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_add(v_i_813_, v___x_834_);
v_i_813_ = v___x_835_;
v_b_814_ = v___x_833_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_as_878_ = _args[0];
lean_object* v_sz_879_ = _args[1];
lean_object* v_i_880_ = _args[2];
lean_object* v_b_881_ = _args[3];
lean_object* v___y_882_ = _args[4];
lean_object* v___y_883_ = _args[5];
lean_object* v___y_884_ = _args[6];
lean_object* v___y_885_ = _args[7];
lean_object* v___y_886_ = _args[8];
lean_object* v___y_887_ = _args[9];
lean_object* v___y_888_ = _args[10];
lean_object* v___y_889_ = _args[11];
lean_object* v___y_890_ = _args[12];
lean_object* v___y_891_ = _args[13];
lean_object* v___y_892_ = _args[14];
lean_object* v___y_893_ = _args[15];
lean_object* v___y_894_ = _args[16];
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_879_);
lean_dec(v_sz_879_);
v_i_boxed_896_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5(v_as_878_, v_sz_boxed_895_, v_i_boxed_896_, v_b_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec_ref(v_as_878_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2(lean_object* v_as_901_, size_t v_sz_902_, size_t v_i_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v_b_904_);
return v___x_919_;
}
else
{
lean_object* v___x_920_; lean_object* v_a_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec_ref(v_b_904_);
v___x_920_ = lean_box(0);
v_a_926_ = lean_array_uget_borrowed(v_as_901_, v_i_903_);
v___x_927_ = lean_st_ref_get(v___y_907_);
lean_inc(v_a_926_);
v___x_928_ = l_Lean_Meta_Grind_Goal_getENode(v___x_927_, v_a_926_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___x_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_929_);
if (v___x_930_ == 0)
{
lean_dec(v_a_929_);
goto v___jp_921_;
}
else
{
lean_object* v___x_931_; 
lean_inc(v_a_926_);
v___x_931_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_a_926_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
if (lean_obj_tag(v_a_932_) == 1)
{
lean_object* v_val_933_; uint8_t v___y_935_; uint8_t v_heqProofs_948_; 
v_val_933_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v_a_932_, 1);
v_heqProofs_948_ = lean_ctor_get_uint8(v_a_929_, sizeof(void*)*12 + 4);
lean_dec(v_a_929_);
if (v_heqProofs_948_ == 0)
{
v___y_935_ = v___x_930_;
goto v___jp_934_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = 0;
v___y_935_ = v___x_949_;
goto v___jp_934_;
}
v___jp_934_:
{
uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_936_ = 0;
v___x_937_ = lean_st_ref_get(v___y_907_);
lean_inc(v_a_926_);
v___x_938_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_937_, v_a_926_, v___x_936_);
lean_dec(v___x_937_);
v___x_939_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_933_, v___y_935_, v___x_938_, v___x_920_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___x_938_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_dec_ref_known(v___x_939_, 1);
goto v___jp_921_;
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
else
{
lean_dec(v_a_932_);
lean_dec(v_a_929_);
goto v___jp_921_;
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v_a_929_);
v_a_950_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_931_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_931_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_928_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_928_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
v___jp_921_:
{
lean_object* v___x_922_; size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; 
v___x_922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2___closed__0));
v___x_923_ = ((size_t)1ULL);
v___x_924_ = lean_usize_add(v_i_903_, v___x_923_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5(v_as_901_, v_sz_902_, v___x_924_, v___x_922_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_925_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_as_966_ = _args[0];
lean_object* v_sz_967_ = _args[1];
lean_object* v_i_968_ = _args[2];
lean_object* v_b_969_ = _args[3];
lean_object* v___y_970_ = _args[4];
lean_object* v___y_971_ = _args[5];
lean_object* v___y_972_ = _args[6];
lean_object* v___y_973_ = _args[7];
lean_object* v___y_974_ = _args[8];
lean_object* v___y_975_ = _args[9];
lean_object* v___y_976_ = _args[10];
lean_object* v___y_977_ = _args[11];
lean_object* v___y_978_ = _args[12];
lean_object* v___y_979_ = _args[13];
lean_object* v___y_980_ = _args[14];
lean_object* v___y_981_ = _args[15];
lean_object* v___y_982_ = _args[16];
_start:
{
size_t v_sz_boxed_983_; size_t v_i_boxed_984_; lean_object* v_res_985_; 
v_sz_boxed_983_ = lean_unbox_usize(v_sz_967_);
lean_dec(v_sz_967_);
v_i_boxed_984_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2(v_as_966_, v_sz_boxed_983_, v_i_boxed_984_, v_b_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v_as_966_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_986_, size_t v_sz_987_, size_t v_i_988_, lean_object* v_b_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_usize_dec_lt(v_i_988_, v_sz_987_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_b_989_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; lean_object* v_a_1007_; lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref(v_b_989_);
v___x_1005_ = lean_box(0);
v___x_1012_ = lean_box(0);
v_a_1013_ = lean_array_uget_borrowed(v_as_986_, v_i_988_);
v___x_1014_ = lean_st_ref_get(v___y_992_);
lean_inc(v_a_1013_);
v___x_1015_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1014_, v_a_1013_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___x_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; uint8_t v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_a_1016_);
v_a_1007_ = v___x_1012_;
goto v___jp_1006_;
}
else
{
lean_object* v___x_1018_; 
lean_inc(v_a_1013_);
v___x_1018_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_a_1013_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
if (lean_obj_tag(v_a_1019_) == 1)
{
lean_object* v_val_1020_; uint8_t v___y_1022_; uint8_t v_heqProofs_1035_; 
v_val_1020_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_val_1020_);
lean_dec_ref_known(v_a_1019_, 1);
v_heqProofs_1035_ = lean_ctor_get_uint8(v_a_1016_, sizeof(void*)*12 + 4);
lean_dec(v_a_1016_);
if (v_heqProofs_1035_ == 0)
{
v___y_1022_ = v___x_1017_;
goto v___jp_1021_;
}
else
{
uint8_t v___x_1036_; 
v___x_1036_ = 0;
v___y_1022_ = v___x_1036_;
goto v___jp_1021_;
}
v___jp_1021_:
{
uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1023_ = 0;
v___x_1024_ = lean_st_ref_get(v___y_992_);
lean_inc(v_a_1013_);
v___x_1025_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1024_, v_a_1013_, v___x_1023_);
lean_dec(v___x_1024_);
v___x_1026_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_1020_, v___y_1022_, v___x_1025_, v___x_1012_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___x_1025_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_dec_ref_known(v___x_1026_, 1);
v_a_1007_ = v___x_1012_;
goto v___jp_1006_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
else
{
lean_dec(v_a_1019_);
lean_dec(v_a_1016_);
v_a_1007_ = v___x_1012_;
goto v___jp_1006_;
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v_a_1016_);
v_a_1037_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1018_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1018_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1015_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1015_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
v___jp_1006_:
{
lean_object* v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; 
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1005_);
lean_ctor_set(v___x_1008_, 1, v_a_1007_);
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_988_, v___x_1009_);
v_i_988_ = v___x_1010_;
v_b_989_ = v___x_1008_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_as_1053_ = _args[0];
lean_object* v_sz_1054_ = _args[1];
lean_object* v_i_1055_ = _args[2];
lean_object* v_b_1056_ = _args[3];
lean_object* v___y_1057_ = _args[4];
lean_object* v___y_1058_ = _args[5];
lean_object* v___y_1059_ = _args[6];
lean_object* v___y_1060_ = _args[7];
lean_object* v___y_1061_ = _args[8];
lean_object* v___y_1062_ = _args[9];
lean_object* v___y_1063_ = _args[10];
lean_object* v___y_1064_ = _args[11];
lean_object* v___y_1065_ = _args[12];
lean_object* v___y_1066_ = _args[13];
lean_object* v___y_1067_ = _args[14];
lean_object* v___y_1068_ = _args[15];
lean_object* v___y_1069_ = _args[16];
_start:
{
size_t v_sz_boxed_1070_; size_t v_i_boxed_1071_; lean_object* v_res_1072_; 
v_sz_boxed_1070_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1071_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4(v_as_1053_, v_sz_boxed_1070_, v_i_boxed_1071_, v_b_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v_as_1053_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3(lean_object* v_as_1076_, size_t v_sz_1077_, size_t v_i_1078_, lean_object* v_b_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
uint8_t v___x_1093_; 
v___x_1093_ = lean_usize_dec_lt(v_i_1078_, v_sz_1077_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_b_1079_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; lean_object* v_a_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec_ref(v_b_1079_);
v___x_1095_ = lean_box(0);
v_a_1101_ = lean_array_uget_borrowed(v_as_1076_, v_i_1078_);
v___x_1102_ = lean_st_ref_get(v___y_1082_);
lean_inc(v_a_1101_);
v___x_1103_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1102_, v_a_1101_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___x_1102_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; uint8_t v___x_1105_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1104_);
if (v___x_1105_ == 0)
{
lean_dec(v_a_1104_);
goto v___jp_1096_;
}
else
{
lean_object* v___x_1106_; 
lean_inc(v_a_1101_);
v___x_1106_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_a_1101_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
if (lean_obj_tag(v_a_1107_) == 1)
{
lean_object* v_val_1108_; uint8_t v___y_1110_; uint8_t v_heqProofs_1123_; 
v_val_1108_ = lean_ctor_get(v_a_1107_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v_a_1107_, 1);
v_heqProofs_1123_ = lean_ctor_get_uint8(v_a_1104_, sizeof(void*)*12 + 4);
lean_dec(v_a_1104_);
if (v_heqProofs_1123_ == 0)
{
v___y_1110_ = v___x_1105_;
goto v___jp_1109_;
}
else
{
uint8_t v___x_1124_; 
v___x_1124_ = 0;
v___y_1110_ = v___x_1124_;
goto v___jp_1109_;
}
v___jp_1109_:
{
uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1111_ = 0;
v___x_1112_ = lean_st_ref_get(v___y_1082_);
lean_inc(v_a_1101_);
v___x_1113_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1112_, v_a_1101_, v___x_1111_);
lean_dec(v___x_1112_);
v___x_1114_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_1108_, v___y_1110_, v___x_1113_, v___x_1095_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_dec_ref_known(v___x_1114_, 1);
goto v___jp_1096_;
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
else
{
lean_dec(v_a_1107_);
lean_dec(v_a_1104_);
goto v___jp_1096_;
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v_a_1104_);
v_a_1125_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1106_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1106_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_a_1133_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1103_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1103_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
v___jp_1096_:
{
lean_object* v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3___closed__0));
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_add(v_i_1078_, v___x_1098_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4(v_as_1076_, v_sz_1077_, v___x_1099_, v___x_1097_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_as_1141_ = _args[0];
lean_object* v_sz_1142_ = _args[1];
lean_object* v_i_1143_ = _args[2];
lean_object* v_b_1144_ = _args[3];
lean_object* v___y_1145_ = _args[4];
lean_object* v___y_1146_ = _args[5];
lean_object* v___y_1147_ = _args[6];
lean_object* v___y_1148_ = _args[7];
lean_object* v___y_1149_ = _args[8];
lean_object* v___y_1150_ = _args[9];
lean_object* v___y_1151_ = _args[10];
lean_object* v___y_1152_ = _args[11];
lean_object* v___y_1153_ = _args[12];
lean_object* v___y_1154_ = _args[13];
lean_object* v___y_1155_ = _args[14];
lean_object* v___y_1156_ = _args[15];
lean_object* v___y_1157_ = _args[16];
_start:
{
size_t v_sz_boxed_1158_; size_t v_i_boxed_1159_; lean_object* v_res_1160_; 
v_sz_boxed_1158_ = lean_unbox_usize(v_sz_1142_);
lean_dec(v_sz_1142_);
v_i_boxed_1159_ = lean_unbox_usize(v_i_1143_);
lean_dec(v_i_1143_);
v_res_1160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3(v_as_1141_, v_sz_boxed_1158_, v_i_boxed_1159_, v_b_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_as_1141_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(lean_object* v_init_1161_, lean_object* v_n_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
if (lean_obj_tag(v_n_1162_) == 0)
{
lean_object* v_cs_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; size_t v_sz_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v_cs_1177_ = lean_ctor_get(v_n_1162_, 0);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v_b_1163_);
v_sz_1180_ = lean_array_size(v_cs_1177_);
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2(v_init_1161_, v_cs_1177_, v_sz_1180_, v___x_1181_, v___x_1179_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1197_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1197_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1197_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_fst_1187_; 
v_fst_1187_ = lean_ctor_get(v_a_1183_, 0);
if (lean_obj_tag(v_fst_1187_) == 0)
{
lean_object* v_snd_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v_snd_1188_ = lean_ctor_get(v_a_1183_, 1);
lean_inc(v_snd_1188_);
lean_dec(v_a_1183_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_snd_1188_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1189_);
v___x_1191_ = v___x_1185_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
else
{
lean_object* v_val_1193_; lean_object* v___x_1195_; 
lean_inc_ref(v_fst_1187_);
lean_dec(v_a_1183_);
v_val_1193_ = lean_ctor_get(v_fst_1187_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v_fst_1187_, 1);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_val_1193_);
v___x_1195_ = v___x_1185_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_val_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1182_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1182_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_vs_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; size_t v_sz_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v_vs_1206_ = lean_ctor_get(v_n_1162_, 0);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v_b_1163_);
v_sz_1209_ = lean_array_size(v_vs_1206_);
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3(v_vs_1206_, v_sz_1209_, v___x_1210_, v___x_1208_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1226_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1226_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1226_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_fst_1216_; 
v_fst_1216_ = lean_ctor_get(v_a_1212_, 0);
if (lean_obj_tag(v_fst_1216_) == 0)
{
lean_object* v_snd_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v_snd_1217_ = lean_ctor_get(v_a_1212_, 1);
lean_inc(v_snd_1217_);
lean_dec(v_a_1212_);
v___x_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_snd_1217_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1218_);
v___x_1220_ = v___x_1214_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
else
{
lean_object* v_val_1222_; lean_object* v___x_1224_; 
lean_inc_ref(v_fst_1216_);
lean_dec(v_a_1212_);
v_val_1222_ = lean_ctor_get(v_fst_1216_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v_fst_1216_, 1);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_val_1222_);
v___x_1224_ = v___x_1214_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_val_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_a_1227_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1211_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1211_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2(lean_object* v_init_1235_, lean_object* v_as_1236_, size_t v_sz_1237_, size_t v_i_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_lt(v_i_1238_, v_sz_1237_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_b_1239_);
return v___x_1254_;
}
else
{
lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1289_; 
v_snd_1255_ = lean_ctor_get(v_b_1239_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_b_1239_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_b_1239_, 0);
lean_dec(v_unused_1290_);
v___x_1257_ = v_b_1239_;
v_isShared_1258_ = v_isSharedCheck_1289_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_dec(v_b_1239_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1289_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v_a_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_box(0);
v_a_1260_ = lean_array_uget_borrowed(v_as_1236_, v_i_1238_);
lean_inc(v_snd_1255_);
v___x_1261_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(v_init_1235_, v_a_1260_, v_snd_1255_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1280_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1280_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1280_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
if (lean_obj_tag(v_a_1262_) == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1266_, 0, v_a_1262_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1266_);
v___x_1268_ = v___x_1257_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_snd_1255_);
v___x_1268_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1268_);
v___x_1270_ = v___x_1264_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; 
lean_del_object(v___x_1264_);
lean_dec(v_snd_1255_);
v_a_1273_ = lean_ctor_get(v_a_1262_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v_a_1262_, 1);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_a_1273_);
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1275_ = v___x_1257_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_a_1273_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
size_t v___x_1276_; size_t v___x_1277_; 
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1238_, v___x_1276_);
v_i_1238_ = v___x_1277_;
v_b_1239_ = v___x_1275_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
v_a_1281_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1261_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1261_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_1291_ = _args[0];
lean_object* v_as_1292_ = _args[1];
lean_object* v_sz_1293_ = _args[2];
lean_object* v_i_1294_ = _args[3];
lean_object* v_b_1295_ = _args[4];
lean_object* v___y_1296_ = _args[5];
lean_object* v___y_1297_ = _args[6];
lean_object* v___y_1298_ = _args[7];
lean_object* v___y_1299_ = _args[8];
lean_object* v___y_1300_ = _args[9];
lean_object* v___y_1301_ = _args[10];
lean_object* v___y_1302_ = _args[11];
lean_object* v___y_1303_ = _args[12];
lean_object* v___y_1304_ = _args[13];
lean_object* v___y_1305_ = _args[14];
lean_object* v___y_1306_ = _args[15];
lean_object* v___y_1307_ = _args[16];
lean_object* v___y_1308_ = _args[17];
_start:
{
size_t v_sz_boxed_1309_; size_t v_i_boxed_1310_; lean_object* v_res_1311_; 
v_sz_boxed_1309_ = lean_unbox_usize(v_sz_1293_);
lean_dec(v_sz_1293_);
v_i_boxed_1310_ = lean_unbox_usize(v_i_1294_);
lean_dec(v_i_1294_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2(v_init_1291_, v_as_1292_, v_sz_boxed_1309_, v_i_boxed_1310_, v_b_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v_as_1292_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1___boxed(lean_object* v_init_1312_, lean_object* v_n_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(v_init_1312_, v_n_1313_, v_b_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec_ref(v_n_1313_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(lean_object* v_t_1329_, lean_object* v_init_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_root_1344_; lean_object* v_tail_1345_; lean_object* v___x_1346_; 
v_root_1344_ = lean_ctor_get(v_t_1329_, 0);
v_tail_1345_ = lean_ctor_get(v_t_1329_, 1);
v___x_1346_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(v_init_1330_, v_root_1344_, v_init_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1383_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1383_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1383_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; 
v_a_1351_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v_a_1347_, 1);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_a_1351_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; size_t v_sz_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
lean_del_object(v___x_1349_);
v_a_1355_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v_a_1347_, 1);
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v_a_1355_);
v_sz_1358_ = lean_array_size(v_tail_1345_);
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2(v_tail_1345_, v_sz_1358_, v___x_1359_, v___x_1357_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1374_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1374_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1374_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v_fst_1365_; 
v_fst_1365_ = lean_ctor_get(v_a_1361_, 0);
if (lean_obj_tag(v_fst_1365_) == 0)
{
lean_object* v_snd_1366_; lean_object* v___x_1368_; 
v_snd_1366_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_snd_1366_);
lean_dec(v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v_snd_1366_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_snd_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1372_; 
lean_inc_ref(v_fst_1365_);
lean_dec(v_a_1361_);
v_val_1370_ = lean_ctor_get(v_fst_1365_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v_fst_1365_, 1);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v_val_1370_);
v___x_1372_ = v___x_1363_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_val_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1360_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1360_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1346_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1346_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___boxed(lean_object* v_t_1392_, lean_object* v_init_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(v_t_1392_, v_init_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec_ref(v_t_1392_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_1410_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = lean_box(0);
v___x_1424_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(v_a_1422_, v___x_1423_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1422_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1424_, 0);
lean_dec(v_unused_1432_);
v___x_1426_ = v___x_1424_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v___x_1424_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1423_);
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1423_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
return v___x_1424_;
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1433_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1421_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1421_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities___boxed(lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(lean_object* v_val_1455_, uint8_t v___y_1456_, lean_object* v_as_1457_, lean_object* v_as_x27_1458_, lean_object* v_b_1459_, lean_object* v_a_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_1455_, v___y_1456_, v_as_x27_1458_, v_b_1459_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___boxed(lean_object** _args){
lean_object* v_val_1475_ = _args[0];
lean_object* v___y_1476_ = _args[1];
lean_object* v_as_1477_ = _args[2];
lean_object* v_as_x27_1478_ = _args[3];
lean_object* v_b_1479_ = _args[4];
lean_object* v_a_1480_ = _args[5];
lean_object* v___y_1481_ = _args[6];
lean_object* v___y_1482_ = _args[7];
lean_object* v___y_1483_ = _args[8];
lean_object* v___y_1484_ = _args[9];
lean_object* v___y_1485_ = _args[10];
lean_object* v___y_1486_ = _args[11];
lean_object* v___y_1487_ = _args[12];
lean_object* v___y_1488_ = _args[13];
lean_object* v___y_1489_ = _args[14];
lean_object* v___y_1490_ = _args[15];
lean_object* v___y_1491_ = _args[16];
lean_object* v___y_1492_ = _args[17];
lean_object* v___y_1493_ = _args[18];
_start:
{
uint8_t v___y_47739__boxed_1494_; lean_object* v_res_1495_; 
v___y_47739__boxed_1494_ = lean_unbox(v___y_1476_);
v_res_1495_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(v_val_1475_, v___y_47739__boxed_1494_, v_as_1477_, v_as_x27_1478_, v_b_1479_, v_a_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v_as_x27_1478_);
lean_dec(v_as_1477_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(lean_object* v_a_1496_, lean_object* v_as_x27_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
if (lean_obj_tag(v_as_x27_1497_) == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_b_1498_);
return v___x_1511_;
}
else
{
lean_object* v_head_1512_; lean_object* v_tail_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v_head_1512_ = lean_ctor_get(v_as_x27_1497_, 0);
v_tail_1513_ = lean_ctor_get(v_as_x27_1497_, 1);
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_expr_eqv(v_head_1512_, v_a_1496_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_inc(v_head_1512_);
v___x_1516_ = l_Lean_mkNot(v_head_1512_);
v___x_1517_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1516_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
lean_inc(v_head_1512_);
v___x_1519_ = l_Lean_Meta_Grind_mkEqFalseProof(v_head_1512_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = l_Lean_Meta_mkOfEqFalse(v_a_1520_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_box(4);
v___x_1525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v_a_1518_);
lean_ctor_set(v___x_1525_, 2, v_a_1522_);
lean_ctor_set(v___x_1525_, 3, v___x_1524_);
v___x_1526_ = lean_st_ref_take(v___y_1499_);
v___x_1527_ = lean_array_push(v___x_1526_, v___x_1525_);
v___x_1528_ = lean_st_ref_put(v___y_1499_, v___x_1527_);
v_as_x27_1497_ = v_tail_1513_;
v_b_1498_ = v___x_1514_;
goto _start;
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec(v_a_1518_);
v_a_1530_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1521_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1521_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_a_1518_);
v_a_1538_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1519_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1519_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
v_a_1546_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1517_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1517_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
v_as_x27_1497_ = v_tail_1513_;
v_b_1498_ = v___x_1514_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg___boxed(lean_object* v_a_1555_, lean_object* v_as_x27_1556_, lean_object* v_b_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_1555_, v_as_x27_1556_, v_b_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v_as_x27_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1577_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_n(v_a_1585_, 2);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = 0;
v___x_1587_ = lean_st_ref_get(v_a_1573_);
v___x_1588_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1587_, v_a_1585_, v___x_1586_);
lean_dec(v___x_1587_);
v___x_1589_ = lean_box(0);
v___x_1590_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_1585_, v___x_1588_, v___x_1589_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
lean_dec(v___x_1588_);
lean_dec(v_a_1585_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v___x_1590_, 0);
lean_dec(v_unused_1598_);
v___x_1592_ = v___x_1590_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v___x_1590_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1589_);
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1589_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
else
{
return v___x_1590_;
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1584_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1584_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse___boxed(lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0(lean_object* v_a_1621_, lean_object* v_as_1622_, lean_object* v_as_x27_1623_, lean_object* v_b_1624_, lean_object* v_a_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_1621_, v_as_x27_1623_, v_b_1624_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___boxed(lean_object** _args){
lean_object* v_a_1640_ = _args[0];
lean_object* v_as_1641_ = _args[1];
lean_object* v_as_x27_1642_ = _args[2];
lean_object* v_b_1643_ = _args[3];
lean_object* v_a_1644_ = _args[4];
lean_object* v___y_1645_ = _args[5];
lean_object* v___y_1646_ = _args[6];
lean_object* v___y_1647_ = _args[7];
lean_object* v___y_1648_ = _args[8];
lean_object* v___y_1649_ = _args[9];
lean_object* v___y_1650_ = _args[10];
lean_object* v___y_1651_ = _args[11];
lean_object* v___y_1652_ = _args[12];
lean_object* v___y_1653_ = _args[13];
lean_object* v___y_1654_ = _args[14];
lean_object* v___y_1655_ = _args[15];
lean_object* v___y_1656_ = _args[16];
lean_object* v___y_1657_ = _args[17];
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0(v_a_1640_, v_as_1641_, v_as_x27_1642_, v_b_1643_, v_a_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v_as_x27_1642_);
lean_dec(v_as_1641_);
lean_dec_ref(v_a_1640_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(lean_object* v_a_1659_, lean_object* v_as_x27_1660_, lean_object* v_b_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
if (lean_obj_tag(v_as_x27_1660_) == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_b_1661_);
return v___x_1674_;
}
else
{
lean_object* v_head_1675_; lean_object* v_tail_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_head_1675_ = lean_ctor_get(v_as_x27_1660_, 0);
v_tail_1676_ = lean_ctor_get(v_as_x27_1660_, 1);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_expr_eqv(v_head_1675_, v_a_1659_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_inc(v_head_1675_);
v___x_1679_ = l_Lean_Meta_Grind_mkEqTrueProof(v_head_1675_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = l_Lean_Meta_mkOfEqTrue(v_a_1680_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_box(4);
lean_inc(v_head_1675_);
v___x_1685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v_head_1675_);
lean_ctor_set(v___x_1685_, 2, v_a_1682_);
lean_ctor_set(v___x_1685_, 3, v___x_1684_);
v___x_1686_ = lean_st_ref_take(v___y_1662_);
v___x_1687_ = lean_array_push(v___x_1686_, v___x_1685_);
v___x_1688_ = lean_st_ref_put(v___y_1662_, v___x_1687_);
v_as_x27_1660_ = v_tail_1676_;
v_b_1661_ = v___x_1677_;
goto _start;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1681_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1681_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1679_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1679_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
v_as_x27_1660_ = v_tail_1676_;
v_b_1661_ = v___x_1677_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg___boxed(lean_object* v_a_1707_, lean_object* v_as_x27_1708_, lean_object* v_b_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1707_, v_as_x27_1708_, v_b_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec(v_as_x27_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1729_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc_n(v_a_1737_, 2);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1738_ = 0;
v___x_1739_ = lean_st_ref_get(v_a_1725_);
v___x_1740_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1739_, v_a_1737_, v___x_1738_);
lean_dec(v___x_1739_);
v___x_1741_ = lean_box(0);
v___x_1742_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1737_, v___x_1740_, v___x_1741_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
lean_dec(v___x_1740_);
lean_dec(v_a_1737_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v___x_1742_, 0);
lean_dec(v_unused_1750_);
v___x_1744_ = v___x_1742_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_dec(v___x_1742_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1741_);
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1741_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
else
{
return v___x_1742_;
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
v_a_1751_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1736_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1736_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue___boxed(lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0(lean_object* v_a_1773_, lean_object* v_as_1774_, lean_object* v_as_x27_1775_, lean_object* v_b_1776_, lean_object* v_a_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1773_, v_as_x27_1775_, v_b_1776_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___boxed(lean_object** _args){
lean_object* v_a_1792_ = _args[0];
lean_object* v_as_1793_ = _args[1];
lean_object* v_as_x27_1794_ = _args[2];
lean_object* v_b_1795_ = _args[3];
lean_object* v_a_1796_ = _args[4];
lean_object* v___y_1797_ = _args[5];
lean_object* v___y_1798_ = _args[6];
lean_object* v___y_1799_ = _args[7];
lean_object* v___y_1800_ = _args[8];
lean_object* v___y_1801_ = _args[9];
lean_object* v___y_1802_ = _args[10];
lean_object* v___y_1803_ = _args[11];
lean_object* v___y_1804_ = _args[12];
lean_object* v___y_1805_ = _args[13];
lean_object* v___y_1806_ = _args[14];
lean_object* v___y_1807_ = _args[15];
lean_object* v___y_1808_ = _args[16];
lean_object* v___y_1809_ = _args[17];
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0(v_a_1792_, v_as_1793_, v_as_x27_1794_, v_b_1795_, v_a_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v_as_x27_1794_);
lean_dec(v_as_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1825_; 
lean_dec_ref_known(v___x_1824_, 1);
v___x_1825_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1826_; 
lean_dec_ref_known(v___x_1825_, 1);
v___x_1826_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v___x_1827_; 
lean_dec_ref_known(v___x_1826_, 1);
v___x_1827_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg(v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
return v___x_1827_;
}
else
{
return v___x_1826_;
}
}
else
{
return v___x_1825_;
}
}
else
{
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go___boxed(lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(lean_object* v_cfg_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0));
v___x_1857_ = lean_st_mk_ref(v___x_1856_);
v___x_1858_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(v_cfg_1844_, v___x_1857_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1866_; 
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v___x_1858_, 0);
lean_dec(v_unused_1867_);
v___x_1860_ = v___x_1858_;
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
else
{
lean_dec(v___x_1858_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = lean_st_ref_get(v___x_1857_);
lean_dec(v___x_1857_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v___x_1857_);
v_a_1868_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1858_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1858_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___boxed(lean_object* v_cfg_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(v_cfg_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_cfg_1876_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordLocalHyp(lean_object* v_fvarId_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1897_; 
lean_inc(v_fvarId_1889_);
v___x_1897_ = l_Lean_FVarId_getUserName___redArg(v_fvarId_1889_, v_a_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
lean_inc(v_fvarId_1889_);
v___x_1899_ = l_Lean_FVarId_getType___redArg(v_fvarId_1889_, v_a_1892_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1901_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_1900_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1912_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1912_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1912_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_inc(v_fvarId_1889_);
v___x_1906_ = l_Lean_mkFVar(v_fvarId_1889_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_fvarId_1889_);
v___x_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1908_, 0, v_a_1898_);
lean_ctor_set(v___x_1908_, 1, v_a_1902_);
lean_ctor_set(v___x_1908_, 2, v___x_1906_);
lean_ctor_set(v___x_1908_, 3, v___x_1907_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1908_);
v___x_1910_ = v___x_1904_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_a_1898_);
lean_dec(v_fvarId_1889_);
v_a_1913_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1901_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1901_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_a_1898_);
lean_dec(v_fvarId_1889_);
v_a_1921_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1899_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1899_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_fvarId_1889_);
v_a_1929_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1897_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1897_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordLocalHyp___boxed(lean_object* v_fvarId_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordLocalHyp(v_fvarId_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
return v_res_1945_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1(lean_object* v_msg_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_6181__overap_1956_; lean_object* v___x_1957_; 
v___x_1955_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0);
v___x_6181__overap_1956_ = lean_panic_fn_borrowed(v___x_1955_, v_msg_1947_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc(v___y_1951_);
lean_inc_ref(v___y_1950_);
lean_inc(v___y_1949_);
lean_inc_ref(v___y_1948_);
v___x_1957_ = lean_apply_7(v___x_6181__overap_1956_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, lean_box(0));
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___boxed(lean_object* v_msg_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1(v_msg_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0(lean_object* v_x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
lean_inc(v___y_1969_);
lean_inc_ref(v___y_1968_);
v___x_1975_ = lean_apply_7(v_x_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, lean_box(0));
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0___boxed(lean_object* v_x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0(v_x_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(lean_object* v_mvarId_1985_, lean_object* v_x_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___f_1994_; lean_object* v___x_1995_; 
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1994_, 0, v_x_1986_);
lean_closure_set(v___f_1994_, 1, v___y_1987_);
lean_closure_set(v___f_1994_, 2, v___y_1988_);
v___x_1995_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1985_, v___f_1994_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1995_) == 0)
{
return v___x_1995_;
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___boxed(lean_object* v_mvarId_2004_, lean_object* v_x_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(v_mvarId_2004_, v_x_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2(lean_object* v_00_u03b1_2014_, lean_object* v_mvarId_2015_, lean_object* v_x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(v_mvarId_2015_, v_x_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___boxed(lean_object* v_00_u03b1_2025_, lean_object* v_mvarId_2026_, lean_object* v_x_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2(v_00_u03b1_2025_, v_mvarId_2026_, v_x_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(lean_object* v_msgData_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v_env_2043_; lean_object* v___x_2044_; lean_object* v_toCold_2045_; lean_object* v_mctx_2046_; lean_object* v_lctx_2047_; lean_object* v_options_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2042_ = lean_st_ref_get(v___y_2040_);
v_env_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc_ref(v_env_2043_);
lean_dec(v___x_2042_);
v___x_2044_ = lean_st_ref_get(v___y_2038_);
v_toCold_2045_ = lean_ctor_get(v___y_2039_, 0);
v_mctx_2046_ = lean_ctor_get(v___x_2044_, 0);
lean_inc_ref(v_mctx_2046_);
lean_dec(v___x_2044_);
v_lctx_2047_ = lean_ctor_get(v___y_2037_, 2);
v_options_2048_ = lean_ctor_get(v_toCold_2045_, 2);
lean_inc_ref(v_options_2048_);
lean_inc_ref(v_lctx_2047_);
v___x_2049_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2049_, 0, v_env_2043_);
lean_ctor_set(v___x_2049_, 1, v_mctx_2046_);
lean_ctor_set(v___x_2049_, 2, v_lctx_2047_);
lean_ctor_set(v___x_2049_, 3, v_options_2048_);
v___x_2050_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v_msgData_2036_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0___boxed(lean_object* v_msgData_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msgData_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(lean_object* v_msg_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_ref_2065_; lean_object* v___x_2066_; lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
v_ref_2065_ = lean_ctor_get(v___y_2062_, 2);
v___x_2066_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_inc(v_ref_2065_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v_ref_2065_);
lean_ctor_set(v___x_2071_, 1, v_a_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 1);
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg___boxed(lean_object* v_msg_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v_msg_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2082_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__0));
v___x_2085_ = l_Lean_stringToMessageData(v___x_2084_);
return v___x_2085_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__4));
v___x_2090_ = lean_unsigned_to_nat(37u);
v___x_2091_ = lean_unsigned_to_nat(200u);
v___x_2092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__3));
v___x_2093_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__2));
v___x_2094_ = l_mkPanicMessageWithDecl(v___x_2093_, v___x_2092_, v___x_2091_, v___x_2090_, v___x_2089_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0(lean_object* v_snd_2095_, lean_object* v_fst_2096_, uint8_t v___x_2097_, lean_object* v_____x_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; 
lean_inc(v_snd_2095_);
v___x_2106_ = l_Lean_MVarId_getType(v_snd_2095_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_n(v_a_2107_, 2);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = l_Lean_Meta_isProp(v_a_2107_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2199_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2199_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2199_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
uint8_t v___x_2113_; 
v___x_2113_ = lean_unbox(v_a_2109_);
lean_dec(v_a_2109_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_del_object(v___x_2111_);
lean_dec(v_a_2107_);
lean_dec_ref(v_____x_2098_);
v___x_2114_ = l_Lean_MVarId_exfalso(v_snd_2095_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l_Lean_Meta_Sym_preprocessMVar(v_a_2115_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2125_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_fst_2096_);
lean_ctor_set(v___x_2121_, 1, v_a_2117_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2121_);
v___x_2123_ = v___x_2119_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_fst_2096_);
v_a_2126_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2116_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2116_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_fst_2096_);
v_a_2134_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2114_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2114_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
uint8_t v___x_2142_; 
v___x_2142_ = l_Lean_Expr_isFalse(v_a_2107_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_del_object(v___x_2111_);
lean_dec_ref(v_____x_2098_);
v___x_2143_ = l_Lean_MVarId_byContra_x3f(v_snd_2095_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
if (lean_obj_tag(v_a_2144_) == 1)
{
lean_object* v_val_2145_; lean_object* v___x_2146_; 
v_val_2145_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_a_2144_, 1);
v___x_2146_ = l_Lean_Meta_Sym_preprocessMVar(v_val_2145_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = l_Lean_Meta_Sym_introN(v_a_2147_, v___x_2148_, v___x_2097_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2169_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2169_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2169_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
if (lean_obj_tag(v_a_2150_) == 1)
{
lean_object* v_newDecls_2154_; lean_object* v_mvarId_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2166_; 
v_newDecls_2154_ = lean_ctor_get(v_a_2150_, 0);
v_mvarId_2155_ = lean_ctor_get(v_a_2150_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_a_2150_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2157_ = v_a_2150_;
v_isShared_2158_ = v_isSharedCheck_2166_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_mvarId_2155_);
lean_inc(v_newDecls_2154_);
lean_dec(v_a_2150_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2166_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = l_Array_append___redArg(v_fst_2096_, v_newDecls_2154_);
lean_dec_ref(v_newDecls_2154_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2159_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_mvarId_2155_);
v___x_2161_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2163_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2161_);
v___x_2163_ = v___x_2152_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_del_object(v___x_2152_);
lean_dec(v_a_2150_);
lean_dec_ref(v_fst_2096_);
v___x_2167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1);
v___x_2168_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v___x_2167_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v_fst_2096_);
v_a_2170_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2149_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2149_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v_fst_2096_);
v_a_2178_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2146_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2146_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_dec(v_a_2144_);
lean_dec_ref(v_fst_2096_);
v___x_2186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5);
v___x_2187_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1(v___x_2186_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
return v___x_2187_;
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v_fst_2096_);
v_a_2188_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2143_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2143_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v___x_2197_; 
lean_dec_ref(v_fst_2096_);
lean_dec(v_snd_2095_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v_____x_2098_);
v___x_2197_ = v___x_2111_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_____x_2098_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_a_2107_);
lean_dec_ref(v_____x_2098_);
lean_dec_ref(v_fst_2096_);
lean_dec(v_snd_2095_);
v_a_2200_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2108_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2108_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v_____x_2098_);
lean_dec_ref(v_fst_2096_);
lean_dec(v_snd_2095_);
v_a_2208_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2106_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2106_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___boxed(lean_object* v_snd_2216_, lean_object* v_fst_2217_, lean_object* v___x_2218_, lean_object* v_____x_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v___x_7876__boxed_2227_; lean_object* v_res_2228_; 
v___x_7876__boxed_2227_ = lean_unbox(v___x_2218_);
v_res_2228_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0(v_snd_2216_, v_fst_2217_, v___x_7876__boxed_2227_, v_____x_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(lean_object* v_goal_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2239_; uint8_t v___x_2240_; lean_object* v_____x_2242_; lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___x_2254_; 
v___x_2239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0));
v___x_2240_ = 1;
lean_inc(v_goal_2231_);
v___x_2254_ = l_Lean_Meta_Sym_intros(v_goal_2231_, v___x_2239_, v___x_2240_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
if (lean_obj_tag(v_a_2255_) == 0)
{
lean_object* v___x_2256_; 
lean_inc(v_goal_2231_);
v___x_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2239_);
lean_ctor_set(v___x_2256_, 1, v_goal_2231_);
v_____x_2242_ = v___x_2256_;
v_fst_2243_ = v___x_2239_;
v_snd_2244_ = v_goal_2231_;
v___y_2245_ = v_a_2232_;
v___y_2246_ = v_a_2233_;
v___y_2247_ = v_a_2234_;
v___y_2248_ = v_a_2235_;
v___y_2249_ = v_a_2236_;
v___y_2250_ = v_a_2237_;
goto v___jp_2241_;
}
else
{
lean_object* v_newDecls_2257_; lean_object* v_mvarId_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_goal_2231_);
v_newDecls_2257_ = lean_ctor_get(v_a_2255_, 0);
v_mvarId_2258_ = lean_ctor_get(v_a_2255_, 1);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_a_2255_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v_a_2255_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_mvarId_2258_);
lean_inc(v_newDecls_2257_);
lean_dec(v_a_2255_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
lean_inc(v_mvarId_2258_);
lean_inc_ref(v_newDecls_2257_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set_tag(v___x_2260_, 0);
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_newDecls_2257_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_mvarId_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
v_____x_2242_ = v___x_2263_;
v_fst_2243_ = v_newDecls_2257_;
v_snd_2244_ = v_mvarId_2258_;
v___y_2245_ = v_a_2232_;
v___y_2246_ = v_a_2233_;
v___y_2247_ = v_a_2234_;
v___y_2248_ = v_a_2235_;
v___y_2249_ = v_a_2236_;
v___y_2250_ = v_a_2237_;
goto v___jp_2241_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_goal_2231_);
v_a_2266_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2254_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2254_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
v___jp_2241_:
{
lean_object* v___x_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_box(v___x_2240_);
lean_inc(v_snd_2244_);
v___f_2252_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2252_, 0, v_snd_2244_);
lean_closure_set(v___f_2252_, 1, v_fst_2243_);
lean_closure_set(v___f_2252_, 2, v___x_2251_);
lean_closure_set(v___f_2252_, 3, v_____x_2242_);
v___x_2253_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(v_snd_2244_, v___f_2252_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___boxed(lean_object* v_goal_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_goal_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0(lean_object* v_00_u03b1_2283_, lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v_msg_2284_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0(v_00_u03b1_2293_, v_msg_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(lean_object* v_goal_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_toGoalState_2311_; lean_object* v_mvarId_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2345_; 
v_toGoalState_2311_ = lean_ctor_get(v_goal_2303_, 0);
v_mvarId_2312_ = lean_ctor_get(v_goal_2303_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_goal_2303_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2314_ = v_goal_2303_;
v_isShared_2315_ = v_isSharedCheck_2345_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_mvarId_2312_);
lean_inc(v_toGoalState_2311_);
lean_dec(v_goal_2303_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2345_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; 
v___x_2316_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_mvarId_2312_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2336_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2336_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2336_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_fst_2321_; lean_object* v_snd_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2335_; 
v_fst_2321_ = lean_ctor_get(v_a_2317_, 0);
v_snd_2322_ = lean_ctor_get(v_a_2317_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_a_2317_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2324_ = v_a_2317_;
v_isShared_2325_ = v_isSharedCheck_2335_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snd_2322_);
lean_inc(v_fst_2321_);
lean_dec(v_a_2317_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2335_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v_snd_2322_);
v___x_2327_ = v___x_2314_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_toGoalState_2311_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_snd_2322_);
v___x_2327_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v___x_2327_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_fst_2321_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2329_);
v___x_2331_ = v___x_2319_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_del_object(v___x_2314_);
lean_dec_ref(v_toGoalState_2311_);
v_a_2337_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2316_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2316_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg___boxed(lean_object* v_goal_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget(lean_object* v_goal_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2355_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___boxed(lean_object* v_goal_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget(v_goal_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0(lean_object* v_x_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
v___x_2390_ = lean_apply_10(v_x_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, lean_box(0));
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0___boxed(lean_object* v_x_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0(v_x_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(lean_object* v_mvarId_2403_, lean_object* v_x_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___f_2415_; lean_object* v___x_2416_; 
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
lean_inc(v___y_2407_);
lean_inc_ref(v___y_2406_);
lean_inc(v___y_2405_);
v___f_2415_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2415_, 0, v_x_2404_);
lean_closure_set(v___f_2415_, 1, v___y_2405_);
lean_closure_set(v___f_2415_, 2, v___y_2406_);
lean_closure_set(v___f_2415_, 3, v___y_2407_);
lean_closure_set(v___f_2415_, 4, v___y_2408_);
lean_closure_set(v___f_2415_, 5, v___y_2409_);
v___x_2416_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2403_, v___f_2415_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2416_) == 0)
{
return v___x_2416_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___boxed(lean_object* v_mvarId_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2425_, v_x_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1(lean_object* v_00_u03b1_2438_, lean_object* v_mvarId_2439_, lean_object* v_x_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2439_, v_x_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_mvarId_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1(v_00_u03b1_2452_, v_mvarId_2453_, v_x_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0(lean_object* v_x_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
lean_inc(v___y_2473_);
lean_inc_ref(v___y_2472_);
lean_inc(v___y_2471_);
lean_inc_ref(v___y_2470_);
lean_inc(v___y_2469_);
lean_inc(v___y_2468_);
lean_inc_ref(v___y_2467_);
v___x_2479_ = lean_apply_12(v_x_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, lean_box(0));
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0___boxed(lean_object* v_x_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0(v_x_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(lean_object* v_mvarId_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___f_2508_; lean_object* v___x_2509_; 
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
lean_inc(v___y_2500_);
lean_inc_ref(v___y_2499_);
lean_inc(v___y_2498_);
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
v___f_2508_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2508_, 0, v_x_2495_);
lean_closure_set(v___f_2508_, 1, v___y_2496_);
lean_closure_set(v___f_2508_, 2, v___y_2497_);
lean_closure_set(v___f_2508_, 3, v___y_2498_);
lean_closure_set(v___f_2508_, 4, v___y_2499_);
lean_closure_set(v___f_2508_, 5, v___y_2500_);
lean_closure_set(v___f_2508_, 6, v___y_2501_);
lean_closure_set(v___f_2508_, 7, v___y_2502_);
v___x_2509_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2494_, v___f_2508_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2509_) == 0)
{
return v___x_2509_;
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___boxed(lean_object* v_mvarId_2518_, lean_object* v_x_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_mvarId_2518_, v_x_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3(lean_object* v_00_u03b1_2533_, lean_object* v_mvarId_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_mvarId_2534_, v_x_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___boxed(lean_object* v_00_u03b1_2549_, lean_object* v_mvarId_2550_, lean_object* v_x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3(v_00_u03b1_2549_, v_mvarId_2550_, v_x_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(lean_object* v_as_2565_, size_t v_i_2566_, size_t v_stop_2567_, lean_object* v_b_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_a_2580_; uint8_t v___x_2584_; 
v___x_2584_ = lean_usize_dec_eq(v_i_2566_, v_stop_2567_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_array_uget_borrowed(v_as_2565_, v_i_2566_);
lean_inc(v___x_2585_);
v___x_2586_ = l_Lean_FVarId_getType___redArg(v___x_2585_, v___y_2574_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = l_Lean_Meta_isProp(v_a_2587_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; uint8_t v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = lean_unbox(v_a_2589_);
lean_dec(v_a_2589_);
if (v___x_2590_ == 0)
{
v_a_2580_ = v_b_2568_;
goto v___jp_2579_;
}
else
{
lean_object* v___x_2591_; 
lean_inc(v___x_2585_);
v___x_2591_ = l_Lean_FVarId_getUserName___redArg(v___x_2585_, v___y_2574_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
lean_inc(v___x_2585_);
v___x_2593_ = l_Lean_FVarId_getType___redArg(v___x_2585_, v___y_2574_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_2594_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
lean_inc_n(v___x_2585_, 2);
v___x_2597_ = l_Lean_mkFVar(v___x_2585_);
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2585_);
v___x_2599_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2599_, 0, v_a_2592_);
lean_ctor_set(v___x_2599_, 1, v_a_2596_);
lean_ctor_set(v___x_2599_, 2, v___x_2597_);
lean_ctor_set(v___x_2599_, 3, v___x_2598_);
v___x_2600_ = lean_array_push(v_b_2568_, v___x_2599_);
v_a_2580_ = v___x_2600_;
goto v___jp_2579_;
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec(v_a_2592_);
lean_dec_ref(v_b_2568_);
v_a_2601_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2595_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2595_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_a_2592_);
lean_dec_ref(v_b_2568_);
v_a_2609_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2593_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2593_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_b_2568_);
v_a_2617_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2591_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2591_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_b_2568_);
v_a_2625_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2588_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2588_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v_b_2568_);
v_a_2633_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2586_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2586_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v___x_2641_; 
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_b_2568_);
return v___x_2641_;
}
v___jp_2579_:
{
size_t v___x_2581_; size_t v___x_2582_; 
v___x_2581_ = ((size_t)1ULL);
v___x_2582_ = lean_usize_add(v_i_2566_, v___x_2581_);
v_i_2566_ = v___x_2582_;
v_b_2568_ = v_a_2580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg___boxed(lean_object* v_as_2642_, lean_object* v_i_2643_, lean_object* v_stop_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
size_t v_i_boxed_2656_; size_t v_stop_boxed_2657_; lean_object* v_res_2658_; 
v_i_boxed_2656_ = lean_unbox_usize(v_i_2643_);
lean_dec(v_i_2643_);
v_stop_boxed_2657_ = lean_unbox_usize(v_stop_2644_);
lean_dec(v_stop_2644_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2642_, v_i_boxed_2656_, v_stop_boxed_2657_, v_b_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v_as_2642_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(lean_object* v_as_2659_, lean_object* v_start_2660_, lean_object* v_stop_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0));
v___x_2674_ = lean_nat_dec_lt(v_start_2660_, v_stop_2661_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = lean_array_get_size(v_as_2659_);
v___x_2677_ = lean_nat_dec_le(v_stop_2661_, v___x_2676_);
if (v___x_2677_ == 0)
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_nat_dec_lt(v_start_2660_, v___x_2676_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2673_);
return v___x_2679_;
}
else
{
size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_usize_of_nat(v_start_2660_);
v___x_2681_ = lean_usize_of_nat(v___x_2676_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2659_, v___x_2680_, v___x_2681_, v___x_2673_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2682_;
}
}
else
{
size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_usize_of_nat(v_start_2660_);
v___x_2684_ = lean_usize_of_nat(v_stop_2661_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2659_, v___x_2683_, v___x_2684_, v___x_2673_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___boxed(lean_object* v_as_2686_, lean_object* v_start_2687_, lean_object* v_stop_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(v_as_2686_, v_start_2687_, v_stop_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec(v_stop_2688_);
lean_dec(v_start_2687_);
lean_dec_ref(v_as_2686_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(lean_object* v_snd_2701_, lean_object* v_config_2702_, lean_object* v_fst_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v_a_2716_; lean_object* v___y_2721_; lean_object* v___x_2731_; 
v___x_2714_ = lean_st_mk_ref(v_snd_2701_);
v___x_2731_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(v_config_2702_, v___x_2714_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = lean_unsigned_to_nat(0u);
v___x_2734_ = lean_array_get_size(v_fst_2703_);
v___x_2735_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(v_fst_2703_, v___x_2733_, v___x_2734_, v___x_2714_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = l_Array_append___redArg(v_a_2732_, v_a_2736_);
lean_dec(v_a_2736_);
v_a_2716_ = v___x_2737_;
goto v___jp_2715_;
}
else
{
lean_dec(v_a_2732_);
v___y_2721_ = v___x_2735_;
goto v___jp_2720_;
}
}
else
{
v___y_2721_ = v___x_2731_;
goto v___jp_2720_;
}
v___jp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_st_ref_get(v___x_2714_);
lean_dec(v___x_2714_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_a_2716_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
v___jp_2720_:
{
if (lean_obj_tag(v___y_2721_) == 0)
{
lean_object* v_a_2722_; 
v_a_2722_ = lean_ctor_get(v___y_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___y_2721_, 1);
v_a_2716_ = v_a_2722_;
goto v___jp_2715_;
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v___x_2714_);
v_a_2723_ = lean_ctor_get(v___y_2721_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___y_2721_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___y_2721_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___y_2721_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed(lean_object* v_snd_2738_, lean_object* v_config_2739_, lean_object* v_fst_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(v_snd_2738_, v_config_2739_, v_fst_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v_fst_2740_);
lean_dec_ref(v_config_2739_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(size_t v_sz_2752_, size_t v_i_2753_, lean_object* v_bs_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
uint8_t v___x_2762_; 
v___x_2762_ = lean_usize_dec_lt(v_i_2753_, v_sz_2752_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_bs_2754_);
return v___x_2763_;
}
else
{
lean_object* v_v_2764_; lean_object* v___x_2765_; lean_object* v_bs_x27_2766_; lean_object* v___x_2767_; 
v_v_2764_ = lean_array_uget(v_bs_2754_, v_i_2753_);
v___x_2765_ = lean_unsigned_to_nat(0u);
v_bs_x27_2766_ = lean_array_uset(v_bs_2754_, v_i_2753_, v___x_2765_);
lean_inc(v_v_2764_);
v___x_2767_ = l_Lean_FVarId_getUserName___redArg(v_v_2764_, v___y_2757_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
lean_inc(v_v_2764_);
v___x_2769_ = l_Lean_FVarId_getType___redArg(v_v_2764_, v___y_2757_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2771_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2771_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_2770_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; size_t v___x_2776_; size_t v___x_2777_; lean_object* v___x_2778_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
lean_inc(v_v_2764_);
v___x_2773_ = l_Lean_mkFVar(v_v_2764_);
v___x_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2774_, 0, v_v_2764_);
v___x_2775_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2775_, 0, v_a_2768_);
lean_ctor_set(v___x_2775_, 1, v_a_2772_);
lean_ctor_set(v___x_2775_, 2, v___x_2773_);
lean_ctor_set(v___x_2775_, 3, v___x_2774_);
v___x_2776_ = ((size_t)1ULL);
v___x_2777_ = lean_usize_add(v_i_2753_, v___x_2776_);
v___x_2778_ = lean_array_uset(v_bs_x27_2766_, v_i_2753_, v___x_2775_);
v_i_2753_ = v___x_2777_;
v_bs_2754_ = v___x_2778_;
goto _start;
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2768_);
lean_dec_ref(v_bs_x27_2766_);
lean_dec(v_v_2764_);
v_a_2780_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2771_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2771_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2768_);
lean_dec_ref(v_bs_x27_2766_);
lean_dec(v_v_2764_);
v_a_2788_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2769_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2769_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_bs_x27_2766_);
lean_dec(v_v_2764_);
v_a_2796_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2767_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2767_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg___boxed(lean_object* v_sz_2804_, lean_object* v_i_2805_, lean_object* v_bs_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
size_t v_sz_boxed_2814_; size_t v_i_boxed_2815_; lean_object* v_res_2816_; 
v_sz_boxed_2814_ = lean_unbox_usize(v_sz_2804_);
lean_dec(v_sz_2804_);
v_i_boxed_2815_ = lean_unbox_usize(v_i_2805_);
lean_dec(v_i_2805_);
v_res_2816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_boxed_2814_, v_i_boxed_2815_, v_bs_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_Meta_getPropHyps(v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; size_t v_sz_2831_; size_t v___x_2832_; lean_object* v___x_2833_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v_sz_2831_ = lean_array_size(v_a_2830_);
v___x_2832_ = ((size_t)0ULL);
v___x_2833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_2831_, v___x_2832_, v_a_2830_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2842_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2842_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_a_2834_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2838_);
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2833_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2833_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
v_a_2851_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2829_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2829_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed(lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_fst_2886_; lean_object* v_snd_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v_target_2943_; 
v___f_2941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0));
v___x_2942_ = lean_st_ref_get(v_a_2874_);
v_target_2943_ = lean_ctor_get(v___x_2942_, 2);
lean_inc_ref(v_target_2943_);
lean_dec(v___x_2942_);
if (lean_obj_tag(v_target_2943_) == 0)
{
lean_object* v_mvar_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2987_; 
v_mvar_2944_ = lean_ctor_get(v_target_2943_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_target_2943_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2946_ = v_target_2943_;
v_isShared_2947_ = v_isSharedCheck_2987_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_mvar_2944_);
lean_dec(v_target_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2987_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; 
v___x_2948_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_mvar_2944_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v_snd_2950_; lean_object* v___x_2951_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v_snd_2950_ = lean_ctor_get(v_a_2949_, 1);
lean_inc(v_snd_2950_);
lean_dec(v_a_2949_);
v___x_2951_ = l_Lean_Meta_Sym_preprocessMVar(v_snd_2950_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc_n(v_a_2952_, 2);
lean_dec_ref_known(v___x_2951_, 1);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v_a_2952_);
v___x_2954_ = v___x_2946_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2952_);
v___x_2954_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v_caches_2956_; lean_object* v_typeAnalysis_2957_; lean_object* v_hypotheses_2958_; uint8_t v_didChange_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2968_; 
v___x_2955_ = lean_st_ref_take(v_a_2874_);
v_caches_2956_ = lean_ctor_get(v___x_2955_, 0);
v_typeAnalysis_2957_ = lean_ctor_get(v___x_2955_, 1);
v_hypotheses_2958_ = lean_ctor_get(v___x_2955_, 3);
v_didChange_2959_ = lean_ctor_get_uint8(v___x_2955_, sizeof(void*)*4);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v___x_2955_, 2);
lean_dec(v_unused_2969_);
v___x_2961_ = v___x_2955_;
v_isShared_2962_ = v_isSharedCheck_2968_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_hypotheses_2958_);
lean_inc(v_typeAnalysis_2957_);
lean_inc(v_caches_2956_);
lean_dec(v___x_2955_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2968_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 2, v___x_2954_);
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_caches_2956_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_typeAnalysis_2957_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_hypotheses_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_2967_, sizeof(void*)*4, v_didChange_2959_);
v___x_2964_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_st_ref_put(v_a_2874_, v___x_2964_);
v___x_2966_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_a_2952_, v___f_2941_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_del_object(v___x_2946_);
v_a_2971_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2951_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2951_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_del_object(v___x_2946_);
v_a_2979_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2948_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2948_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
else
{
lean_object* v_goal_2988_; lean_object* v_mode_2989_; uint8_t v___x_2990_; 
v_goal_2988_ = lean_ctor_get(v_target_2943_, 0);
lean_inc_ref(v_goal_2988_);
lean_dec_ref_known(v_target_2943_, 1);
v_mode_2989_ = lean_ctor_get(v_a_2873_, 1);
v___x_2990_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
v___x_2991_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2988_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v_fst_2993_; lean_object* v_snd_2994_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v_fst_2993_ = lean_ctor_get(v_a_2992_, 0);
lean_inc(v_fst_2993_);
v_snd_2994_ = lean_ctor_get(v_a_2992_, 1);
lean_inc(v_snd_2994_);
lean_dec(v_a_2992_);
v_fst_2886_ = v_fst_2993_;
v_snd_2887_ = v_snd_2994_;
v___y_2888_ = v_a_2873_;
v___y_2889_ = v_a_2874_;
v___y_2890_ = v_a_2875_;
v___y_2891_ = v_a_2876_;
v___y_2892_ = v_a_2877_;
v___y_2893_ = v_a_2878_;
v___y_2894_ = v_a_2879_;
v___y_2895_ = v_a_2880_;
v___y_2896_ = v_a_2881_;
v___y_2897_ = v_a_2882_;
v___y_2898_ = v_a_2883_;
goto v___jp_2885_;
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
v_a_2995_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2991_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2991_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v___x_3003_; 
v___x_3003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0));
v_fst_2886_ = v___x_3003_;
v_snd_2887_ = v_goal_2988_;
v___y_2888_ = v_a_2873_;
v___y_2889_ = v_a_2874_;
v___y_2890_ = v_a_2875_;
v___y_2891_ = v_a_2876_;
v___y_2892_ = v_a_2877_;
v___y_2893_ = v_a_2878_;
v___y_2894_ = v_a_2879_;
v___y_2895_ = v_a_2880_;
v___y_2896_ = v_a_2881_;
v___y_2897_ = v_a_2882_;
v___y_2898_ = v_a_2883_;
goto v___jp_2885_;
}
}
v___jp_2885_:
{
lean_object* v_toGoalState_2899_; uint8_t v_inconsistent_2900_; 
v_toGoalState_2899_ = lean_ctor_get(v_snd_2887_, 0);
v_inconsistent_2900_ = lean_ctor_get_uint8(v_toGoalState_2899_, sizeof(void*)*17);
if (v_inconsistent_2900_ == 0)
{
lean_object* v_mvarId_2901_; lean_object* v_config_2902_; lean_object* v___f_2903_; lean_object* v___x_2904_; 
v_mvarId_2901_ = lean_ctor_get(v_snd_2887_, 1);
lean_inc(v_mvarId_2901_);
v_config_2902_ = lean_ctor_get(v___y_2888_, 0);
lean_inc_ref(v_config_2902_);
v___f_2903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2903_, 0, v_snd_2887_);
lean_closure_set(v___f_2903_, 1, v_config_2902_);
lean_closure_set(v___f_2903_, 2, v_fst_2886_);
v___x_2904_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2901_, v___f_2903_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2930_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2930_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2930_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v_fst_2909_; lean_object* v_snd_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v_caches_2913_; lean_object* v_typeAnalysis_2914_; lean_object* v_hypotheses_2915_; uint8_t v_didChange_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2928_; 
v_fst_2909_ = lean_ctor_get(v_a_2905_, 0);
lean_inc(v_fst_2909_);
v_snd_2910_ = lean_ctor_get(v_a_2905_, 1);
lean_inc(v_snd_2910_);
lean_dec(v_a_2905_);
v___x_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2911_, 0, v_snd_2910_);
v___x_2912_ = lean_st_ref_take(v___y_2889_);
v_caches_2913_ = lean_ctor_get(v___x_2912_, 0);
v_typeAnalysis_2914_ = lean_ctor_get(v___x_2912_, 1);
v_hypotheses_2915_ = lean_ctor_get(v___x_2912_, 3);
v_didChange_2916_ = lean_ctor_get_uint8(v___x_2912_, sizeof(void*)*4);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2928_ == 0)
{
lean_object* v_unused_2929_; 
v_unused_2929_ = lean_ctor_get(v___x_2912_, 2);
lean_dec(v_unused_2929_);
v___x_2918_ = v___x_2912_;
v_isShared_2919_ = v_isSharedCheck_2928_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_hypotheses_2915_);
lean_inc(v_typeAnalysis_2914_);
lean_inc(v_caches_2913_);
lean_dec(v___x_2912_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2928_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 2, v___x_2911_);
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_caches_2913_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_typeAnalysis_2914_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_hypotheses_2915_);
lean_ctor_set_uint8(v_reuseFailAlloc_2927_, sizeof(void*)*4, v_didChange_2916_);
v___x_2921_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2922_ = lean_st_ref_put(v___y_2889_, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_fst_2909_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2923_);
v___x_2925_ = v___x_2907_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2923_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
v_a_2931_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2904_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2904_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
lean_dec_ref(v_snd_2887_);
lean_dec_ref(v_fst_2886_);
v___x_2939_ = lean_box(0);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___boxed(lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2(size_t v_sz_3017_, size_t v_i_3018_, lean_object* v_bs_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_3017_, v_i_3018_, v_bs_3019_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___boxed(lean_object* v_sz_3033_, lean_object* v_i_3034_, lean_object* v_bs_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
size_t v_sz_boxed_3048_; size_t v_i_boxed_3049_; lean_object* v_res_3050_; 
v_sz_boxed_3048_ = lean_unbox_usize(v_sz_3033_);
lean_dec(v_sz_3033_);
v_i_boxed_3049_ = lean_unbox_usize(v_i_3034_);
lean_dec(v_i_3034_);
v_res_3050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2(v_sz_boxed_3048_, v_i_boxed_3049_, v_bs_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(lean_object* v_as_3051_, size_t v_i_3052_, size_t v_stop_3053_, lean_object* v_b_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_3051_, v_i_3052_, v_stop_3053_, v_b_3054_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___boxed(lean_object* v_as_3067_, lean_object* v_i_3068_, lean_object* v_stop_3069_, lean_object* v_b_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
size_t v_i_boxed_3082_; size_t v_stop_boxed_3083_; lean_object* v_res_3084_; 
v_i_boxed_3082_ = lean_unbox_usize(v_i_3068_);
lean_dec(v_i_3068_);
v_stop_boxed_3083_ = lean_unbox_usize(v_stop_3069_);
lean_dec(v_stop_3069_);
v_res_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(v_as_3067_, v_i_boxed_3082_, v_stop_boxed_3083_, v_b_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v_as_3067_);
return v_res_3084_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = lean_unsigned_to_nat(32u);
v___x_3086_ = lean_mk_empty_array_with_capacity(v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3088_ = ((size_t)5ULL);
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = lean_unsigned_to_nat(32u);
v___x_3091_ = lean_mk_empty_array_with_capacity(v___x_3090_);
v___x_3092_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0);
v___x_3093_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
lean_ctor_set(v___x_3093_, 1, v___x_3091_);
lean_ctor_set(v___x_3093_, 2, v___x_3089_);
lean_ctor_set(v___x_3093_, 3, v___x_3089_);
lean_ctor_set_usize(v___x_3093_, 4, v___x_3088_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v_traceState_3097_; lean_object* v_traces_3098_; lean_object* v___x_3099_; lean_object* v_traceState_3100_; lean_object* v_env_3101_; lean_object* v_nextMacroScope_3102_; lean_object* v_ngen_3103_; lean_object* v_auxDeclNGen_3104_; lean_object* v_cache_3105_; lean_object* v_messages_3106_; lean_object* v_infoState_3107_; lean_object* v_snapshotTasks_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3127_; 
v___x_3096_ = lean_st_ref_get(v___y_3094_);
v_traceState_3097_ = lean_ctor_get(v___x_3096_, 4);
lean_inc_ref(v_traceState_3097_);
lean_dec(v___x_3096_);
v_traces_3098_ = lean_ctor_get(v_traceState_3097_, 0);
lean_inc_ref(v_traces_3098_);
lean_dec_ref(v_traceState_3097_);
v___x_3099_ = lean_st_ref_take(v___y_3094_);
v_traceState_3100_ = lean_ctor_get(v___x_3099_, 4);
v_env_3101_ = lean_ctor_get(v___x_3099_, 0);
v_nextMacroScope_3102_ = lean_ctor_get(v___x_3099_, 1);
v_ngen_3103_ = lean_ctor_get(v___x_3099_, 2);
v_auxDeclNGen_3104_ = lean_ctor_get(v___x_3099_, 3);
v_cache_3105_ = lean_ctor_get(v___x_3099_, 5);
v_messages_3106_ = lean_ctor_get(v___x_3099_, 6);
v_infoState_3107_ = lean_ctor_get(v___x_3099_, 7);
v_snapshotTasks_3108_ = lean_ctor_get(v___x_3099_, 8);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3110_ = v___x_3099_;
v_isShared_3111_ = v_isSharedCheck_3127_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_snapshotTasks_3108_);
lean_inc(v_infoState_3107_);
lean_inc(v_messages_3106_);
lean_inc(v_cache_3105_);
lean_inc(v_traceState_3100_);
lean_inc(v_auxDeclNGen_3104_);
lean_inc(v_ngen_3103_);
lean_inc(v_nextMacroScope_3102_);
lean_inc(v_env_3101_);
lean_dec(v___x_3099_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3127_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
uint64_t v_tid_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3125_; 
v_tid_3112_ = lean_ctor_get_uint64(v_traceState_3100_, sizeof(void*)*1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_traceState_3100_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_traceState_3100_, 0);
lean_dec(v_unused_3126_);
v___x_3114_ = v_traceState_3100_;
v_isShared_3115_ = v_isSharedCheck_3125_;
goto v_resetjp_3113_;
}
else
{
lean_dec(v_traceState_3100_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3125_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3116_);
lean_ctor_set_uint64(v_reuseFailAlloc_3124_, sizeof(void*)*1, v_tid_3112_);
v___x_3118_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3120_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 4, v___x_3118_);
v___x_3120_ = v___x_3110_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_env_3101_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_nextMacroScope_3102_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_ngen_3103_);
lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_auxDeclNGen_3104_);
lean_ctor_set(v_reuseFailAlloc_3123_, 4, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3123_, 5, v_cache_3105_);
lean_ctor_set(v_reuseFailAlloc_3123_, 6, v_messages_3106_);
lean_ctor_set(v_reuseFailAlloc_3123_, 7, v_infoState_3107_);
lean_ctor_set(v_reuseFailAlloc_3123_, 8, v_snapshotTasks_3108_);
v___x_3120_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_st_ref_put(v___y_3094_, v___x_3120_);
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_traces_3098_);
return v___x_3122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___boxed(lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_3128_);
lean_dec(v___y_3128_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___boxed(lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v_res_3156_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(lean_object* v_opts_3157_, lean_object* v_opt_3158_){
_start:
{
lean_object* v_name_3159_; lean_object* v_defValue_3160_; lean_object* v_map_3161_; lean_object* v___x_3162_; 
v_name_3159_ = lean_ctor_get(v_opt_3158_, 0);
v_defValue_3160_ = lean_ctor_get(v_opt_3158_, 1);
v_map_3161_ = lean_ctor_get(v_opts_3157_, 0);
v___x_3162_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3161_, v_name_3159_);
if (lean_obj_tag(v___x_3162_) == 0)
{
uint8_t v___x_3163_; 
v___x_3163_ = lean_unbox(v_defValue_3160_);
return v___x_3163_;
}
else
{
lean_object* v_val_3164_; 
v_val_3164_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_val_3164_);
lean_dec_ref_known(v___x_3162_, 1);
if (lean_obj_tag(v_val_3164_) == 1)
{
uint8_t v_v_3165_; 
v_v_3165_ = lean_ctor_get_uint8(v_val_3164_, 0);
lean_dec_ref_known(v_val_3164_, 0);
return v_v_3165_;
}
else
{
uint8_t v___x_3166_; 
lean_dec(v_val_3164_);
v___x_3166_ = lean_unbox(v_defValue_3160_);
return v___x_3166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3___boxed(lean_object* v_opts_3167_, lean_object* v_opt_3168_){
_start:
{
uint8_t v_res_3169_; lean_object* v_r_3170_; 
v_res_3169_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3167_, v_opt_3168_);
lean_dec_ref(v_opt_3168_);
lean_dec_ref(v_opts_3167_);
v_r_3170_ = lean_box(v_res_3169_);
return v_r_3170_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0));
v___x_3173_ = l_Lean_stringToMessageData(v___x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(lean_object* v_x_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1);
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___boxed(lean_object* v_x_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(v_x_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec_ref(v_x_3189_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(lean_object* v_opts_3203_, lean_object* v_opt_3204_){
_start:
{
lean_object* v_name_3205_; lean_object* v_defValue_3206_; lean_object* v_map_3207_; lean_object* v___x_3208_; 
v_name_3205_ = lean_ctor_get(v_opt_3204_, 0);
v_defValue_3206_ = lean_ctor_get(v_opt_3204_, 1);
v_map_3207_ = lean_ctor_get(v_opts_3203_, 0);
v___x_3208_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3207_, v_name_3205_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_inc(v_defValue_3206_);
return v_defValue_3206_;
}
else
{
lean_object* v_val_3209_; 
v_val_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_val_3209_);
lean_dec_ref_known(v___x_3208_, 1);
if (lean_obj_tag(v_val_3209_) == 3)
{
lean_object* v_v_3210_; 
v_v_3210_ = lean_ctor_get(v_val_3209_, 0);
lean_inc(v_v_3210_);
lean_dec_ref_known(v_val_3209_, 1);
return v_v_3210_;
}
else
{
lean_dec(v_val_3209_);
lean_inc(v_defValue_3206_);
return v_defValue_3206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8___boxed(lean_object* v_opts_3211_, lean_object* v_opt_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3211_, v_opt_3212_);
lean_dec_ref(v_opt_3212_);
lean_dec_ref(v_opts_3211_);
return v_res_3213_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(lean_object* v_e_3214_){
_start:
{
if (lean_obj_tag(v_e_3214_) == 0)
{
uint8_t v___x_3215_; 
v___x_3215_ = 2;
return v___x_3215_;
}
else
{
uint8_t v___x_3216_; 
v___x_3216_ = 0;
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___boxed(lean_object* v_e_3217_){
_start:
{
uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_res_3218_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(v_e_3217_);
lean_dec_ref(v_e_3217_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(size_t v_sz_3220_, size_t v_i_3221_, lean_object* v_bs_3222_){
_start:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_usize_dec_lt(v_i_3221_, v_sz_3220_);
if (v___x_3223_ == 0)
{
return v_bs_3222_;
}
else
{
lean_object* v_v_3224_; lean_object* v_msg_3225_; lean_object* v___x_3226_; lean_object* v_bs_x27_3227_; size_t v___x_3228_; size_t v___x_3229_; lean_object* v___x_3230_; 
v_v_3224_ = lean_array_uget_borrowed(v_bs_3222_, v_i_3221_);
v_msg_3225_ = lean_ctor_get(v_v_3224_, 1);
lean_inc_ref(v_msg_3225_);
v___x_3226_ = lean_unsigned_to_nat(0u);
v_bs_x27_3227_ = lean_array_uset(v_bs_3222_, v_i_3221_, v___x_3226_);
v___x_3228_ = ((size_t)1ULL);
v___x_3229_ = lean_usize_add(v_i_3221_, v___x_3228_);
v___x_3230_ = lean_array_uset(v_bs_x27_3227_, v_i_3221_, v_msg_3225_);
v_i_3221_ = v___x_3229_;
v_bs_3222_ = v___x_3230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_3232_, lean_object* v_i_3233_, lean_object* v_bs_3234_){
_start:
{
size_t v_sz_boxed_3235_; size_t v_i_boxed_3236_; lean_object* v_res_3237_; 
v_sz_boxed_3235_ = lean_unbox_usize(v_sz_3232_);
lean_dec(v_sz_3232_);
v_i_boxed_3236_ = lean_unbox_usize(v_i_3233_);
lean_dec(v_i_3233_);
v_res_3237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(v_sz_boxed_3235_, v_i_boxed_3236_, v_bs_3234_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(lean_object* v_oldTraces_3238_, lean_object* v_data_3239_, lean_object* v_ref_3240_, lean_object* v_msg_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_toCold_3247_; lean_object* v_currRecDepth_3248_; lean_object* v_ref_3249_; uint8_t v_diag_3250_; uint8_t v_suppressElabErrors_3251_; lean_object* v_ref_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v_traceState_3255_; lean_object* v_traces_3256_; lean_object* v___x_3257_; size_t v_sz_3258_; size_t v___x_3259_; lean_object* v___x_3260_; lean_object* v_msg_3261_; lean_object* v___x_3262_; lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3300_; 
v_toCold_3247_ = lean_ctor_get(v___y_3244_, 0);
v_currRecDepth_3248_ = lean_ctor_get(v___y_3244_, 1);
v_ref_3249_ = lean_ctor_get(v___y_3244_, 2);
v_diag_3250_ = lean_ctor_get_uint8(v___y_3244_, sizeof(void*)*3);
v_suppressElabErrors_3251_ = lean_ctor_get_uint8(v___y_3244_, sizeof(void*)*3 + 1);
v_ref_3252_ = l_Lean_replaceRef(v_ref_3240_, v_ref_3249_);
lean_inc(v_currRecDepth_3248_);
lean_inc_ref(v_toCold_3247_);
v___x_3253_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3253_, 0, v_toCold_3247_);
lean_ctor_set(v___x_3253_, 1, v_currRecDepth_3248_);
lean_ctor_set(v___x_3253_, 2, v_ref_3252_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*3, v_diag_3250_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*3 + 1, v_suppressElabErrors_3251_);
v___x_3254_ = lean_st_ref_get(v___y_3245_);
v_traceState_3255_ = lean_ctor_get(v___x_3254_, 4);
lean_inc_ref(v_traceState_3255_);
lean_dec(v___x_3254_);
v_traces_3256_ = lean_ctor_get(v_traceState_3255_, 0);
lean_inc_ref(v_traces_3256_);
lean_dec_ref(v_traceState_3255_);
v___x_3257_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3256_);
lean_dec_ref(v_traces_3256_);
v_sz_3258_ = lean_array_size(v___x_3257_);
v___x_3259_ = ((size_t)0ULL);
v___x_3260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(v_sz_3258_, v___x_3259_, v___x_3257_);
v_msg_3261_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3261_, 0, v_data_3239_);
lean_ctor_set(v_msg_3261_, 1, v_msg_3241_);
lean_ctor_set(v_msg_3261_, 2, v___x_3260_);
v___x_3262_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_3261_, v___y_3242_, v___y_3243_, v___x_3253_, v___y_3245_);
lean_dec_ref_known(v___x_3253_, 3);
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3265_ = v___x_3262_;
v_isShared_3266_ = v_isSharedCheck_3300_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3300_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3267_; lean_object* v_traceState_3268_; lean_object* v_env_3269_; lean_object* v_nextMacroScope_3270_; lean_object* v_ngen_3271_; lean_object* v_auxDeclNGen_3272_; lean_object* v_cache_3273_; lean_object* v_messages_3274_; lean_object* v_infoState_3275_; lean_object* v_snapshotTasks_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3299_; 
v___x_3267_ = lean_st_ref_take(v___y_3245_);
v_traceState_3268_ = lean_ctor_get(v___x_3267_, 4);
v_env_3269_ = lean_ctor_get(v___x_3267_, 0);
v_nextMacroScope_3270_ = lean_ctor_get(v___x_3267_, 1);
v_ngen_3271_ = lean_ctor_get(v___x_3267_, 2);
v_auxDeclNGen_3272_ = lean_ctor_get(v___x_3267_, 3);
v_cache_3273_ = lean_ctor_get(v___x_3267_, 5);
v_messages_3274_ = lean_ctor_get(v___x_3267_, 6);
v_infoState_3275_ = lean_ctor_get(v___x_3267_, 7);
v_snapshotTasks_3276_ = lean_ctor_get(v___x_3267_, 8);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3278_ = v___x_3267_;
v_isShared_3279_ = v_isSharedCheck_3299_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_snapshotTasks_3276_);
lean_inc(v_infoState_3275_);
lean_inc(v_messages_3274_);
lean_inc(v_cache_3273_);
lean_inc(v_traceState_3268_);
lean_inc(v_auxDeclNGen_3272_);
lean_inc(v_ngen_3271_);
lean_inc(v_nextMacroScope_3270_);
lean_inc(v_env_3269_);
lean_dec(v___x_3267_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3299_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
uint64_t v_tid_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3297_; 
v_tid_3280_ = lean_ctor_get_uint64(v_traceState_3268_, sizeof(void*)*1);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_traceState_3268_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v_traceState_3268_, 0);
lean_dec(v_unused_3298_);
v___x_3282_ = v_traceState_3268_;
v_isShared_3283_ = v_isSharedCheck_3297_;
goto v_resetjp_3281_;
}
else
{
lean_dec(v_traceState_3268_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3297_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v_ref_3240_);
lean_ctor_set(v___x_3285_, 1, v_a_3263_);
v___x_3286_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3238_, v___x_3285_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3286_);
v___x_3288_ = v___x_3282_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3286_);
lean_ctor_set_uint64(v_reuseFailAlloc_3296_, sizeof(void*)*1, v_tid_3280_);
v___x_3288_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3290_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 4, v___x_3288_);
v___x_3290_ = v___x_3278_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_env_3269_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_nextMacroScope_3270_);
lean_ctor_set(v_reuseFailAlloc_3295_, 2, v_ngen_3271_);
lean_ctor_set(v_reuseFailAlloc_3295_, 3, v_auxDeclNGen_3272_);
lean_ctor_set(v_reuseFailAlloc_3295_, 4, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3295_, 5, v_cache_3273_);
lean_ctor_set(v_reuseFailAlloc_3295_, 6, v_messages_3274_);
lean_ctor_set(v_reuseFailAlloc_3295_, 7, v_infoState_3275_);
lean_ctor_set(v_reuseFailAlloc_3295_, 8, v_snapshotTasks_3276_);
v___x_3290_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_st_ref_put(v___y_3245_, v___x_3290_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3284_);
v___x_3293_ = v___x_3265_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3284_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg___boxed(lean_object* v_oldTraces_3301_, lean_object* v_data_3302_, lean_object* v_ref_3303_, lean_object* v_msg_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3301_, v_data_3302_, v_ref_3303_, v_msg_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(lean_object* v_x_3311_){
_start:
{
if (lean_obj_tag(v_x_3311_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
v_a_3313_ = lean_ctor_get(v_x_3311_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_x_3311_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v_x_3311_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v_x_3311_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
lean_ctor_set_tag(v___x_3315_, 1);
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
v_a_3321_ = lean_ctor_get(v_x_3311_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_x_3311_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v_x_3311_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v_x_3311_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
lean_ctor_set_tag(v___x_3323_, 0);
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg___boxed(lean_object* v_x_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_x_3329_);
return v_res_3331_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0(void){
_start:
{
lean_object* v___x_3332_; double v___x_3333_; 
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_float_of_nat(v___x_3332_);
return v___x_3333_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1));
v___x_3336_ = l_Lean_stringToMessageData(v___x_3335_);
return v___x_3336_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3337_; double v___x_3338_; 
v___x_3337_ = lean_unsigned_to_nat(1000u);
v___x_3338_ = lean_float_of_nat(v___x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(lean_object* v_cls_3339_, uint8_t v_collapsed_3340_, lean_object* v_tag_3341_, lean_object* v_opts_3342_, uint8_t v_clsEnabled_3343_, lean_object* v_oldTraces_3344_, lean_object* v_msg_3345_, lean_object* v_resStartStop_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_fst_3359_; lean_object* v_snd_3360_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v_data_3364_; lean_object* v_fst_3367_; lean_object* v_snd_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; lean_object* v___y_3372_; lean_object* v_a_3373_; uint8_t v___y_3388_; double v___y_3419_; 
v_fst_3359_ = lean_ctor_get(v_resStartStop_3346_, 0);
lean_inc(v_fst_3359_);
v_snd_3360_ = lean_ctor_get(v_resStartStop_3346_, 1);
lean_inc(v_snd_3360_);
lean_dec_ref(v_resStartStop_3346_);
v_fst_3367_ = lean_ctor_get(v_snd_3360_, 0);
lean_inc(v_fst_3367_);
v_snd_3368_ = lean_ctor_get(v_snd_3360_, 1);
lean_inc(v_snd_3368_);
lean_dec(v_snd_3360_);
v___x_3369_ = l_Lean_trace_profiler;
v___x_3370_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3342_, v___x_3369_);
if (v___x_3370_ == 0)
{
v___y_3388_ = v___x_3370_;
goto v___jp_3387_;
}
else
{
lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3424_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3425_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3342_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; double v___x_3428_; double v___x_3429_; double v___x_3430_; 
v___x_3426_ = l_Lean_trace_profiler_threshold;
v___x_3427_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3342_, v___x_3426_);
v___x_3428_ = lean_float_of_nat(v___x_3427_);
v___x_3429_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3);
v___x_3430_ = lean_float_div(v___x_3428_, v___x_3429_);
v___y_3419_ = v___x_3430_;
goto v___jp_3418_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; double v___x_3433_; 
v___x_3431_ = l_Lean_trace_profiler_threshold;
v___x_3432_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3342_, v___x_3431_);
v___x_3433_ = lean_float_of_nat(v___x_3432_);
v___y_3419_ = v___x_3433_;
goto v___jp_3418_;
}
}
v___jp_3361_:
{
lean_object* v___x_3365_; 
lean_inc(v___y_3362_);
v___x_3365_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3344_, v_data_3364_, v___y_3362_, v___y_3363_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; 
lean_dec_ref_known(v___x_3365_, 1);
v___x_3366_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_fst_3359_);
return v___x_3366_;
}
else
{
lean_dec(v_fst_3359_);
return v___x_3365_;
}
}
v___jp_3371_:
{
uint8_t v_result_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; double v___x_3377_; lean_object* v_data_3378_; 
v_result_3374_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(v_fst_3359_);
v___x_3375_ = lean_box(v_result_3374_);
v___x_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
v___x_3377_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0);
lean_inc_ref(v_tag_3341_);
lean_inc_ref(v___x_3376_);
lean_inc(v_cls_3339_);
v_data_3378_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3378_, 0, v_cls_3339_);
lean_ctor_set(v_data_3378_, 1, v___x_3376_);
lean_ctor_set(v_data_3378_, 2, v_tag_3341_);
lean_ctor_set_float(v_data_3378_, sizeof(void*)*3, v___x_3377_);
lean_ctor_set_float(v_data_3378_, sizeof(void*)*3 + 8, v___x_3377_);
lean_ctor_set_uint8(v_data_3378_, sizeof(void*)*3 + 16, v_collapsed_3340_);
if (v___x_3370_ == 0)
{
lean_dec_ref_known(v___x_3376_, 1);
lean_dec(v_snd_3368_);
lean_dec(v_fst_3367_);
lean_dec_ref(v_tag_3341_);
lean_dec(v_cls_3339_);
v___y_3362_ = v___y_3372_;
v___y_3363_ = v_a_3373_;
v_data_3364_ = v_data_3378_;
goto v___jp_3361_;
}
else
{
lean_object* v_data_3379_; double v___x_3380_; double v___x_3381_; 
lean_dec_ref_known(v_data_3378_, 3);
v_data_3379_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3379_, 0, v_cls_3339_);
lean_ctor_set(v_data_3379_, 1, v___x_3376_);
lean_ctor_set(v_data_3379_, 2, v_tag_3341_);
v___x_3380_ = lean_unbox_float(v_fst_3367_);
lean_dec(v_fst_3367_);
lean_ctor_set_float(v_data_3379_, sizeof(void*)*3, v___x_3380_);
v___x_3381_ = lean_unbox_float(v_snd_3368_);
lean_dec(v_snd_3368_);
lean_ctor_set_float(v_data_3379_, sizeof(void*)*3 + 8, v___x_3381_);
lean_ctor_set_uint8(v_data_3379_, sizeof(void*)*3 + 16, v_collapsed_3340_);
v___y_3362_ = v___y_3372_;
v___y_3363_ = v_a_3373_;
v_data_3364_ = v_data_3379_;
goto v___jp_3361_;
}
}
v___jp_3382_:
{
lean_object* v_ref_3383_; lean_object* v___x_3384_; 
v_ref_3383_ = lean_ctor_get(v___y_3356_, 2);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
lean_inc(v___y_3355_);
lean_inc_ref(v___y_3354_);
lean_inc(v___y_3353_);
lean_inc_ref(v___y_3352_);
lean_inc(v___y_3351_);
lean_inc_ref(v___y_3350_);
lean_inc(v___y_3349_);
lean_inc(v___y_3348_);
lean_inc_ref(v___y_3347_);
lean_inc(v_fst_3359_);
v___x_3384_ = lean_apply_13(v_msg_3345_, v_fst_3359_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, lean_box(0));
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___y_3372_ = v_ref_3383_;
v_a_3373_ = v_a_3385_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3386_; 
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2);
v___y_3372_ = v_ref_3383_;
v_a_3373_ = v___x_3386_;
goto v___jp_3371_;
}
}
v___jp_3387_:
{
if (v_clsEnabled_3343_ == 0)
{
if (v___y_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v_traceState_3390_; lean_object* v_env_3391_; lean_object* v_nextMacroScope_3392_; lean_object* v_ngen_3393_; lean_object* v_auxDeclNGen_3394_; lean_object* v_cache_3395_; lean_object* v_messages_3396_; lean_object* v_infoState_3397_; lean_object* v_snapshotTasks_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v_snd_3368_);
lean_dec(v_fst_3367_);
lean_dec_ref(v_msg_3345_);
lean_dec_ref(v_tag_3341_);
lean_dec(v_cls_3339_);
v___x_3389_ = lean_st_ref_take(v___y_3357_);
v_traceState_3390_ = lean_ctor_get(v___x_3389_, 4);
v_env_3391_ = lean_ctor_get(v___x_3389_, 0);
v_nextMacroScope_3392_ = lean_ctor_get(v___x_3389_, 1);
v_ngen_3393_ = lean_ctor_get(v___x_3389_, 2);
v_auxDeclNGen_3394_ = lean_ctor_get(v___x_3389_, 3);
v_cache_3395_ = lean_ctor_get(v___x_3389_, 5);
v_messages_3396_ = lean_ctor_get(v___x_3389_, 6);
v_infoState_3397_ = lean_ctor_get(v___x_3389_, 7);
v_snapshotTasks_3398_ = lean_ctor_get(v___x_3389_, 8);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3400_ = v___x_3389_;
v_isShared_3401_ = v_isSharedCheck_3417_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_snapshotTasks_3398_);
lean_inc(v_infoState_3397_);
lean_inc(v_messages_3396_);
lean_inc(v_cache_3395_);
lean_inc(v_traceState_3390_);
lean_inc(v_auxDeclNGen_3394_);
lean_inc(v_ngen_3393_);
lean_inc(v_nextMacroScope_3392_);
lean_inc(v_env_3391_);
lean_dec(v___x_3389_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3417_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
uint64_t v_tid_3402_; lean_object* v_traces_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3416_; 
v_tid_3402_ = lean_ctor_get_uint64(v_traceState_3390_, sizeof(void*)*1);
v_traces_3403_ = lean_ctor_get(v_traceState_3390_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_traceState_3390_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3405_ = v_traceState_3390_;
v_isShared_3406_ = v_isSharedCheck_3416_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_traces_3403_);
lean_dec(v_traceState_3390_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3416_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3407_; lean_object* v___x_3409_; 
v___x_3407_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3344_, v_traces_3403_);
lean_dec_ref(v_traces_3403_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v___x_3407_);
v___x_3409_ = v___x_3405_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3407_);
lean_ctor_set_uint64(v_reuseFailAlloc_3415_, sizeof(void*)*1, v_tid_3402_);
v___x_3409_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3411_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 4, v___x_3409_);
v___x_3411_ = v___x_3400_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_env_3391_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_nextMacroScope_3392_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_ngen_3393_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_auxDeclNGen_3394_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3414_, 5, v_cache_3395_);
lean_ctor_set(v_reuseFailAlloc_3414_, 6, v_messages_3396_);
lean_ctor_set(v_reuseFailAlloc_3414_, 7, v_infoState_3397_);
lean_ctor_set(v_reuseFailAlloc_3414_, 8, v_snapshotTasks_3398_);
v___x_3411_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_st_ref_put(v___y_3357_, v___x_3411_);
v___x_3413_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_fst_3359_);
return v___x_3413_;
}
}
}
}
}
else
{
goto v___jp_3382_;
}
}
else
{
goto v___jp_3382_;
}
}
v___jp_3418_:
{
double v___x_3420_; double v___x_3421_; double v___x_3422_; uint8_t v___x_3423_; 
v___x_3420_ = lean_unbox_float(v_snd_3368_);
v___x_3421_ = lean_unbox_float(v_fst_3367_);
v___x_3422_ = lean_float_sub(v___x_3420_, v___x_3421_);
v___x_3423_ = lean_float_decLt(v___y_3419_, v___x_3422_);
v___y_3388_ = v___x_3423_;
goto v___jp_3387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___boxed(lean_object** _args){
lean_object* v_cls_3434_ = _args[0];
lean_object* v_collapsed_3435_ = _args[1];
lean_object* v_tag_3436_ = _args[2];
lean_object* v_opts_3437_ = _args[3];
lean_object* v_clsEnabled_3438_ = _args[4];
lean_object* v_oldTraces_3439_ = _args[5];
lean_object* v_msg_3440_ = _args[6];
lean_object* v_resStartStop_3441_ = _args[7];
lean_object* v___y_3442_ = _args[8];
lean_object* v___y_3443_ = _args[9];
lean_object* v___y_3444_ = _args[10];
lean_object* v___y_3445_ = _args[11];
lean_object* v___y_3446_ = _args[12];
lean_object* v___y_3447_ = _args[13];
lean_object* v___y_3448_ = _args[14];
lean_object* v___y_3449_ = _args[15];
lean_object* v___y_3450_ = _args[16];
lean_object* v___y_3451_ = _args[17];
lean_object* v___y_3452_ = _args[18];
lean_object* v___y_3453_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_3454_; uint8_t v_clsEnabled_boxed_3455_; lean_object* v_res_3456_; 
v_collapsed_boxed_3454_ = lean_unbox(v_collapsed_3435_);
v_clsEnabled_boxed_3455_ = lean_unbox(v_clsEnabled_3438_);
v_res_3456_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v_cls_3434_, v_collapsed_boxed_3454_, v_tag_3436_, v_opts_3437_, v_clsEnabled_boxed_3455_, v_oldTraces_3439_, v_msg_3440_, v_resStartStop_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_opts_3437_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(lean_object* v_cls_3460_, lean_object* v_msg_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v_ref_3467_; lean_object* v___x_3468_; lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3513_; 
v_ref_3467_ = lean_ctor_get(v___y_3464_, 2);
v___x_3468_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3513_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3513_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v_traceState_3474_; lean_object* v_env_3475_; lean_object* v_nextMacroScope_3476_; lean_object* v_ngen_3477_; lean_object* v_auxDeclNGen_3478_; lean_object* v_cache_3479_; lean_object* v_messages_3480_; lean_object* v_infoState_3481_; lean_object* v_snapshotTasks_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3512_; 
v___x_3473_ = lean_st_ref_take(v___y_3465_);
v_traceState_3474_ = lean_ctor_get(v___x_3473_, 4);
v_env_3475_ = lean_ctor_get(v___x_3473_, 0);
v_nextMacroScope_3476_ = lean_ctor_get(v___x_3473_, 1);
v_ngen_3477_ = lean_ctor_get(v___x_3473_, 2);
v_auxDeclNGen_3478_ = lean_ctor_get(v___x_3473_, 3);
v_cache_3479_ = lean_ctor_get(v___x_3473_, 5);
v_messages_3480_ = lean_ctor_get(v___x_3473_, 6);
v_infoState_3481_ = lean_ctor_get(v___x_3473_, 7);
v_snapshotTasks_3482_ = lean_ctor_get(v___x_3473_, 8);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3484_ = v___x_3473_;
v_isShared_3485_ = v_isSharedCheck_3512_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_snapshotTasks_3482_);
lean_inc(v_infoState_3481_);
lean_inc(v_messages_3480_);
lean_inc(v_cache_3479_);
lean_inc(v_traceState_3474_);
lean_inc(v_auxDeclNGen_3478_);
lean_inc(v_ngen_3477_);
lean_inc(v_nextMacroScope_3476_);
lean_inc(v_env_3475_);
lean_dec(v___x_3473_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3512_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
uint64_t v_tid_3486_; lean_object* v_traces_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3511_; 
v_tid_3486_ = lean_ctor_get_uint64(v_traceState_3474_, sizeof(void*)*1);
v_traces_3487_ = lean_ctor_get(v_traceState_3474_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_traceState_3474_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3489_ = v_traceState_3474_;
v_isShared_3490_ = v_isSharedCheck_3511_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_traces_3487_);
lean_dec(v_traceState_3474_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3511_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; double v___x_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3502_; 
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_box(0);
v___x_3493_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0);
v___x_3494_ = 0;
v___x_3495_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0));
v___x_3496_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3496_, 0, v_cls_3460_);
lean_ctor_set(v___x_3496_, 1, v___x_3492_);
lean_ctor_set(v___x_3496_, 2, v___x_3495_);
lean_ctor_set_float(v___x_3496_, sizeof(void*)*3, v___x_3493_);
lean_ctor_set_float(v___x_3496_, sizeof(void*)*3 + 8, v___x_3493_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*3 + 16, v___x_3494_);
v___x_3497_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1));
v___x_3498_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3496_);
lean_ctor_set(v___x_3498_, 1, v_a_3469_);
lean_ctor_set(v___x_3498_, 2, v___x_3497_);
lean_inc(v_ref_3467_);
v___x_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3499_, 0, v_ref_3467_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_PersistentArray_push___redArg(v_traces_3487_, v___x_3499_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3500_);
v___x_3502_ = v___x_3489_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3500_);
lean_ctor_set_uint64(v_reuseFailAlloc_3510_, sizeof(void*)*1, v_tid_3486_);
v___x_3502_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 4, v___x_3502_);
v___x_3504_ = v___x_3484_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_env_3475_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_nextMacroScope_3476_);
lean_ctor_set(v_reuseFailAlloc_3509_, 2, v_ngen_3477_);
lean_ctor_set(v_reuseFailAlloc_3509_, 3, v_auxDeclNGen_3478_);
lean_ctor_set(v_reuseFailAlloc_3509_, 4, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3509_, 5, v_cache_3479_);
lean_ctor_set(v_reuseFailAlloc_3509_, 6, v_messages_3480_);
lean_ctor_set(v_reuseFailAlloc_3509_, 7, v_infoState_3481_);
lean_ctor_set(v_reuseFailAlloc_3509_, 8, v_snapshotTasks_3482_);
v___x_3504_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = lean_st_ref_put(v___y_3465_, v___x_3504_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3491_);
v___x_3507_ = v___x_3471_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3491_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___boxed(lean_object* v_cls_3514_, lean_object* v_msg_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v_cls_3514_, v_msg_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3521_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__5));
v___x_3534_ = l_Lean_Name_append(v___x_3533_, v___x_3532_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(lean_object* v_as_3535_, size_t v_i_3536_, size_t v_stop_3537_, lean_object* v_b_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_a_3552_; uint8_t v___x_3558_; 
v___x_3558_ = lean_usize_dec_eq(v_i_3536_, v_stop_3537_);
if (v___x_3558_ == 0)
{
lean_object* v_toCold_3559_; lean_object* v_options_3560_; uint8_t v_hasTrace_3561_; 
v_toCold_3559_ = lean_ctor_get(v___y_3548_, 0);
v_options_3560_ = lean_ctor_get(v_toCold_3559_, 2);
v_hasTrace_3561_ = lean_ctor_get_uint8(v_options_3560_, sizeof(void*)*1);
if (v_hasTrace_3561_ == 0)
{
goto v___jp_3556_;
}
else
{
lean_object* v_inheritedTraceOptions_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; 
v_inheritedTraceOptions_3562_ = lean_ctor_get(v_toCold_3559_, 11);
v___x_3563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3564_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3565_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3562_, v_options_3560_, v___x_3564_);
if (v___x_3565_ == 0)
{
goto v___jp_3556_;
}
else
{
lean_object* v___x_3566_; lean_object* v_type_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3566_ = lean_array_uget_borrowed(v_as_3535_, v_i_3536_);
v_type_3567_ = lean_ctor_get(v___x_3566_, 1);
lean_inc_ref(v_type_3567_);
v___x_3568_ = l_Lean_MessageData_ofExpr(v_type_3567_);
v___x_3569_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v___x_3563_, v___x_3568_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3569_, 1);
v_a_3552_ = v_a_3570_;
goto v___jp_3551_;
}
else
{
return v___x_3569_;
}
}
}
}
else
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_b_3538_);
return v___x_3571_;
}
v___jp_3551_:
{
size_t v___x_3553_; size_t v___x_3554_; 
v___x_3553_ = ((size_t)1ULL);
v___x_3554_ = lean_usize_add(v_i_3536_, v___x_3553_);
v_i_3536_ = v___x_3554_;
v_b_3538_ = v_a_3552_;
goto _start;
}
v___jp_3556_:
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_box(0);
v_a_3552_ = v___x_3557_;
goto v___jp_3551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___boxed(lean_object* v_as_3572_, lean_object* v_i_3573_, lean_object* v_stop_3574_, lean_object* v_b_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
size_t v_i_boxed_3588_; size_t v_stop_boxed_3589_; lean_object* v_res_3590_; 
v_i_boxed_3588_ = lean_unbox_usize(v_i_3573_);
lean_dec(v_i_3573_);
v_stop_boxed_3589_ = lean_unbox_usize(v_stop_3574_);
lean_dec(v_stop_3574_);
v_res_3590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(v_as_3572_, v_i_boxed_3588_, v_stop_boxed_3589_, v_b_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec_ref(v_as_3572_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(lean_object* v_as_3591_, size_t v_i_3592_, size_t v_stop_3593_, lean_object* v_b_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v_a_3608_; uint8_t v___x_3614_; 
v___x_3614_ = lean_usize_dec_eq(v_i_3592_, v_stop_3593_);
if (v___x_3614_ == 0)
{
lean_object* v_toCold_3615_; lean_object* v_options_3616_; uint8_t v_hasTrace_3617_; 
v_toCold_3615_ = lean_ctor_get(v___y_3604_, 0);
v_options_3616_ = lean_ctor_get(v_toCold_3615_, 2);
v_hasTrace_3617_ = lean_ctor_get_uint8(v_options_3616_, sizeof(void*)*1);
if (v_hasTrace_3617_ == 0)
{
goto v___jp_3612_;
}
else
{
lean_object* v_inheritedTraceOptions_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; 
v_inheritedTraceOptions_3618_ = lean_ctor_get(v_toCold_3615_, 11);
v___x_3619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3620_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3621_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3618_, v_options_3616_, v___x_3620_);
if (v___x_3621_ == 0)
{
goto v___jp_3612_;
}
else
{
lean_object* v___x_3622_; lean_object* v_type_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3622_ = lean_array_uget_borrowed(v_as_3591_, v_i_3592_);
v_type_3623_ = lean_ctor_get(v___x_3622_, 1);
lean_inc_ref(v_type_3623_);
v___x_3624_ = l_Lean_MessageData_ofExpr(v_type_3623_);
v___x_3625_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v___x_3619_, v___x_3624_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
v_a_3608_ = v_a_3626_;
goto v___jp_3607_;
}
else
{
return v___x_3625_;
}
}
}
}
else
{
lean_object* v___x_3627_; 
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v_b_3594_);
return v___x_3627_;
}
v___jp_3607_:
{
size_t v___x_3609_; size_t v___x_3610_; lean_object* v___x_3611_; 
v___x_3609_ = ((size_t)1ULL);
v___x_3610_ = lean_usize_add(v_i_3592_, v___x_3609_);
v___x_3611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(v_as_3591_, v___x_3610_, v_stop_3593_, v_a_3608_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
return v___x_3611_;
}
v___jp_3612_:
{
lean_object* v___x_3613_; 
v___x_3613_ = lean_box(0);
v_a_3608_ = v___x_3613_;
goto v___jp_3607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1___boxed(lean_object* v_as_3628_, lean_object* v_i_3629_, lean_object* v_stop_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
size_t v_i_boxed_3644_; size_t v_stop_boxed_3645_; lean_object* v_res_3646_; 
v_i_boxed_3644_ = lean_unbox_usize(v_i_3629_);
lean_dec(v_i_3629_);
v_stop_boxed_3645_ = lean_unbox_usize(v_stop_3630_);
lean_dec(v_stop_3630_);
v_res_3646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_as_3628_, v_i_boxed_3644_, v_stop_boxed_3645_, v_b_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_as_3628_);
return v_res_3646_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1(void){
_start:
{
lean_object* v___x_3648_; double v___x_3649_; 
v___x_3648_ = lean_unsigned_to_nat(1000000000u);
v___x_3649_ = lean_float_of_nat(v___x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v___f_3662_; lean_object* v___x_3663_; 
v___f_3662_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0));
v___x_3663_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3828_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3828_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3828_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
if (lean_obj_tag(v_a_3664_) == 1)
{
lean_object* v_val_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3822_; 
v_val_3668_ = lean_ctor_get(v_a_3664_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_a_3664_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3670_ = v_a_3664_;
v_isShared_3671_ = v_isSharedCheck_3822_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_val_3668_);
lean_dec(v_a_3664_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3822_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___y_3693_; lean_object* v_toCold_3702_; lean_object* v_options_3703_; lean_object* v_inheritedTraceOptions_3704_; uint8_t v_hasTrace_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_toCold_3702_ = lean_ctor_get(v_a_3659_, 0);
v_options_3703_ = lean_ctor_get(v_toCold_3702_, 2);
v_inheritedTraceOptions_3704_ = lean_ctor_get(v_toCold_3702_, 11);
v_hasTrace_3705_ = lean_ctor_get_uint8(v_options_3703_, sizeof(void*)*1);
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = lean_array_get_size(v_val_3668_);
if (v_hasTrace_3705_ == 0)
{
uint8_t v___x_3708_; 
lean_del_object(v___x_3670_);
v___x_3708_ = lean_nat_dec_lt(v___x_3706_, v___x_3707_);
if (v___x_3708_ == 0)
{
goto v___jp_3672_;
}
else
{
lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = lean_box(0);
v___x_3710_ = lean_nat_dec_le(v___x_3707_, v___x_3707_);
if (v___x_3710_ == 0)
{
if (v___x_3708_ == 0)
{
goto v___jp_3672_;
}
else
{
size_t v___x_3711_; size_t v___x_3712_; lean_object* v___x_3713_; 
v___x_3711_ = ((size_t)0ULL);
v___x_3712_ = lean_usize_of_nat(v___x_3707_);
v___x_3713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3668_, v___x_3711_, v___x_3712_, v___x_3709_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3693_ = v___x_3713_;
goto v___jp_3692_;
}
}
else
{
size_t v___x_3714_; size_t v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = ((size_t)0ULL);
v___x_3715_ = lean_usize_of_nat(v___x_3707_);
v___x_3716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3668_, v___x_3714_, v___x_3715_, v___x_3709_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3693_ = v___x_3716_;
goto v___jp_3692_;
}
}
}
else
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v_a_3724_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v_a_3739_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v_a_3759_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_a_3771_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; 
v___x_3717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3718_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0));
v___x_3719_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3704_, v_options_3703_, v___x_3719_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3811_; uint8_t v___x_3812_; 
v___x_3811_ = l_Lean_trace_profiler;
v___x_3812_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_options_3703_, v___x_3811_);
if (v___x_3812_ == 0)
{
uint8_t v___x_3813_; 
lean_del_object(v___x_3670_);
v___x_3813_ = lean_nat_dec_lt(v___x_3706_, v___x_3707_);
if (v___x_3813_ == 0)
{
goto v___jp_3672_;
}
else
{
lean_object* v___x_3814_; uint8_t v___x_3815_; 
v___x_3814_ = lean_box(0);
v___x_3815_ = lean_nat_dec_le(v___x_3707_, v___x_3707_);
if (v___x_3815_ == 0)
{
if (v___x_3813_ == 0)
{
goto v___jp_3672_;
}
else
{
size_t v___x_3816_; size_t v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = ((size_t)0ULL);
v___x_3817_ = lean_usize_of_nat(v___x_3707_);
v___x_3818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3668_, v___x_3816_, v___x_3817_, v___x_3814_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3693_ = v___x_3818_;
goto v___jp_3692_;
}
}
else
{
size_t v___x_3819_; size_t v___x_3820_; lean_object* v___x_3821_; 
v___x_3819_ = ((size_t)0ULL);
v___x_3820_ = lean_usize_of_nat(v___x_3707_);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3668_, v___x_3819_, v___x_3820_, v___x_3814_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3693_ = v___x_3821_;
goto v___jp_3692_;
}
}
}
else
{
goto v___jp_3786_;
}
}
else
{
goto v___jp_3786_;
}
v___jp_3721_:
{
lean_object* v___x_3725_; double v___x_3726_; double v___x_3727_; double v___x_3728_; double v___x_3729_; double v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3725_ = lean_io_mono_nanos_now();
v___x_3726_ = lean_float_of_nat(v___y_3723_);
v___x_3727_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1);
v___x_3728_ = lean_float_div(v___x_3726_, v___x_3727_);
v___x_3729_ = lean_float_of_nat(v___x_3725_);
v___x_3730_ = lean_float_div(v___x_3729_, v___x_3727_);
v___x_3731_ = lean_box_float(v___x_3728_);
v___x_3732_ = lean_box_float(v___x_3730_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_a_3724_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v___x_3717_, v_hasTrace_3705_, v___x_3718_, v_options_3703_, v___x_3720_, v___y_3722_, v___f_3662_, v___x_3734_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3693_ = v___x_3735_;
goto v___jp_3692_;
}
v___jp_3736_:
{
lean_object* v___x_3741_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_a_3739_);
v___x_3741_ = v___x_3670_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
v___y_3722_ = v___y_3737_;
v___y_3723_ = v___y_3738_;
v_a_3724_ = v___x_3741_;
goto v___jp_3721_;
}
}
v___jp_3743_:
{
if (lean_obj_tag(v___y_3746_) == 0)
{
lean_object* v_a_3747_; 
v_a_3747_ = lean_ctor_get(v___y_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___y_3746_, 1);
v___y_3737_ = v___y_3744_;
v___y_3738_ = v___y_3745_;
v_a_3739_ = v_a_3747_;
goto v___jp_3736_;
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_del_object(v___x_3670_);
v_a_3748_ = lean_ctor_get(v___y_3746_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___y_3746_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___y_3746_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___y_3746_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set_tag(v___x_3750_, 0);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
v___y_3722_ = v___y_3744_;
v___y_3723_ = v___y_3745_;
v_a_3724_ = v___x_3753_;
goto v___jp_3721_;
}
}
}
}
v___jp_3756_:
{
lean_object* v___x_3760_; double v___x_3761_; double v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3760_ = lean_io_get_num_heartbeats();
v___x_3761_ = lean_float_of_nat(v___y_3758_);
v___x_3762_ = lean_float_of_nat(v___x_3760_);
v___x_3763_ = lean_box_float(v___x_3761_);
v___x_3764_ = lean_box_float(v___x_3762_);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_a_3759_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v___x_3717_, v_hasTrace_3705_, v___x_3718_, v_options_3703_, v___x_3720_, v___y_3757_, v___f_3662_, v___x_3766_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3693_ = v___x_3767_;
goto v___jp_3692_;
}
v___jp_3768_:
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v_a_3771_);
v___y_3757_ = v___y_3769_;
v___y_3758_ = v___y_3770_;
v_a_3759_ = v___x_3772_;
goto v___jp_3756_;
}
v___jp_3773_:
{
if (lean_obj_tag(v___y_3776_) == 0)
{
lean_object* v_a_3777_; 
v_a_3777_ = lean_ctor_get(v___y_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___y_3776_, 1);
v___y_3769_ = v___y_3774_;
v___y_3770_ = v___y_3775_;
v_a_3771_ = v_a_3777_;
goto v___jp_3768_;
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
v_a_3778_ = lean_ctor_get(v___y_3776_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___y_3776_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___y_3776_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___y_3776_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
lean_ctor_set_tag(v___x_3780_, 0);
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
v___y_3757_ = v___y_3774_;
v___y_3758_ = v___y_3775_;
v_a_3759_ = v___x_3783_;
goto v___jp_3756_;
}
}
}
}
v___jp_3786_:
{
lean_object* v___x_3787_; lean_object* v_a_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v___x_3787_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v_a_3660_);
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3787_);
v___x_3789_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3790_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_options_3703_, v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3791_ = lean_io_mono_nanos_now();
v___x_3792_ = lean_box(0);
v___x_3793_ = lean_nat_dec_lt(v___x_3706_, v___x_3707_);
if (v___x_3793_ == 0)
{
v___y_3737_ = v_a_3788_;
v___y_3738_ = v___x_3791_;
v_a_3739_ = v___x_3792_;
goto v___jp_3736_;
}
else
{
uint8_t v___x_3794_; 
v___x_3794_ = lean_nat_dec_le(v___x_3707_, v___x_3707_);
if (v___x_3794_ == 0)
{
if (v___x_3793_ == 0)
{
v___y_3737_ = v_a_3788_;
v___y_3738_ = v___x_3791_;
v_a_3739_ = v___x_3792_;
goto v___jp_3736_;
}
else
{
size_t v___x_3795_; size_t v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = ((size_t)0ULL);
v___x_3796_ = lean_usize_of_nat(v___x_3707_);
v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3668_, v___x_3795_, v___x_3796_, v___x_3792_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3744_ = v_a_3788_;
v___y_3745_ = v___x_3791_;
v___y_3746_ = v___x_3797_;
goto v___jp_3743_;
}
}
else
{
size_t v___x_3798_; size_t v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = ((size_t)0ULL);
v___x_3799_ = lean_usize_of_nat(v___x_3707_);
v___x_3800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3668_, v___x_3798_, v___x_3799_, v___x_3792_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3744_ = v_a_3788_;
v___y_3745_ = v___x_3791_;
v___y_3746_ = v___x_3800_;
goto v___jp_3743_;
}
}
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
lean_del_object(v___x_3670_);
v___x_3801_ = lean_io_get_num_heartbeats();
v___x_3802_ = lean_box(0);
v___x_3803_ = lean_nat_dec_lt(v___x_3706_, v___x_3707_);
if (v___x_3803_ == 0)
{
v___y_3769_ = v_a_3788_;
v___y_3770_ = v___x_3801_;
v_a_3771_ = v___x_3802_;
goto v___jp_3768_;
}
else
{
uint8_t v___x_3804_; 
v___x_3804_ = lean_nat_dec_le(v___x_3707_, v___x_3707_);
if (v___x_3804_ == 0)
{
if (v___x_3803_ == 0)
{
v___y_3769_ = v_a_3788_;
v___y_3770_ = v___x_3801_;
v_a_3771_ = v___x_3802_;
goto v___jp_3768_;
}
else
{
size_t v___x_3805_; size_t v___x_3806_; lean_object* v___x_3807_; 
v___x_3805_ = ((size_t)0ULL);
v___x_3806_ = lean_usize_of_nat(v___x_3707_);
v___x_3807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3668_, v___x_3805_, v___x_3806_, v___x_3802_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3774_ = v_a_3788_;
v___y_3775_ = v___x_3801_;
v___y_3776_ = v___x_3807_;
goto v___jp_3773_;
}
}
else
{
size_t v___x_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = ((size_t)0ULL);
v___x_3809_ = lean_usize_of_nat(v___x_3707_);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3668_, v___x_3808_, v___x_3809_, v___x_3802_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3774_ = v_a_3788_;
v___y_3775_ = v___x_3801_;
v___y_3776_ = v___x_3810_;
goto v___jp_3773_;
}
}
}
}
}
v___jp_3672_:
{
lean_object* v___x_3673_; lean_object* v_caches_3674_; lean_object* v_typeAnalysis_3675_; lean_object* v_target_3676_; uint8_t v_didChange_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3690_; 
v___x_3673_ = lean_st_ref_take(v_a_3651_);
v_caches_3674_ = lean_ctor_get(v___x_3673_, 0);
v_typeAnalysis_3675_ = lean_ctor_get(v___x_3673_, 1);
v_target_3676_ = lean_ctor_get(v___x_3673_, 2);
v_didChange_3677_ = lean_ctor_get_uint8(v___x_3673_, sizeof(void*)*4);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; 
v_unused_3691_ = lean_ctor_get(v___x_3673_, 3);
lean_dec(v_unused_3691_);
v___x_3679_ = v___x_3673_;
v_isShared_3680_ = v_isSharedCheck_3690_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_target_3676_);
lean_inc(v_typeAnalysis_3675_);
lean_inc(v_caches_3674_);
lean_dec(v___x_3673_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3690_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 3, v_val_3668_);
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_caches_3674_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_typeAnalysis_3675_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_target_3676_);
lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_val_3668_);
lean_ctor_set_uint8(v_reuseFailAlloc_3689_, sizeof(void*)*4, v_didChange_3677_);
v___x_3682_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
v___x_3683_ = lean_st_ref_put(v_a_3651_, v___x_3682_);
v___x_3684_ = 0;
v___x_3685_ = lean_box(v___x_3684_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v___x_3685_);
v___x_3687_ = v___x_3666_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
v___jp_3692_:
{
if (lean_obj_tag(v___y_3693_) == 0)
{
lean_dec_ref_known(v___y_3693_, 1);
goto v___jp_3672_;
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec(v_val_3668_);
lean_del_object(v___x_3666_);
v_a_3694_ = lean_ctor_get(v___y_3693_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___y_3693_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___y_3693_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___y_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
}
else
{
uint8_t v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
lean_dec(v_a_3664_);
v___x_3823_ = 1;
v___x_3824_ = lean_box(v___x_3823_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v___x_3824_);
v___x_3826_ = v___x_3666_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
v_a_3829_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3663_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3663_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___boxed(lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec(v_a_3845_);
lean_dec_ref(v_a_3844_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(lean_object* v_cls_3850_, lean_object* v_msg_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v_cls_3850_, v_msg_3851_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___boxed(lean_object* v_cls_3865_, lean_object* v_msg_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(v_cls_3865_, v_msg_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(lean_object* v_00_u03b1_3880_, lean_object* v_x_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_x_3881_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3895_, lean_object* v_x_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(v_00_u03b1_3895_, v_x_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5(lean_object* v_oldTraces_3910_, lean_object* v_data_3911_, lean_object* v_ref_3912_, lean_object* v_msg_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3910_, v_data_3911_, v_ref_3912_, v_msg_3913_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___boxed(lean_object* v_oldTraces_3927_, lean_object* v_data_3928_, lean_object* v_ref_3929_, lean_object* v_msg_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5(v_oldTraces_3927_, v_data_3928_, v_ref_3929_, v_msg_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3943_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
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
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
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
lean_object* initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
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
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
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
