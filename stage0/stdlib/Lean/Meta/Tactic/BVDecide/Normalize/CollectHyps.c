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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getExprs___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_introN(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getUInt64Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_getInt64Value_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
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
v___x_5_ = lean_array_push(v___x_4_, v_hyp_1_);
v___x_6_ = lean_st_ref_put(v_a_2_, v___x_5_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordHyp(lean_object* v_hyp_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_27_ = lean_st_ref_take(v_a_15_);
v___x_28_ = lean_array_push(v___x_27_, v_hyp_13_);
v___x_29_ = lean_st_ref_put(v_a_15_, v___x_28_);
v___x_30_ = lean_box(0);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
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
uint8_t v___x_10249__boxed_133_; lean_object* v_res_134_; 
v___x_10249__boxed_133_ = lean_unbox(v___x_131_);
v_res_134_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(v___x_10249__boxed_133_, v_x_132_);
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
lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_163_ = lean_st_ref_get(v_a_146_);
v___x_164_ = 0;
lean_inc(v_a_159_);
v___x_165_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_163_, v_a_159_, v___x_164_);
lean_dec(v___x_163_);
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
v___x_178_ = lean_st_ref_take(v_a_145_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_box(4);
v___x_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v_a_172_);
lean_ctor_set(v___x_181_, 2, v_a_174_);
lean_ctor_set(v___x_181_, 3, v___x_180_);
v___x_182_ = lean_array_push(v___x_178_, v___x_181_);
v___x_183_ = lean_st_ref_put(v_a_145_, v___x_182_);
v___x_184_ = lean_box(0);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_184_);
v___x_186_ = v___x_176_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
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
lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = lean_st_ref_get(v_a_288_);
v___x_291_ = 0;
lean_inc_ref(v_default_286_);
v___x_292_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_290_, v_default_286_, v___x_291_);
lean_dec(v___x_290_);
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
lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___x_444_; 
lean_inc_ref(v_root_422_);
v___x_444_ = l_Lean_Meta_Sym_inferType(v_root_422_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_655_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_655_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_655_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_655_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; 
lean_inc(v_a_445_);
v___x_449_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_445_, v_a_432_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_646_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_646_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_646_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_646_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___y_455_; lean_object* v___y_456_; uint8_t v___y_465_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = l_Lean_Expr_cleanupAnnotations(v_a_450_);
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__4));
v___x_474_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__6));
v___x_476_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__8));
v___x_478_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
lean_del_object(v___x_452_);
v___x_479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__10));
v___x_480_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__12));
v___x_482_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__14));
v___x_484_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__16));
v___x_486_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__18));
v___x_488_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__20));
v___x_490_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__22));
v___x_492_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; 
v___x_493_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__24));
v___x_494_ = l_Lean_Expr_isConstOf(v___x_472_, v___x_493_);
if (v___x_494_ == 0)
{
uint8_t v___x_544_; 
v___x_544_ = l_Lean_Expr_isApp(v___x_472_);
if (v___x_544_ == 0)
{
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
v___y_496_ = v_a_423_;
v___y_497_ = v_a_424_;
v___y_498_ = v_a_425_;
v___y_499_ = v_a_426_;
v___y_500_ = v_a_427_;
v___y_501_ = v_a_428_;
v___y_502_ = v_a_429_;
v___y_503_ = v_a_430_;
v___y_504_ = v_a_431_;
v___y_505_ = v_a_432_;
v___y_506_ = v_a_433_;
v___y_507_ = v_a_434_;
goto v___jp_495_;
}
else
{
lean_object* v_arg_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_arg_545_ = lean_ctor_get(v___x_472_, 1);
lean_inc_ref(v_arg_545_);
v___x_546_ = l_Lean_Expr_appFnCleanup___redArg(v___x_472_);
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__26));
v___x_548_ = l_Lean_Expr_isConstOf(v___x_546_, v___x_547_);
lean_dec_ref(v___x_546_);
if (v___x_548_ == 0)
{
lean_dec_ref(v_arg_545_);
lean_del_object(v___x_447_);
v___y_496_ = v_a_423_;
v___y_497_ = v_a_424_;
v___y_498_ = v_a_425_;
v___y_499_ = v_a_426_;
v___y_500_ = v_a_427_;
v___y_501_ = v_a_428_;
v___y_502_ = v_a_429_;
v___y_503_ = v_a_430_;
v___y_504_ = v_a_431_;
v___y_505_ = v_a_432_;
v___y_506_ = v_a_433_;
v___y_507_ = v_a_434_;
goto v___jp_495_;
}
else
{
lean_object* v___x_549_; 
lean_dec(v_a_445_);
v___x_549_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_545_);
if (lean_obj_tag(v___x_549_) == 0)
{
v___y_465_ = v___x_494_;
goto v___jp_464_;
}
else
{
lean_dec_ref_known(v___x_549_, 1);
v___y_465_ = v___x_548_;
goto v___jp_464_;
}
}
}
}
else
{
lean_object* v___x_550_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
lean_inc_ref(v_root_422_);
v___x_550_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_root_422_, v_a_425_, v_a_429_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; uint8_t v___x_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = lean_unbox(v_a_551_);
lean_dec(v_a_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_inc_ref(v_root_422_);
v___x_553_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_root_422_, v_a_425_, v_a_429_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_581_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_581_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_581_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_581_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
uint8_t v___x_558_; 
v___x_558_ = lean_unbox(v_a_554_);
lean_dec(v_a_554_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_root_422_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_559_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
else
{
lean_object* v___x_563_; 
lean_del_object(v___x_556_);
lean_dec_ref(v_root_422_);
v___x_563_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_429_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_572_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_572_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v_a_564_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_568_);
v___x_570_ = v___x_566_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_563_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_563_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_root_422_);
v_a_582_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_553_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_553_);
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
else
{
lean_object* v___x_590_; 
lean_dec_ref(v_root_422_);
v___x_590_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_429_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v_a_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_597_ = v___x_593_;
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
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_590_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_590_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_root_422_);
v_a_608_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_550_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_550_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
v___jp_495_:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Expr_getAppFn_x27(v_a_445_);
lean_dec(v_a_445_);
if (lean_obj_tag(v___x_508_) == 4)
{
lean_object* v_declName_509_; lean_object* v___x_510_; 
v_declName_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_declName_509_);
lean_dec_ref_known(v___x_508_, 2);
v___x_510_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v___y_496_, v_declName_509_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_533_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_533_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_533_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_533_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
uint8_t v___x_515_; 
v___x_515_ = lean_unbox(v_a_511_);
lean_dec(v_a_511_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec_ref(v_root_422_);
v___x_516_ = lean_box(0);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_516_);
v___x_518_ = v___x_513_;
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
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_del_object(v___x_513_);
v___x_520_ = lean_st_ref_get(v___y_498_);
lean_inc_ref(v_root_422_);
v___x_521_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_520_, v_root_422_, v___x_494_);
lean_dec(v___x_520_);
v___x_522_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(v___x_521_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
if (lean_obj_tag(v_a_523_) == 1)
{
lean_dec_ref_known(v_a_523_, 1);
lean_dec_ref(v_root_422_);
return v___x_522_;
}
else
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_a_523_);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_532_);
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v_root_422_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_dec_ref(v_root_422_);
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_root_422_);
v_a_534_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_510_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_510_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec_ref(v___x_508_);
lean_dec_ref(v_root_422_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
}
else
{
uint8_t v_fixedInt_616_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v_fixedInt_616_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec_ref(v_root_422_);
v___x_617_ = lean_box(0);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__27));
v___x_620_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_619_, v_a_425_);
return v___x_620_;
}
}
}
else
{
uint8_t v_fixedInt_621_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v_fixedInt_621_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec_ref(v_root_422_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__28));
v___x_625_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_624_, v_a_425_);
return v___x_625_;
}
}
}
else
{
uint8_t v_fixedInt_626_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v_fixedInt_626_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec_ref(v_root_422_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__29));
v___x_630_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_629_, v_a_425_);
return v___x_630_;
}
}
}
else
{
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v___y_437_ = v_a_423_;
v___y_438_ = v_a_425_;
goto v___jp_436_;
}
}
else
{
uint8_t v_fixedInt_631_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v_fixedInt_631_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_root_422_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__30));
v___x_635_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_634_, v_a_425_);
return v___x_635_;
}
}
}
else
{
uint8_t v_fixedInt_636_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v_fixedInt_636_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v_root_422_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__31));
v___x_640_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_639_, v_a_425_);
return v___x_640_;
}
}
}
else
{
uint8_t v_fixedInt_641_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v_fixedInt_641_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 6);
if (v_fixedInt_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec_ref(v_root_422_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__32));
v___x_645_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_644_, v_a_425_);
return v___x_645_;
}
}
}
else
{
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v___y_455_ = v_a_423_;
v___y_456_ = v_a_425_;
goto v___jp_454_;
}
}
else
{
lean_dec_ref(v___x_472_);
lean_del_object(v___x_452_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v___y_437_ = v_a_423_;
v___y_438_ = v_a_425_;
goto v___jp_436_;
}
}
else
{
lean_dec_ref(v___x_472_);
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
v___y_455_ = v_a_423_;
v___y_456_ = v_a_425_;
goto v___jp_454_;
}
v___jp_454_:
{
uint8_t v_fixedInt_457_; 
v_fixedInt_457_ = lean_ctor_get_uint8(v___y_455_, sizeof(void*)*2 + 6);
if (v_fixedInt_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec_ref(v_root_422_);
v___x_458_ = lean_box(0);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_458_);
v___x_460_ = v___x_452_;
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
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_del_object(v___x_452_);
v___x_462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__1));
v___x_463_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_462_, v___y_456_);
return v___x_463_;
}
}
v___jp_464_:
{
if (v___y_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_468_; 
lean_dec_ref(v_root_422_);
v___x_466_ = lean_box(0);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_466_);
v___x_468_ = v___x_447_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_del_object(v___x_447_);
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___closed__2));
v___x_471_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_handleEqcWithConstType___redArg(v_root_422_, v___x_470_, v_a_425_);
return v___x_471_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
lean_dec_ref(v_root_422_);
v_a_647_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_449_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_449_);
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
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v_root_422_);
v_a_656_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_444_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_444_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass___boxed(lean_object* v_root_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_root_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0(lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___redArg(v_x_679_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0___boxed(lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_List_findM_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass_spec__0(v_x_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(lean_object* v_val_709_, uint8_t v___y_710_, lean_object* v_as_x27_711_, lean_object* v_b_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
if (lean_obj_tag(v_as_x27_711_) == 0)
{
lean_object* v___x_725_; 
lean_dec_ref(v_val_709_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_712_);
return v___x_725_;
}
else
{
lean_object* v_head_726_; lean_object* v_tail_727_; lean_object* v___x_728_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___x_778_; 
v_head_726_ = lean_ctor_get(v_as_x27_711_, 0);
v_tail_727_ = lean_ctor_get(v_as_x27_711_, 1);
v___x_728_ = lean_box(0);
v___x_778_ = lean_expr_eqv(v_head_726_, v_val_709_);
if (v___x_778_ == 0)
{
if (v___y_710_ == 0)
{
lean_object* v___x_779_; 
lean_inc_ref(v_val_709_);
lean_inc(v_head_726_);
v___x_779_ = l_Lean_Meta_Grind_hasSameType(v_head_726_, v_val_709_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; uint8_t v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = lean_unbox(v_a_780_);
lean_dec(v_a_780_);
if (v___x_781_ == 0)
{
v_as_x27_711_ = v_tail_727_;
v_b_712_ = v___x_728_;
goto _start;
}
else
{
v___y_730_ = v___y_713_;
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
goto v___jp_729_;
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_val_709_);
v_a_783_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_779_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_779_);
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
v___y_730_ = v___y_713_;
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
goto v___jp_729_;
}
}
else
{
v_as_x27_711_ = v_tail_727_;
v_b_712_ = v___x_728_;
goto _start;
}
v___jp_729_:
{
lean_object* v___x_741_; 
lean_inc_ref(v_val_709_);
lean_inc(v_head_726_);
v___x_741_ = l_Lean_Meta_mkEq(v_head_726_, v_val_709_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_Meta_Sym_shareCommonInc(v_a_742_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc(v___y_731_);
lean_inc_ref(v_val_709_);
lean_inc(v_head_726_);
v___x_745_ = lean_grind_mk_eq_proof(v_head_726_, v_val_709_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v___x_747_ = lean_st_ref_take(v___y_730_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_box(4);
v___x_750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v_a_744_);
lean_ctor_set(v___x_750_, 2, v_a_746_);
lean_ctor_set(v___x_750_, 3, v___x_749_);
v___x_751_ = lean_array_push(v___x_747_, v___x_750_);
v___x_752_ = lean_st_ref_put(v___y_730_, v___x_751_);
v_as_x27_711_ = v_tail_727_;
v_b_712_ = v___x_728_;
goto _start;
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_744_);
lean_dec_ref(v_val_709_);
v_a_754_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_745_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_745_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v_val_709_);
v_a_762_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_743_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_743_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_val_709_);
v_a_770_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_741_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_741_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg___boxed(lean_object* v_val_792_, lean_object* v___y_793_, lean_object* v_as_x27_794_, lean_object* v_b_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v___y_46583__boxed_808_; lean_object* v_res_809_; 
v___y_46583__boxed_808_ = lean_unbox(v___y_793_);
v_res_809_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_792_, v___y_46583__boxed_808_, v_as_x27_794_, v_b_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
lean_dec(v_as_x27_794_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5(lean_object* v_as_810_, size_t v_sz_811_, size_t v_i_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_usize_dec_lt(v_i_812_, v_sz_811_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_b_813_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v_a_830_; lean_object* v___x_831_; 
lean_dec_ref(v_b_813_);
v___x_829_ = lean_st_ref_get(v___y_816_);
v_a_830_ = lean_array_uget_borrowed(v_as_810_, v_i_812_);
lean_inc(v_a_830_);
v___x_831_ = l_Lean_Meta_Grind_Goal_getENode(v___x_829_, v_a_830_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___x_829_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; lean_object* v_a_835_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v___x_833_ = lean_box(0);
v___x_840_ = lean_box(0);
v___x_841_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_832_);
if (v___x_841_ == 0)
{
lean_dec(v_a_832_);
v_a_835_ = v___x_840_;
goto v___jp_834_;
}
else
{
lean_object* v___x_842_; 
lean_inc(v_a_830_);
v___x_842_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_a_830_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
if (lean_obj_tag(v_a_843_) == 1)
{
lean_object* v_val_844_; uint8_t v___y_846_; uint8_t v_heqProofs_859_; 
v_val_844_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v_a_843_, 1);
v_heqProofs_859_ = lean_ctor_get_uint8(v_a_832_, sizeof(void*)*12 + 4);
lean_dec(v_a_832_);
if (v_heqProofs_859_ == 0)
{
v___y_846_ = v___x_841_;
goto v___jp_845_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = 0;
v___y_846_ = v___x_860_;
goto v___jp_845_;
}
v___jp_845_:
{
lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_st_ref_get(v___y_816_);
v___x_848_ = 0;
lean_inc(v_a_830_);
v___x_849_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_847_, v_a_830_, v___x_848_);
lean_dec(v___x_847_);
v___x_850_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_844_, v___y_846_, v___x_849_, v___x_840_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___x_849_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_dec_ref_known(v___x_850_, 1);
v_a_835_ = v___x_840_;
goto v___jp_834_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
else
{
lean_dec(v_a_843_);
lean_dec(v_a_832_);
v_a_835_ = v___x_840_;
goto v___jp_834_;
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_a_832_);
v_a_861_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_842_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_842_);
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
v___jp_834_:
{
lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; 
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_833_);
lean_ctor_set(v___x_836_, 1, v_a_835_);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_812_, v___x_837_);
v_i_812_ = v___x_838_;
v_b_813_ = v___x_836_;
goto _start;
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_831_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_831_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_as_877_ = _args[0];
lean_object* v_sz_878_ = _args[1];
lean_object* v_i_879_ = _args[2];
lean_object* v_b_880_ = _args[3];
lean_object* v___y_881_ = _args[4];
lean_object* v___y_882_ = _args[5];
lean_object* v___y_883_ = _args[6];
lean_object* v___y_884_ = _args[7];
lean_object* v___y_885_ = _args[8];
lean_object* v___y_886_ = _args[9];
lean_object* v___y_887_ = _args[10];
lean_object* v___y_888_ = _args[11];
lean_object* v___y_889_ = _args[12];
lean_object* v___y_890_ = _args[13];
lean_object* v___y_891_ = _args[14];
lean_object* v___y_892_ = _args[15];
lean_object* v___y_893_ = _args[16];
_start:
{
size_t v_sz_boxed_894_; size_t v_i_boxed_895_; lean_object* v_res_896_; 
v_sz_boxed_894_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v_i_boxed_895_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5(v_as_877_, v_sz_boxed_894_, v_i_boxed_895_, v_b_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v_as_877_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2(lean_object* v_as_900_, size_t v_sz_901_, size_t v_i_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v___x_917_; 
v___x_917_ = lean_usize_dec_lt(v_i_902_, v_sz_901_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v_b_903_);
return v___x_918_;
}
else
{
lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_921_; 
lean_dec_ref(v_b_903_);
v___x_919_ = lean_st_ref_get(v___y_906_);
v_a_920_ = lean_array_uget_borrowed(v_as_900_, v_i_902_);
lean_inc(v_a_920_);
v___x_921_ = l_Lean_Meta_Grind_Goal_getENode(v___x_919_, v_a_920_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___x_919_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; uint8_t v___x_929_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v___x_923_ = lean_box(0);
v___x_929_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_922_);
if (v___x_929_ == 0)
{
lean_dec(v_a_922_);
goto v___jp_924_;
}
else
{
lean_object* v___x_930_; 
lean_inc(v_a_920_);
v___x_930_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_a_920_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
if (lean_obj_tag(v_a_931_) == 1)
{
lean_object* v_val_932_; uint8_t v___y_934_; uint8_t v_heqProofs_947_; 
v_val_932_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v_a_931_, 1);
v_heqProofs_947_ = lean_ctor_get_uint8(v_a_922_, sizeof(void*)*12 + 4);
lean_dec(v_a_922_);
if (v_heqProofs_947_ == 0)
{
v___y_934_ = v___x_929_;
goto v___jp_933_;
}
else
{
uint8_t v___x_948_; 
v___x_948_ = 0;
v___y_934_ = v___x_948_;
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_935_ = lean_st_ref_get(v___y_906_);
v___x_936_ = 0;
lean_inc(v_a_920_);
v___x_937_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_935_, v_a_920_, v___x_936_);
lean_dec(v___x_935_);
v___x_938_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_932_, v___y_934_, v___x_937_, v___x_923_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___x_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_dec_ref_known(v___x_938_, 1);
goto v___jp_924_;
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
else
{
lean_dec(v_a_931_);
lean_dec(v_a_922_);
goto v___jp_924_;
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_a_922_);
v_a_949_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_930_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_930_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
v___jp_924_:
{
lean_object* v___x_925_; size_t v___x_926_; size_t v___x_927_; lean_object* v___x_928_; 
v___x_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2___closed__0));
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_902_, v___x_926_);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2_spec__5(v_as_900_, v_sz_901_, v___x_927_, v___x_925_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_928_;
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_921_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_921_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_as_965_ = _args[0];
lean_object* v_sz_966_ = _args[1];
lean_object* v_i_967_ = _args[2];
lean_object* v_b_968_ = _args[3];
lean_object* v___y_969_ = _args[4];
lean_object* v___y_970_ = _args[5];
lean_object* v___y_971_ = _args[6];
lean_object* v___y_972_ = _args[7];
lean_object* v___y_973_ = _args[8];
lean_object* v___y_974_ = _args[9];
lean_object* v___y_975_ = _args[10];
lean_object* v___y_976_ = _args[11];
lean_object* v___y_977_ = _args[12];
lean_object* v___y_978_ = _args[13];
lean_object* v___y_979_ = _args[14];
lean_object* v___y_980_ = _args[15];
lean_object* v___y_981_ = _args[16];
_start:
{
size_t v_sz_boxed_982_; size_t v_i_boxed_983_; lean_object* v_res_984_; 
v_sz_boxed_982_ = lean_unbox_usize(v_sz_966_);
lean_dec(v_sz_966_);
v_i_boxed_983_ = lean_unbox_usize(v_i_967_);
lean_dec(v_i_967_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2(v_as_965_, v_sz_boxed_982_, v_i_boxed_983_, v_b_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec_ref(v_as_965_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4(lean_object* v_as_985_, size_t v_sz_986_, size_t v_i_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_lt(v_i_987_, v_sz_986_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v_b_988_);
return v___x_1003_;
}
else
{
lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v_b_988_);
v___x_1004_ = lean_st_ref_get(v___y_991_);
v_a_1005_ = lean_array_uget_borrowed(v_as_985_, v_i_987_);
lean_inc(v_a_1005_);
v___x_1006_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1004_, v_a_1005_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___x_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v_a_1010_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_box(0);
v___x_1015_ = lean_box(0);
v___x_1016_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1007_);
if (v___x_1016_ == 0)
{
lean_dec(v_a_1007_);
v_a_1010_ = v___x_1015_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1017_; 
lean_inc(v_a_1005_);
v___x_1017_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_a_1005_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
if (lean_obj_tag(v_a_1018_) == 1)
{
lean_object* v_val_1019_; uint8_t v___y_1021_; uint8_t v_heqProofs_1034_; 
v_val_1019_ = lean_ctor_get(v_a_1018_, 0);
lean_inc(v_val_1019_);
lean_dec_ref_known(v_a_1018_, 1);
v_heqProofs_1034_ = lean_ctor_get_uint8(v_a_1007_, sizeof(void*)*12 + 4);
lean_dec(v_a_1007_);
if (v_heqProofs_1034_ == 0)
{
v___y_1021_ = v___x_1016_;
goto v___jp_1020_;
}
else
{
uint8_t v___x_1035_; 
v___x_1035_ = 0;
v___y_1021_ = v___x_1035_;
goto v___jp_1020_;
}
v___jp_1020_:
{
lean_object* v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1022_ = lean_st_ref_get(v___y_991_);
v___x_1023_ = 0;
lean_inc(v_a_1005_);
v___x_1024_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1022_, v_a_1005_, v___x_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_1019_, v___y_1021_, v___x_1024_, v___x_1015_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___x_1024_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_dec_ref_known(v___x_1025_, 1);
v_a_1010_ = v___x_1015_;
goto v___jp_1009_;
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
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
}
}
else
{
lean_dec(v_a_1018_);
lean_dec(v_a_1007_);
v_a_1010_ = v___x_1015_;
goto v___jp_1009_;
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v_a_1007_);
v_a_1036_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1017_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1017_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
v___jp_1009_:
{
lean_object* v___x_1011_; size_t v___x_1012_; size_t v___x_1013_; 
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1008_);
lean_ctor_set(v___x_1011_, 1, v_a_1010_);
v___x_1012_ = ((size_t)1ULL);
v___x_1013_ = lean_usize_add(v_i_987_, v___x_1012_);
v_i_987_ = v___x_1013_;
v_b_988_ = v___x_1011_;
goto _start;
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1006_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1006_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_as_1052_ = _args[0];
lean_object* v_sz_1053_ = _args[1];
lean_object* v_i_1054_ = _args[2];
lean_object* v_b_1055_ = _args[3];
lean_object* v___y_1056_ = _args[4];
lean_object* v___y_1057_ = _args[5];
lean_object* v___y_1058_ = _args[6];
lean_object* v___y_1059_ = _args[7];
lean_object* v___y_1060_ = _args[8];
lean_object* v___y_1061_ = _args[9];
lean_object* v___y_1062_ = _args[10];
lean_object* v___y_1063_ = _args[11];
lean_object* v___y_1064_ = _args[12];
lean_object* v___y_1065_ = _args[13];
lean_object* v___y_1066_ = _args[14];
lean_object* v___y_1067_ = _args[15];
lean_object* v___y_1068_ = _args[16];
_start:
{
size_t v_sz_boxed_1069_; size_t v_i_boxed_1070_; lean_object* v_res_1071_; 
v_sz_boxed_1069_ = lean_unbox_usize(v_sz_1053_);
lean_dec(v_sz_1053_);
v_i_boxed_1070_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_res_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4(v_as_1052_, v_sz_boxed_1069_, v_i_boxed_1070_, v_b_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v_as_1052_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3(lean_object* v_as_1075_, size_t v_sz_1076_, size_t v_i_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
uint8_t v___x_1092_; 
v___x_1092_ = lean_usize_dec_lt(v_i_1077_, v_sz_1076_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_b_1078_);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; lean_object* v_a_1095_; lean_object* v___x_1096_; 
lean_dec_ref(v_b_1078_);
v___x_1094_ = lean_st_ref_get(v___y_1081_);
v_a_1095_ = lean_array_uget_borrowed(v_as_1075_, v_i_1077_);
lean_inc(v_a_1095_);
v___x_1096_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1094_, v_a_1095_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___x_1094_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; uint8_t v___x_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_box(0);
v___x_1104_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1097_);
if (v___x_1104_ == 0)
{
lean_dec(v_a_1097_);
goto v___jp_1099_;
}
else
{
lean_object* v___x_1105_; 
lean_inc(v_a_1095_);
v___x_1105_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_analyzeClass(v_a_1095_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
if (lean_obj_tag(v_a_1106_) == 1)
{
lean_object* v_val_1107_; uint8_t v___y_1109_; uint8_t v_heqProofs_1122_; 
v_val_1107_ = lean_ctor_get(v_a_1106_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v_a_1106_, 1);
v_heqProofs_1122_ = lean_ctor_get_uint8(v_a_1097_, sizeof(void*)*12 + 4);
lean_dec(v_a_1097_);
if (v_heqProofs_1122_ == 0)
{
v___y_1109_ = v___x_1104_;
goto v___jp_1108_;
}
else
{
uint8_t v___x_1123_; 
v___x_1123_ = 0;
v___y_1109_ = v___x_1123_;
goto v___jp_1108_;
}
v___jp_1108_:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1110_ = lean_st_ref_get(v___y_1081_);
v___x_1111_ = 0;
lean_inc(v_a_1095_);
v___x_1112_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1110_, v_a_1095_, v___x_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_1107_, v___y_1109_, v___x_1112_, v___x_1098_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___x_1112_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
goto v___jp_1099_;
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_dec(v_a_1106_);
lean_dec(v_a_1097_);
goto v___jp_1099_;
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v_a_1097_);
v_a_1124_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1105_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1105_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
v___jp_1099_:
{
lean_object* v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3___closed__0));
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_add(v_i_1077_, v___x_1101_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3_spec__4(v_as_1075_, v_sz_1076_, v___x_1102_, v___x_1100_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1103_;
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1096_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1096_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3___boxed(lean_object** _args){
lean_object* v_as_1140_ = _args[0];
lean_object* v_sz_1141_ = _args[1];
lean_object* v_i_1142_ = _args[2];
lean_object* v_b_1143_ = _args[3];
lean_object* v___y_1144_ = _args[4];
lean_object* v___y_1145_ = _args[5];
lean_object* v___y_1146_ = _args[6];
lean_object* v___y_1147_ = _args[7];
lean_object* v___y_1148_ = _args[8];
lean_object* v___y_1149_ = _args[9];
lean_object* v___y_1150_ = _args[10];
lean_object* v___y_1151_ = _args[11];
lean_object* v___y_1152_ = _args[12];
lean_object* v___y_1153_ = _args[13];
lean_object* v___y_1154_ = _args[14];
lean_object* v___y_1155_ = _args[15];
lean_object* v___y_1156_ = _args[16];
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1141_);
lean_dec(v_sz_1141_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3(v_as_1140_, v_sz_boxed_1157_, v_i_boxed_1158_, v_b_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec_ref(v_as_1140_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(lean_object* v_init_1160_, lean_object* v_n_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
if (lean_obj_tag(v_n_1161_) == 0)
{
lean_object* v_cs_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; size_t v_sz_1179_; size_t v___x_1180_; lean_object* v___x_1181_; 
v_cs_1176_ = lean_ctor_get(v_n_1161_, 0);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v_b_1162_);
v_sz_1179_ = lean_array_size(v_cs_1176_);
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2(v_init_1160_, v_cs_1176_, v_sz_1179_, v___x_1180_, v___x_1178_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1196_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1196_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1196_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_fst_1186_; 
v_fst_1186_ = lean_ctor_get(v_a_1182_, 0);
if (lean_obj_tag(v_fst_1186_) == 0)
{
lean_object* v_snd_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v_snd_1187_ = lean_ctor_get(v_a_1182_, 1);
lean_inc(v_snd_1187_);
lean_dec(v_a_1182_);
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_snd_1187_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1188_);
v___x_1190_ = v___x_1184_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; 
lean_inc_ref(v_fst_1186_);
lean_dec(v_a_1182_);
v_val_1192_ = lean_ctor_get(v_fst_1186_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v_fst_1186_, 1);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v_val_1192_);
v___x_1194_ = v___x_1184_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_val_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1181_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1181_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_vs_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; size_t v_sz_1208_; size_t v___x_1209_; lean_object* v___x_1210_; 
v_vs_1205_ = lean_ctor_get(v_n_1161_, 0);
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v_b_1162_);
v_sz_1208_ = lean_array_size(v_vs_1205_);
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__3(v_vs_1205_, v_sz_1208_, v___x_1209_, v___x_1207_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1225_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1225_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1225_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_fst_1215_; 
v_fst_1215_ = lean_ctor_get(v_a_1211_, 0);
if (lean_obj_tag(v_fst_1215_) == 0)
{
lean_object* v_snd_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v_snd_1216_ = lean_ctor_get(v_a_1211_, 1);
lean_inc(v_snd_1216_);
lean_dec(v_a_1211_);
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_snd_1216_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1217_);
v___x_1219_ = v___x_1213_;
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
else
{
lean_object* v_val_1221_; lean_object* v___x_1223_; 
lean_inc_ref(v_fst_1215_);
lean_dec(v_a_1211_);
v_val_1221_ = lean_ctor_get(v_fst_1215_, 0);
lean_inc(v_val_1221_);
lean_dec_ref_known(v_fst_1215_, 1);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_val_1221_);
v___x_1223_ = v___x_1213_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_val_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1210_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1210_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2(lean_object* v_init_1234_, lean_object* v_as_1235_, size_t v_sz_1236_, size_t v_i_1237_, lean_object* v_b_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_b_1238_);
return v___x_1253_;
}
else
{
lean_object* v_snd_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1288_; 
v_snd_1254_ = lean_ctor_get(v_b_1238_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_b_1238_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_b_1238_, 0);
lean_dec(v_unused_1289_);
v___x_1256_ = v_b_1238_;
v_isShared_1257_ = v_isSharedCheck_1288_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1254_);
lean_dec(v_b_1238_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1288_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_a_1258_; lean_object* v___x_1259_; 
v_a_1258_ = lean_array_uget_borrowed(v_as_1235_, v_i_1237_);
lean_inc(v_snd_1254_);
v___x_1259_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(v_init_1234_, v_a_1258_, v_snd_1254_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1279_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1279_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1279_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
if (lean_obj_tag(v_a_1260_) == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_a_1260_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1264_);
v___x_1266_ = v___x_1256_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_snd_1254_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1266_);
v___x_1268_ = v___x_1262_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
lean_del_object(v___x_1262_);
lean_dec(v_snd_1254_);
v_a_1271_ = lean_ctor_get(v_a_1260_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v_a_1260_, 1);
v___x_1272_ = lean_box(0);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_a_1271_);
lean_ctor_set(v___x_1256_, 0, v___x_1272_);
v___x_1274_ = v___x_1256_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_a_1271_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
size_t v___x_1275_; size_t v___x_1276_; 
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_add(v_i_1237_, v___x_1275_);
v_i_1237_ = v___x_1276_;
v_b_1238_ = v___x_1274_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
v_a_1280_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1259_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1259_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_init_1290_ = _args[0];
lean_object* v_as_1291_ = _args[1];
lean_object* v_sz_1292_ = _args[2];
lean_object* v_i_1293_ = _args[3];
lean_object* v_b_1294_ = _args[4];
lean_object* v___y_1295_ = _args[5];
lean_object* v___y_1296_ = _args[6];
lean_object* v___y_1297_ = _args[7];
lean_object* v___y_1298_ = _args[8];
lean_object* v___y_1299_ = _args[9];
lean_object* v___y_1300_ = _args[10];
lean_object* v___y_1301_ = _args[11];
lean_object* v___y_1302_ = _args[12];
lean_object* v___y_1303_ = _args[13];
lean_object* v___y_1304_ = _args[14];
lean_object* v___y_1305_ = _args[15];
lean_object* v___y_1306_ = _args[16];
lean_object* v___y_1307_ = _args[17];
_start:
{
size_t v_sz_boxed_1308_; size_t v_i_boxed_1309_; lean_object* v_res_1310_; 
v_sz_boxed_1308_ = lean_unbox_usize(v_sz_1292_);
lean_dec(v_sz_1292_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1293_);
lean_dec(v_i_1293_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1_spec__2(v_init_1290_, v_as_1291_, v_sz_boxed_1308_, v_i_boxed_1309_, v_b_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec_ref(v_as_1291_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1___boxed(lean_object* v_init_1311_, lean_object* v_n_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(v_init_1311_, v_n_1312_, v_b_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v_n_1312_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(lean_object* v_t_1328_, lean_object* v_init_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_root_1343_; lean_object* v_tail_1344_; lean_object* v___x_1345_; 
v_root_1343_ = lean_ctor_get(v_t_1328_, 0);
v_tail_1344_ = lean_ctor_get(v_t_1328_, 1);
v___x_1345_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__1(v_init_1329_, v_root_1343_, v_init_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1382_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1382_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1382_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
if (lean_obj_tag(v_a_1346_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v_a_1346_, 1);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v_a_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; size_t v_sz_1357_; size_t v___x_1358_; lean_object* v___x_1359_; 
lean_del_object(v___x_1348_);
v_a_1354_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v_a_1346_, 1);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v_a_1354_);
v_sz_1357_ = lean_array_size(v_tail_1344_);
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1_spec__2(v_tail_1344_, v_sz_1357_, v___x_1358_, v___x_1356_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1373_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1373_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1373_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_fst_1364_; 
v_fst_1364_ = lean_ctor_get(v_a_1360_, 0);
if (lean_obj_tag(v_fst_1364_) == 0)
{
lean_object* v_snd_1365_; lean_object* v___x_1367_; 
v_snd_1365_ = lean_ctor_get(v_a_1360_, 1);
lean_inc(v_snd_1365_);
lean_dec(v_a_1360_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_snd_1365_);
v___x_1367_ = v___x_1362_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_snd_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1371_; 
lean_inc_ref(v_fst_1364_);
lean_dec(v_a_1360_);
v_val_1369_ = lean_ctor_get(v_fst_1364_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v_fst_1364_, 1);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_val_1369_);
v___x_1371_ = v___x_1362_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_val_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1359_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1359_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1383_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1345_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1345_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1___boxed(lean_object* v_t_1391_, lean_object* v_init_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(v_t_1391_, v_init_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec_ref(v_t_1391_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_1409_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = lean_box(0);
v___x_1423_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__1(v_a_1421_, v___x_1422_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
lean_dec(v_a_1421_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v___x_1423_, 0);
lean_dec(v_unused_1431_);
v___x_1425_ = v___x_1423_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_dec(v___x_1423_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1422_);
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1422_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
else
{
return v___x_1423_;
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1432_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1420_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1420_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities___boxed(lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(lean_object* v_val_1454_, uint8_t v___y_1455_, lean_object* v_as_1456_, lean_object* v_as_x27_1457_, lean_object* v_b_1458_, lean_object* v_a_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_1454_, v___y_1455_, v_as_x27_1457_, v_b_1458_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___boxed(lean_object** _args){
lean_object* v_val_1474_ = _args[0];
lean_object* v___y_1475_ = _args[1];
lean_object* v_as_1476_ = _args[2];
lean_object* v_as_x27_1477_ = _args[3];
lean_object* v_b_1478_ = _args[4];
lean_object* v_a_1479_ = _args[5];
lean_object* v___y_1480_ = _args[6];
lean_object* v___y_1481_ = _args[7];
lean_object* v___y_1482_ = _args[8];
lean_object* v___y_1483_ = _args[9];
lean_object* v___y_1484_ = _args[10];
lean_object* v___y_1485_ = _args[11];
lean_object* v___y_1486_ = _args[12];
lean_object* v___y_1487_ = _args[13];
lean_object* v___y_1488_ = _args[14];
lean_object* v___y_1489_ = _args[15];
lean_object* v___y_1490_ = _args[16];
lean_object* v___y_1491_ = _args[17];
lean_object* v___y_1492_ = _args[18];
_start:
{
uint8_t v___y_47738__boxed_1493_; lean_object* v_res_1494_; 
v___y_47738__boxed_1493_ = lean_unbox(v___y_1475_);
v_res_1494_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(v_val_1474_, v___y_47738__boxed_1493_, v_as_1476_, v_as_x27_1477_, v_b_1478_, v_a_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v_as_x27_1477_);
lean_dec(v_as_1476_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(lean_object* v_a_1495_, lean_object* v_as_x27_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
if (lean_obj_tag(v_as_x27_1496_) == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_b_1497_);
return v___x_1510_;
}
else
{
lean_object* v_head_1511_; lean_object* v_tail_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_head_1511_ = lean_ctor_get(v_as_x27_1496_, 0);
v_tail_1512_ = lean_ctor_get(v_as_x27_1496_, 1);
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_expr_eqv(v_head_1511_, v_a_1495_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_inc(v_head_1511_);
v___x_1515_ = l_Lean_mkNot(v_head_1511_);
v___x_1516_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1515_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
lean_inc(v_head_1511_);
v___x_1518_ = l_Lean_Meta_Grind_mkEqFalseProof(v_head_1511_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = l_Lean_Meta_mkOfEqFalse(v_a_1519_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1522_ = lean_st_ref_take(v___y_1498_);
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_box(4);
v___x_1525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v_a_1517_);
lean_ctor_set(v___x_1525_, 2, v_a_1521_);
lean_ctor_set(v___x_1525_, 3, v___x_1524_);
v___x_1526_ = lean_array_push(v___x_1522_, v___x_1525_);
v___x_1527_ = lean_st_ref_put(v___y_1498_, v___x_1526_);
v_as_x27_1496_ = v_tail_1512_;
v_b_1497_ = v___x_1513_;
goto _start;
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_a_1517_);
v_a_1529_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1520_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1520_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v_a_1517_);
v_a_1537_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1518_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1518_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
v_a_1545_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1516_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1516_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
v_as_x27_1496_ = v_tail_1512_;
v_b_1497_ = v___x_1513_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg___boxed(lean_object* v_a_1554_, lean_object* v_as_x27_1555_, lean_object* v_b_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_1554_, v_as_x27_1555_, v_b_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v_as_x27_1555_);
lean_dec_ref(v_a_1554_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1576_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc_n(v_a_1584_, 2);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_st_ref_get(v_a_1572_);
v___x_1586_ = 0;
v___x_1587_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1585_, v_a_1584_, v___x_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v___x_1589_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_1584_, v___x_1587_, v___x_1588_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v___x_1587_);
lean_dec(v_a_1584_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v___x_1589_, 0);
lean_dec(v_unused_1597_);
v___x_1591_ = v___x_1589_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_dec(v___x_1589_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1588_);
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1588_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
else
{
return v___x_1589_;
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_a_1598_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1583_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1583_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse___boxed(lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0(lean_object* v_a_1620_, lean_object* v_as_1621_, lean_object* v_as_x27_1622_, lean_object* v_b_1623_, lean_object* v_a_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___redArg(v_a_1620_, v_as_x27_1622_, v_b_1623_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0___boxed(lean_object** _args){
lean_object* v_a_1639_ = _args[0];
lean_object* v_as_1640_ = _args[1];
lean_object* v_as_x27_1641_ = _args[2];
lean_object* v_b_1642_ = _args[3];
lean_object* v_a_1643_ = _args[4];
lean_object* v___y_1644_ = _args[5];
lean_object* v___y_1645_ = _args[6];
lean_object* v___y_1646_ = _args[7];
lean_object* v___y_1647_ = _args[8];
lean_object* v___y_1648_ = _args[9];
lean_object* v___y_1649_ = _args[10];
lean_object* v___y_1650_ = _args[11];
lean_object* v___y_1651_ = _args[12];
lean_object* v___y_1652_ = _args[13];
lean_object* v___y_1653_ = _args[14];
lean_object* v___y_1654_ = _args[15];
lean_object* v___y_1655_ = _args[16];
lean_object* v___y_1656_ = _args[17];
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse_spec__0(v_a_1639_, v_as_1640_, v_as_x27_1641_, v_b_1642_, v_a_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v_as_x27_1641_);
lean_dec(v_as_1640_);
lean_dec_ref(v_a_1639_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(lean_object* v_a_1658_, lean_object* v_as_x27_1659_, lean_object* v_b_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
if (lean_obj_tag(v_as_x27_1659_) == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_b_1660_);
return v___x_1673_;
}
else
{
lean_object* v_head_1674_; lean_object* v_tail_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v_head_1674_ = lean_ctor_get(v_as_x27_1659_, 0);
v_tail_1675_ = lean_ctor_get(v_as_x27_1659_, 1);
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_expr_eqv(v_head_1674_, v_a_1658_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; 
lean_inc(v_head_1674_);
v___x_1678_ = l_Lean_Meta_Grind_mkEqTrueProof(v_head_1674_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1680_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1678_, 1);
v___x_1680_ = l_Lean_Meta_mkOfEqTrue(v_a_1679_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v___x_1682_ = lean_st_ref_take(v___y_1661_);
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_box(4);
lean_inc(v_head_1674_);
v___x_1685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v_head_1674_);
lean_ctor_set(v___x_1685_, 2, v_a_1681_);
lean_ctor_set(v___x_1685_, 3, v___x_1684_);
v___x_1686_ = lean_array_push(v___x_1682_, v___x_1685_);
v___x_1687_ = lean_st_ref_put(v___y_1661_, v___x_1686_);
v_as_x27_1659_ = v_tail_1675_;
v_b_1660_ = v___x_1676_;
goto _start;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1680_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1680_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
v_a_1697_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1678_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1678_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
v_as_x27_1659_ = v_tail_1675_;
v_b_1660_ = v___x_1676_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg___boxed(lean_object* v_a_1706_, lean_object* v_as_x27_1707_, lean_object* v_b_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1706_, v_as_x27_1707_, v_b_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec(v_as_x27_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1728_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc_n(v_a_1736_, 2);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = lean_st_ref_get(v_a_1724_);
v___x_1738_ = 0;
v___x_1739_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_1737_, v_a_1736_, v___x_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v___x_1741_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1736_, v___x_1739_, v___x_1740_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v___x_1739_);
lean_dec(v_a_1736_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; 
v_unused_1749_ = lean_ctor_get(v___x_1741_, 0);
lean_dec(v_unused_1749_);
v___x_1743_ = v___x_1741_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v___x_1741_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1740_);
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1740_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
else
{
return v___x_1741_;
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
v_a_1750_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1735_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1735_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue___boxed(lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0(lean_object* v_a_1772_, lean_object* v_as_1773_, lean_object* v_as_x27_1774_, lean_object* v_b_1775_, lean_object* v_a_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___redArg(v_a_1772_, v_as_x27_1774_, v_b_1775_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0___boxed(lean_object** _args){
lean_object* v_a_1791_ = _args[0];
lean_object* v_as_1792_ = _args[1];
lean_object* v_as_x27_1793_ = _args[2];
lean_object* v_b_1794_ = _args[3];
lean_object* v_a_1795_ = _args[4];
lean_object* v___y_1796_ = _args[5];
lean_object* v___y_1797_ = _args[6];
lean_object* v___y_1798_ = _args[7];
lean_object* v___y_1799_ = _args[8];
lean_object* v___y_1800_ = _args[9];
lean_object* v___y_1801_ = _args[10];
lean_object* v___y_1802_ = _args[11];
lean_object* v___y_1803_ = _args[12];
lean_object* v___y_1804_ = _args[13];
lean_object* v___y_1805_ = _args[14];
lean_object* v___y_1806_ = _args[15];
lean_object* v___y_1807_ = _args[16];
lean_object* v___y_1808_ = _args[17];
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue_spec__0(v_a_1791_, v_as_1792_, v_as_x27_1793_, v_b_1794_, v_a_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v_as_x27_1793_);
lean_dec(v_as_1792_);
lean_dec_ref(v_a_1791_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectTrue(v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v___x_1824_; 
lean_dec_ref_known(v___x_1823_, 1);
v___x_1824_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectFalse(v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1825_; 
lean_dec_ref_known(v___x_1824_, 1);
v___x_1825_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities(v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1826_; 
lean_dec_ref_known(v___x_1825_, 1);
v___x_1826_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits___redArg(v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1826_;
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
else
{
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go___boxed(lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(lean_object* v_cfg_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0));
v___x_1856_ = lean_st_mk_ref(v___x_1855_);
v___x_1857_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_go(v_cfg_1843_, v___x_1856_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1865_; 
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; 
v_unused_1866_ = lean_ctor_get(v___x_1857_, 0);
lean_dec(v_unused_1866_);
v___x_1859_ = v___x_1857_;
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
else
{
lean_dec(v___x_1857_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = lean_st_ref_get(v___x_1856_);
lean_dec(v___x_1856_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v___x_1856_);
v_a_1867_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1857_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1857_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___boxed(lean_object* v_cfg_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(v_cfg_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_cfg_1875_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordLocalHyp(lean_object* v_fvarId_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1896_; 
lean_inc(v_fvarId_1888_);
v___x_1896_ = l_Lean_FVarId_getUserName___redArg(v_fvarId_1888_, v_a_1891_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
lean_inc(v_fvarId_1888_);
v___x_1898_ = l_Lean_FVarId_getType___redArg(v_fvarId_1888_, v_a_1891_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_1899_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1911_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_inc(v_fvarId_1888_);
v___x_1905_ = l_Lean_mkFVar(v_fvarId_1888_);
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_fvarId_1888_);
v___x_1907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1907_, 0, v_a_1897_);
lean_ctor_set(v___x_1907_, 1, v_a_1901_);
lean_ctor_set(v___x_1907_, 2, v___x_1905_);
lean_ctor_set(v___x_1907_, 3, v___x_1906_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1907_);
v___x_1909_ = v___x_1903_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_a_1897_);
lean_dec(v_fvarId_1888_);
v_a_1912_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1900_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1900_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_a_1897_);
lean_dec(v_fvarId_1888_);
v_a_1920_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1898_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1898_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_fvarId_1888_);
v_a_1928_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1896_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1896_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordLocalHyp___boxed(lean_object* v_fvarId_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_recordLocalHyp(v_fvarId_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
return v_res_1944_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1(lean_object* v_msg_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_6181__overap_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0);
v___x_6181__overap_1955_ = lean_panic_fn_borrowed(v___x_1954_, v_msg_1946_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
v___x_1956_ = lean_apply_7(v___x_6181__overap_1955_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, lean_box(0));
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___boxed(lean_object* v_msg_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1(v_msg_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0(lean_object* v_x_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
lean_inc(v___y_1968_);
lean_inc_ref(v___y_1967_);
v___x_1974_ = lean_apply_7(v_x_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, lean_box(0));
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0___boxed(lean_object* v_x_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0(v_x_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(lean_object* v_mvarId_1984_, lean_object* v_x_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v___f_1993_; lean_object* v___x_1994_; 
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
v___f_1993_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1993_, 0, v_x_1985_);
lean_closure_set(v___f_1993_, 1, v___y_1986_);
lean_closure_set(v___f_1993_, 2, v___y_1987_);
v___x_1994_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1984_, v___f_1993_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1994_) == 0)
{
return v___x_1994_;
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg___boxed(lean_object* v_mvarId_2003_, lean_object* v_x_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(v_mvarId_2003_, v_x_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2(lean_object* v_00_u03b1_2013_, lean_object* v_mvarId_2014_, lean_object* v_x_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(v_mvarId_2014_, v_x_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_mvarId_2025_, lean_object* v_x_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2(v_00_u03b1_2024_, v_mvarId_2025_, v_x_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(lean_object* v_msgData_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v_env_2042_; lean_object* v___x_2043_; lean_object* v_toCold_2044_; lean_object* v_mctx_2045_; lean_object* v_lctx_2046_; lean_object* v_options_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2041_ = lean_st_ref_get(v___y_2039_);
v_env_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_ref(v_env_2042_);
lean_dec(v___x_2041_);
v___x_2043_ = lean_st_ref_get(v___y_2037_);
v_toCold_2044_ = lean_ctor_get(v___y_2038_, 0);
v_mctx_2045_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_ref(v_mctx_2045_);
lean_dec(v___x_2043_);
v_lctx_2046_ = lean_ctor_get(v___y_2036_, 2);
v_options_2047_ = lean_ctor_get(v_toCold_2044_, 2);
lean_inc_ref(v_options_2047_);
lean_inc_ref(v_lctx_2046_);
v___x_2048_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2048_, 0, v_env_2042_);
lean_ctor_set(v___x_2048_, 1, v_mctx_2045_);
lean_ctor_set(v___x_2048_, 2, v_lctx_2046_);
lean_ctor_set(v___x_2048_, 3, v_options_2047_);
v___x_2049_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v_msgData_2035_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0___boxed(lean_object* v_msgData_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msgData_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(lean_object* v_msg_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_ref_2064_; lean_object* v___x_2065_; lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2074_; 
v_ref_2064_ = lean_ctor_get(v___y_2061_, 2);
v___x_2065_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
lean_inc(v_ref_2064_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_ref_2064_);
lean_ctor_set(v___x_2070_, 1, v_a_2066_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 1);
lean_ctor_set(v___x_2068_, 0, v___x_2070_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg___boxed(lean_object* v_msg_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v_msg_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2081_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__0));
v___x_2084_ = l_Lean_stringToMessageData(v___x_2083_);
return v___x_2084_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__4));
v___x_2089_ = lean_unsigned_to_nat(37u);
v___x_2090_ = lean_unsigned_to_nat(200u);
v___x_2091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__3));
v___x_2092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__2));
v___x_2093_ = l_mkPanicMessageWithDecl(v___x_2092_, v___x_2091_, v___x_2090_, v___x_2089_, v___x_2088_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0(lean_object* v_snd_2094_, lean_object* v_fst_2095_, uint8_t v___x_2096_, lean_object* v_____x_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
lean_inc(v_snd_2094_);
v___x_2105_ = l_Lean_MVarId_getType(v_snd_2094_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc_n(v_a_2106_, 2);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = l_Lean_Meta_isProp(v_a_2106_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2198_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2198_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2198_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_unbox(v_a_2108_);
lean_dec(v_a_2108_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
lean_del_object(v___x_2110_);
lean_dec(v_a_2106_);
lean_dec_ref(v_____x_2097_);
v___x_2113_ = l_Lean_MVarId_exfalso(v_snd_2094_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l_Lean_Meta_Sym_preprocessMVar(v_a_2114_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2124_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_fst_2095_);
lean_ctor_set(v___x_2120_, 1, v_a_2116_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v_fst_2095_);
v_a_2125_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2115_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2115_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_fst_2095_);
v_a_2133_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2113_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2113_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
uint8_t v___x_2141_; 
v___x_2141_ = l_Lean_Expr_isFalse(v_a_2106_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_del_object(v___x_2110_);
lean_dec_ref(v_____x_2097_);
v___x_2142_ = l_Lean_MVarId_byContra_x3f(v_snd_2094_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
if (lean_obj_tag(v_a_2143_) == 1)
{
lean_object* v_val_2144_; lean_object* v___x_2145_; 
v_val_2144_ = lean_ctor_get(v_a_2143_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v_a_2143_, 1);
v___x_2145_ = l_Lean_Meta_Sym_preprocessMVar(v_val_2144_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = l_Lean_Meta_Sym_introN(v_a_2146_, v___x_2147_, v___x_2096_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2168_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2168_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2168_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
if (lean_obj_tag(v_a_2149_) == 1)
{
lean_object* v_newDecls_2153_; lean_object* v_mvarId_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2165_; 
v_newDecls_2153_ = lean_ctor_get(v_a_2149_, 0);
v_mvarId_2154_ = lean_ctor_get(v_a_2149_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_a_2149_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2156_ = v_a_2149_;
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_mvarId_2154_);
lean_inc(v_newDecls_2153_);
lean_dec(v_a_2149_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = l_Array_append___redArg(v_fst_2095_, v_newDecls_2153_);
lean_dec_ref(v_newDecls_2153_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2158_);
v___x_2160_ = v___x_2156_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_mvarId_2154_);
v___x_2160_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2162_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2160_);
v___x_2162_ = v___x_2151_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_del_object(v___x_2151_);
lean_dec(v_a_2149_);
lean_dec_ref(v_fst_2095_);
v___x_2166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1);
v___x_2167_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v___x_2166_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
return v___x_2167_;
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec_ref(v_fst_2095_);
v_a_2169_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2148_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2148_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec_ref(v_fst_2095_);
v_a_2177_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2145_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2145_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v_a_2143_);
lean_dec_ref(v_fst_2095_);
v___x_2185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5);
v___x_2186_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1(v___x_2185_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
return v___x_2186_;
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec_ref(v_fst_2095_);
v_a_2187_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2142_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2142_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_object* v___x_2196_; 
lean_dec_ref(v_fst_2095_);
lean_dec(v_snd_2094_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v_____x_2097_);
v___x_2196_ = v___x_2110_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_____x_2097_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_a_2106_);
lean_dec_ref(v_____x_2097_);
lean_dec_ref(v_fst_2095_);
lean_dec(v_snd_2094_);
v_a_2199_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2107_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2107_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v_____x_2097_);
lean_dec_ref(v_fst_2095_);
lean_dec(v_snd_2094_);
v_a_2207_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2105_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2105_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___boxed(lean_object* v_snd_2215_, lean_object* v_fst_2216_, lean_object* v___x_2217_, lean_object* v_____x_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
uint8_t v___x_7874__boxed_2226_; lean_object* v_res_2227_; 
v___x_7874__boxed_2226_ = lean_unbox(v___x_2217_);
v_res_2227_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0(v_snd_2215_, v_fst_2216_, v___x_7874__boxed_2226_, v_____x_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(lean_object* v_goal_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0));
v___x_2239_ = 1;
lean_inc(v_goal_2230_);
v___x_2240_ = l_Lean_Meta_Sym_intros(v_goal_2230_, v___x_2238_, v___x_2239_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v_____x_2243_; lean_object* v_fst_2244_; lean_object* v_snd_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
if (lean_obj_tag(v_a_2241_) == 0)
{
lean_object* v___x_2255_; 
lean_inc(v_goal_2230_);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2238_);
lean_ctor_set(v___x_2255_, 1, v_goal_2230_);
v_____x_2243_ = v___x_2255_;
v_fst_2244_ = v___x_2238_;
v_snd_2245_ = v_goal_2230_;
v___y_2246_ = v_a_2231_;
v___y_2247_ = v_a_2232_;
v___y_2248_ = v_a_2233_;
v___y_2249_ = v_a_2234_;
v___y_2250_ = v_a_2235_;
v___y_2251_ = v_a_2236_;
goto v___jp_2242_;
}
else
{
lean_object* v_newDecls_2256_; lean_object* v_mvarId_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_goal_2230_);
v_newDecls_2256_ = lean_ctor_get(v_a_2241_, 0);
v_mvarId_2257_ = lean_ctor_get(v_a_2241_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_a_2241_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v_a_2241_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_mvarId_2257_);
lean_inc(v_newDecls_2256_);
lean_dec(v_a_2241_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
lean_inc(v_mvarId_2257_);
lean_inc_ref(v_newDecls_2256_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 0);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_newDecls_2256_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_mvarId_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
v_____x_2243_ = v___x_2262_;
v_fst_2244_ = v_newDecls_2256_;
v_snd_2245_ = v_mvarId_2257_;
v___y_2246_ = v_a_2231_;
v___y_2247_ = v_a_2232_;
v___y_2248_ = v_a_2233_;
v___y_2249_ = v_a_2234_;
v___y_2250_ = v_a_2235_;
v___y_2251_ = v_a_2236_;
goto v___jp_2242_;
}
}
}
v___jp_2242_:
{
lean_object* v___x_2252_; lean_object* v___f_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_box(v___x_2239_);
lean_inc(v_snd_2245_);
v___f_2253_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2253_, 0, v_snd_2245_);
lean_closure_set(v___f_2253_, 1, v_fst_2244_);
lean_closure_set(v___f_2253_, 2, v___x_2252_);
lean_closure_set(v___f_2253_, 3, v_____x_2243_);
v___x_2254_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__2___redArg(v_snd_2245_, v___f_2253_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2254_;
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec(v_goal_2230_);
v_a_2265_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2240_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2240_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___boxed(lean_object* v_goal_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_goal_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec(v_a_2275_);
lean_dec_ref(v_a_2274_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0(lean_object* v_00_u03b1_2282_, lean_object* v_msg_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v_msg_2283_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_msg_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0(v_00_u03b1_2292_, v_msg_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(lean_object* v_goal_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_toGoalState_2310_; lean_object* v_mvarId_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2344_; 
v_toGoalState_2310_ = lean_ctor_get(v_goal_2302_, 0);
v_mvarId_2311_ = lean_ctor_get(v_goal_2302_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_goal_2302_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2313_ = v_goal_2302_;
v_isShared_2314_ = v_isSharedCheck_2344_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_mvarId_2311_);
lean_inc(v_toGoalState_2310_);
lean_dec(v_goal_2302_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2344_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; 
v___x_2315_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_mvarId_2311_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2335_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2335_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2335_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_fst_2320_; lean_object* v_snd_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2334_; 
v_fst_2320_ = lean_ctor_get(v_a_2316_, 0);
v_snd_2321_ = lean_ctor_get(v_a_2316_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2316_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2323_ = v_a_2316_;
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_snd_2321_);
lean_inc(v_fst_2320_);
lean_dec(v_a_2316_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v_snd_2321_);
v___x_2326_ = v___x_2313_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_toGoalState_2310_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_snd_2321_);
v___x_2326_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2328_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 1, v___x_2326_);
v___x_2328_ = v___x_2323_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_fst_2320_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2328_);
v___x_2330_ = v___x_2318_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_del_object(v___x_2313_);
lean_dec_ref(v_toGoalState_2310_);
v_a_2336_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2315_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2315_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg___boxed(lean_object* v_goal_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget(lean_object* v_goal_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2354_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___boxed(lean_object* v_goal_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget(v_goal_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0(lean_object* v_x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
lean_inc(v___y_2383_);
lean_inc_ref(v___y_2382_);
lean_inc(v___y_2381_);
lean_inc_ref(v___y_2380_);
lean_inc(v___y_2379_);
v___x_2389_ = lean_apply_10(v_x_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, lean_box(0));
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0___boxed(lean_object* v_x_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0(v_x_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(lean_object* v_mvarId_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___f_2414_; lean_object* v___x_2415_; 
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v___y_2406_);
lean_inc_ref(v___y_2405_);
lean_inc(v___y_2404_);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2414_, 0, v_x_2403_);
lean_closure_set(v___f_2414_, 1, v___y_2404_);
lean_closure_set(v___f_2414_, 2, v___y_2405_);
lean_closure_set(v___f_2414_, 3, v___y_2406_);
lean_closure_set(v___f_2414_, 4, v___y_2407_);
lean_closure_set(v___f_2414_, 5, v___y_2408_);
v___x_2415_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2402_, v___f_2414_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2415_) == 0)
{
return v___x_2415_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___boxed(lean_object* v_mvarId_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2424_, v_x_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1(lean_object* v_00_u03b1_2437_, lean_object* v_mvarId_2438_, lean_object* v_x_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2438_, v_x_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___boxed(lean_object* v_00_u03b1_2451_, lean_object* v_mvarId_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1(v_00_u03b1_2451_, v_mvarId_2452_, v_x_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0(lean_object* v_x_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; 
lean_inc(v___y_2472_);
lean_inc_ref(v___y_2471_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2469_);
lean_inc(v___y_2468_);
lean_inc(v___y_2467_);
lean_inc_ref(v___y_2466_);
v___x_2478_ = lean_apply_12(v_x_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, lean_box(0));
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0___boxed(lean_object* v_x_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0(v_x_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(lean_object* v_mvarId_2493_, lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___f_2507_; lean_object* v___x_2508_; 
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc(v___y_2499_);
lean_inc_ref(v___y_2498_);
lean_inc(v___y_2497_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
v___f_2507_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2507_, 0, v_x_2494_);
lean_closure_set(v___f_2507_, 1, v___y_2495_);
lean_closure_set(v___f_2507_, 2, v___y_2496_);
lean_closure_set(v___f_2507_, 3, v___y_2497_);
lean_closure_set(v___f_2507_, 4, v___y_2498_);
lean_closure_set(v___f_2507_, 5, v___y_2499_);
lean_closure_set(v___f_2507_, 6, v___y_2500_);
lean_closure_set(v___f_2507_, 7, v___y_2501_);
v___x_2508_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2493_, v___f_2507_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2508_) == 0)
{
return v___x_2508_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___boxed(lean_object* v_mvarId_2517_, lean_object* v_x_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_mvarId_2517_, v_x_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3(lean_object* v_00_u03b1_2532_, lean_object* v_mvarId_2533_, lean_object* v_x_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_mvarId_2533_, v_x_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___boxed(lean_object* v_00_u03b1_2548_, lean_object* v_mvarId_2549_, lean_object* v_x_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3(v_00_u03b1_2548_, v_mvarId_2549_, v_x_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(size_t v_sz_2564_, size_t v_i_2565_, lean_object* v_bs_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_usize_dec_lt(v_i_2565_, v_sz_2564_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_bs_2566_);
return v___x_2575_;
}
else
{
lean_object* v_v_2576_; lean_object* v___x_2577_; 
v_v_2576_ = lean_array_uget(v_bs_2566_, v_i_2565_);
lean_inc(v_v_2576_);
v___x_2577_ = l_Lean_FVarId_getUserName___redArg(v_v_2576_, v___y_2569_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2579_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
lean_inc(v_v_2576_);
v___x_2579_ = l_Lean_FVarId_getType___redArg(v_v_2576_, v___y_2569_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2581_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_2580_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; lean_object* v_bs_x27_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; size_t v___x_2588_; size_t v___x_2589_; lean_object* v___x_2590_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = lean_unsigned_to_nat(0u);
v_bs_x27_2584_ = lean_array_uset(v_bs_2566_, v_i_2565_, v___x_2583_);
lean_inc(v_v_2576_);
v___x_2585_ = l_Lean_mkFVar(v_v_2576_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_v_2576_);
v___x_2587_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2587_, 0, v_a_2578_);
lean_ctor_set(v___x_2587_, 1, v_a_2582_);
lean_ctor_set(v___x_2587_, 2, v___x_2585_);
lean_ctor_set(v___x_2587_, 3, v___x_2586_);
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_add(v_i_2565_, v___x_2588_);
v___x_2590_ = lean_array_uset(v_bs_x27_2584_, v_i_2565_, v___x_2587_);
v_i_2565_ = v___x_2589_;
v_bs_2566_ = v___x_2590_;
goto _start;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2578_);
lean_dec(v_v_2576_);
lean_dec_ref(v_bs_2566_);
v_a_2592_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2581_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2581_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_a_2578_);
lean_dec(v_v_2576_);
lean_dec_ref(v_bs_2566_);
v_a_2600_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2579_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2579_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v_v_2576_);
lean_dec_ref(v_bs_2566_);
v_a_2608_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2577_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2577_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg___boxed(lean_object* v_sz_2616_, lean_object* v_i_2617_, lean_object* v_bs_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
size_t v_sz_boxed_2626_; size_t v_i_boxed_2627_; lean_object* v_res_2628_; 
v_sz_boxed_2626_ = lean_unbox_usize(v_sz_2616_);
lean_dec(v_sz_2616_);
v_i_boxed_2627_ = lean_unbox_usize(v_i_2617_);
lean_dec(v_i_2617_);
v_res_2628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_boxed_2626_, v_i_boxed_2627_, v_bs_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_getPropHyps(v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; size_t v_sz_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v_sz_2643_ = lean_array_size(v_a_2642_);
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_2643_, v___x_2644_, v_a_2642_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2654_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2654_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2654_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_a_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v___x_2650_);
v___x_2652_ = v___x_2648_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
v_a_2655_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2645_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2645_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
v_a_2663_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2641_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2641_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed(lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(lean_object* v_as_2684_, size_t v_i_2685_, size_t v_stop_2686_, lean_object* v_b_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_a_2699_; uint8_t v___x_2703_; 
v___x_2703_ = lean_usize_dec_eq(v_i_2685_, v_stop_2686_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_array_uget_borrowed(v_as_2684_, v_i_2685_);
lean_inc(v___x_2704_);
v___x_2705_ = l_Lean_FVarId_getType___redArg(v___x_2704_, v___y_2693_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = l_Lean_Meta_isProp(v_a_2706_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; uint8_t v___x_2709_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v___x_2709_ = lean_unbox(v_a_2708_);
lean_dec(v_a_2708_);
if (v___x_2709_ == 0)
{
v_a_2699_ = v_b_2687_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2710_; 
lean_inc(v___x_2704_);
v___x_2710_ = l_Lean_FVarId_getUserName___redArg(v___x_2704_, v___y_2693_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
lean_inc(v___x_2704_);
v___x_2712_ = l_Lean_FVarId_getType___redArg(v___x_2704_, v___y_2693_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2714_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_2713_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2714_, 1);
lean_inc_n(v___x_2704_, 2);
v___x_2716_ = l_Lean_mkFVar(v___x_2704_);
v___x_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2704_);
v___x_2718_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2718_, 0, v_a_2711_);
lean_ctor_set(v___x_2718_, 1, v_a_2715_);
lean_ctor_set(v___x_2718_, 2, v___x_2716_);
lean_ctor_set(v___x_2718_, 3, v___x_2717_);
v___x_2719_ = lean_array_push(v_b_2687_, v___x_2718_);
v_a_2699_ = v___x_2719_;
goto v___jp_2698_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_b_2687_);
v_a_2720_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2714_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2714_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_b_2687_);
v_a_2728_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2712_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2712_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec_ref(v_b_2687_);
v_a_2736_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2710_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2710_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v_b_2687_);
v_a_2744_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2707_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2707_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref(v_b_2687_);
v_a_2752_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2705_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2705_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_b_2687_);
return v___x_2760_;
}
v___jp_2698_:
{
size_t v___x_2700_; size_t v___x_2701_; 
v___x_2700_ = ((size_t)1ULL);
v___x_2701_ = lean_usize_add(v_i_2685_, v___x_2700_);
v_i_2685_ = v___x_2701_;
v_b_2687_ = v_a_2699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg___boxed(lean_object* v_as_2761_, lean_object* v_i_2762_, lean_object* v_stop_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
size_t v_i_boxed_2775_; size_t v_stop_boxed_2776_; lean_object* v_res_2777_; 
v_i_boxed_2775_ = lean_unbox_usize(v_i_2762_);
lean_dec(v_i_2762_);
v_stop_boxed_2776_ = lean_unbox_usize(v_stop_2763_);
lean_dec(v_stop_2763_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2761_, v_i_boxed_2775_, v_stop_boxed_2776_, v_b_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v_as_2761_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(lean_object* v_as_2778_, lean_object* v_start_2779_, lean_object* v_stop_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0));
v___x_2793_ = lean_nat_dec_lt(v_start_2779_, v_stop_2780_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
return v___x_2794_;
}
else
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = lean_array_get_size(v_as_2778_);
v___x_2796_ = lean_nat_dec_le(v_stop_2780_, v___x_2795_);
if (v___x_2796_ == 0)
{
uint8_t v___x_2797_; 
v___x_2797_ = lean_nat_dec_lt(v_start_2779_, v___x_2795_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2792_);
return v___x_2798_;
}
else
{
size_t v___x_2799_; size_t v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_usize_of_nat(v_start_2779_);
v___x_2800_ = lean_usize_of_nat(v___x_2795_);
v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2778_, v___x_2799_, v___x_2800_, v___x_2792_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2801_;
}
}
else
{
size_t v___x_2802_; size_t v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = lean_usize_of_nat(v_start_2779_);
v___x_2803_ = lean_usize_of_nat(v_stop_2780_);
v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2778_, v___x_2802_, v___x_2803_, v___x_2792_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___boxed(lean_object* v_as_2805_, lean_object* v_start_2806_, lean_object* v_stop_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(v_as_2805_, v_start_2806_, v_stop_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec(v_stop_2807_);
lean_dec(v_start_2806_);
lean_dec_ref(v_as_2805_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(lean_object* v_snd_2820_, lean_object* v_config_2821_, lean_object* v_fst_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; lean_object* v_a_2835_; lean_object* v___y_2840_; lean_object* v___x_2850_; 
v___x_2833_ = lean_st_mk_ref(v_snd_2820_);
v___x_2850_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(v_config_2821_, v___x_2833_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = lean_unsigned_to_nat(0u);
v___x_2853_ = lean_array_get_size(v_fst_2822_);
v___x_2854_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(v_fst_2822_, v___x_2852_, v___x_2853_, v___x_2833_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = l_Array_append___redArg(v_a_2851_, v_a_2855_);
lean_dec(v_a_2855_);
v_a_2835_ = v___x_2856_;
goto v___jp_2834_;
}
else
{
lean_dec(v_a_2851_);
v___y_2840_ = v___x_2854_;
goto v___jp_2839_;
}
}
else
{
v___y_2840_ = v___x_2850_;
goto v___jp_2839_;
}
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_st_ref_get(v___x_2833_);
lean_dec(v___x_2833_);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v_a_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
v___jp_2839_:
{
if (lean_obj_tag(v___y_2840_) == 0)
{
lean_object* v_a_2841_; 
v_a_2841_ = lean_ctor_get(v___y_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___y_2840_, 1);
v_a_2835_ = v_a_2841_;
goto v___jp_2834_;
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v___x_2833_);
v_a_2842_ = lean_ctor_get(v___y_2840_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___y_2840_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___y_2840_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___y_2840_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed(lean_object* v_snd_2857_, lean_object* v_config_2858_, lean_object* v_fst_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(v_snd_2857_, v_config_2858_, v_fst_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v_fst_2859_);
lean_dec_ref(v_config_2858_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_fst_2885_; lean_object* v_snd_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___x_2940_; lean_object* v_target_2941_; 
v___x_2940_ = lean_st_ref_get(v_a_2873_);
v_target_2941_ = lean_ctor_get(v___x_2940_, 2);
lean_inc_ref(v_target_2941_);
lean_dec(v___x_2940_);
if (lean_obj_tag(v_target_2941_) == 0)
{
lean_object* v_mvar_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2986_; 
v_mvar_2942_ = lean_ctor_get(v_target_2941_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_target_2941_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2944_ = v_target_2941_;
v_isShared_2945_ = v_isSharedCheck_2986_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_mvar_2942_);
lean_dec(v_target_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2986_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; 
v___x_2946_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_mvar_2942_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v_snd_2948_; lean_object* v___x_2949_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v_snd_2948_ = lean_ctor_get(v_a_2947_, 1);
lean_inc(v_snd_2948_);
lean_dec(v_a_2947_);
v___x_2949_ = l_Lean_Meta_Sym_preprocessMVar(v_snd_2948_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v_caches_2952_; lean_object* v_typeAnalysis_2953_; lean_object* v_hypotheses_2954_; uint8_t v_didChange_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2968_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = lean_st_ref_take(v_a_2873_);
v_caches_2952_ = lean_ctor_get(v___x_2951_, 0);
v_typeAnalysis_2953_ = lean_ctor_get(v___x_2951_, 1);
v_hypotheses_2954_ = lean_ctor_get(v___x_2951_, 3);
v_didChange_2955_ = lean_ctor_get_uint8(v___x_2951_, sizeof(void*)*4);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v___x_2951_, 2);
lean_dec(v_unused_2969_);
v___x_2957_ = v___x_2951_;
v_isShared_2958_ = v_isSharedCheck_2968_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_hypotheses_2954_);
lean_inc(v_typeAnalysis_2953_);
lean_inc(v_caches_2952_);
lean_dec(v___x_2951_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2968_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
lean_inc(v_a_2950_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v_a_2950_);
v___x_2960_ = v___x_2944_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2950_);
v___x_2960_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2962_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 2, v___x_2960_);
v___x_2962_ = v___x_2957_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_caches_2952_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_typeAnalysis_2953_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_hypotheses_2954_);
lean_ctor_set_uint8(v_reuseFailAlloc_2966_, sizeof(void*)*4, v_didChange_2955_);
v___x_2962_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_st_ref_put(v_a_2873_, v___x_2962_);
v___f_2964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0));
v___x_2965_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_a_2950_, v___f_2964_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_del_object(v___x_2944_);
v_a_2970_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2949_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2949_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_del_object(v___x_2944_);
v_a_2978_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2946_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2946_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
else
{
lean_object* v_goal_2987_; lean_object* v_mode_2988_; uint8_t v___x_2989_; 
v_goal_2987_ = lean_ctor_get(v_target_2941_, 0);
lean_inc_ref(v_goal_2987_);
lean_dec_ref_known(v_target_2941_, 1);
v_mode_2988_ = lean_ctor_get(v_a_2872_, 1);
v___x_2989_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
v___x_2990_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2987_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v_fst_2992_; lean_object* v_snd_2993_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v_fst_2992_ = lean_ctor_get(v_a_2991_, 0);
lean_inc(v_fst_2992_);
v_snd_2993_ = lean_ctor_get(v_a_2991_, 1);
lean_inc(v_snd_2993_);
lean_dec(v_a_2991_);
v_fst_2885_ = v_fst_2992_;
v_snd_2886_ = v_snd_2993_;
v___y_2887_ = v_a_2872_;
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
goto v___jp_2884_;
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_a_2994_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2990_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2990_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
else
{
lean_object* v___x_3002_; 
v___x_3002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0));
v_fst_2885_ = v___x_3002_;
v_snd_2886_ = v_goal_2987_;
v___y_2887_ = v_a_2872_;
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
goto v___jp_2884_;
}
}
v___jp_2884_:
{
lean_object* v_toGoalState_2898_; uint8_t v_inconsistent_2899_; 
v_toGoalState_2898_ = lean_ctor_get(v_snd_2886_, 0);
v_inconsistent_2899_ = lean_ctor_get_uint8(v_toGoalState_2898_, sizeof(void*)*17);
if (v_inconsistent_2899_ == 0)
{
lean_object* v_mvarId_2900_; lean_object* v_config_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; 
v_mvarId_2900_ = lean_ctor_get(v_snd_2886_, 1);
lean_inc(v_mvarId_2900_);
v_config_2901_ = lean_ctor_get(v___y_2887_, 0);
lean_inc_ref(v_config_2901_);
v___f_2902_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed), 13, 3);
lean_closure_set(v___f_2902_, 0, v_snd_2886_);
lean_closure_set(v___f_2902_, 1, v_config_2901_);
lean_closure_set(v___f_2902_, 2, v_fst_2885_);
v___x_2903_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2900_, v___f_2902_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2929_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2929_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2929_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_fst_2908_; lean_object* v_snd_2909_; lean_object* v___x_2910_; lean_object* v_caches_2911_; lean_object* v_typeAnalysis_2912_; lean_object* v_hypotheses_2913_; uint8_t v_didChange_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2927_; 
v_fst_2908_ = lean_ctor_get(v_a_2904_, 0);
lean_inc(v_fst_2908_);
v_snd_2909_ = lean_ctor_get(v_a_2904_, 1);
lean_inc(v_snd_2909_);
lean_dec(v_a_2904_);
v___x_2910_ = lean_st_ref_take(v___y_2888_);
v_caches_2911_ = lean_ctor_get(v___x_2910_, 0);
v_typeAnalysis_2912_ = lean_ctor_get(v___x_2910_, 1);
v_hypotheses_2913_ = lean_ctor_get(v___x_2910_, 3);
v_didChange_2914_ = lean_ctor_get_uint8(v___x_2910_, sizeof(void*)*4);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; 
v_unused_2928_ = lean_ctor_get(v___x_2910_, 2);
lean_dec(v_unused_2928_);
v___x_2916_ = v___x_2910_;
v_isShared_2917_ = v_isSharedCheck_2927_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_hypotheses_2913_);
lean_inc(v_typeAnalysis_2912_);
lean_inc(v_caches_2911_);
lean_dec(v___x_2910_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2927_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v_snd_2909_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 2, v___x_2918_);
v___x_2920_ = v___x_2916_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_caches_2911_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_typeAnalysis_2912_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2926_, 3, v_hypotheses_2913_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, sizeof(void*)*4, v_didChange_2914_);
v___x_2920_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2921_ = lean_st_ref_put(v___y_2888_, v___x_2920_);
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_fst_2908_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2922_);
v___x_2924_ = v___x_2906_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
v_a_2930_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2903_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2903_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec_ref(v_snd_2886_);
lean_dec_ref(v_fst_2885_);
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
return v___x_2939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___boxed(lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2(size_t v_sz_3016_, size_t v_i_3017_, lean_object* v_bs_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_3016_, v_i_3017_, v_bs_3018_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___boxed(lean_object* v_sz_3032_, lean_object* v_i_3033_, lean_object* v_bs_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
size_t v_sz_boxed_3047_; size_t v_i_boxed_3048_; lean_object* v_res_3049_; 
v_sz_boxed_3047_ = lean_unbox_usize(v_sz_3032_);
lean_dec(v_sz_3032_);
v_i_boxed_3048_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_res_3049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2(v_sz_boxed_3047_, v_i_boxed_3048_, v_bs_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(lean_object* v_as_3050_, size_t v_i_3051_, size_t v_stop_3052_, lean_object* v_b_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_3050_, v_i_3051_, v_stop_3052_, v_b_3053_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___boxed(lean_object* v_as_3066_, lean_object* v_i_3067_, lean_object* v_stop_3068_, lean_object* v_b_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
size_t v_i_boxed_3081_; size_t v_stop_boxed_3082_; lean_object* v_res_3083_; 
v_i_boxed_3081_ = lean_unbox_usize(v_i_3067_);
lean_dec(v_i_3067_);
v_stop_boxed_3082_ = lean_unbox_usize(v_stop_3068_);
lean_dec(v_stop_3068_);
v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(v_as_3066_, v_i_boxed_3081_, v_stop_boxed_3082_, v_b_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v_as_3066_);
return v_res_3083_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_unsigned_to_nat(32u);
v___x_3085_ = lean_mk_empty_array_with_capacity(v___x_3084_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
return v___x_3086_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3087_ = ((size_t)5ULL);
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = lean_unsigned_to_nat(32u);
v___x_3090_ = lean_mk_empty_array_with_capacity(v___x_3089_);
v___x_3091_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0);
v___x_3092_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3088_);
lean_ctor_set(v___x_3092_, 3, v___x_3088_);
lean_ctor_set_usize(v___x_3092_, 4, v___x_3087_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; lean_object* v_traceState_3096_; lean_object* v_traces_3097_; lean_object* v___x_3098_; lean_object* v_traceState_3099_; lean_object* v_env_3100_; lean_object* v_nextMacroScope_3101_; lean_object* v_ngen_3102_; lean_object* v_auxDeclNGen_3103_; lean_object* v_cache_3104_; lean_object* v_messages_3105_; lean_object* v_infoState_3106_; lean_object* v_snapshotTasks_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3126_; 
v___x_3095_ = lean_st_ref_get(v___y_3093_);
v_traceState_3096_ = lean_ctor_get(v___x_3095_, 4);
lean_inc_ref(v_traceState_3096_);
lean_dec(v___x_3095_);
v_traces_3097_ = lean_ctor_get(v_traceState_3096_, 0);
lean_inc_ref(v_traces_3097_);
lean_dec_ref(v_traceState_3096_);
v___x_3098_ = lean_st_ref_take(v___y_3093_);
v_traceState_3099_ = lean_ctor_get(v___x_3098_, 4);
v_env_3100_ = lean_ctor_get(v___x_3098_, 0);
v_nextMacroScope_3101_ = lean_ctor_get(v___x_3098_, 1);
v_ngen_3102_ = lean_ctor_get(v___x_3098_, 2);
v_auxDeclNGen_3103_ = lean_ctor_get(v___x_3098_, 3);
v_cache_3104_ = lean_ctor_get(v___x_3098_, 5);
v_messages_3105_ = lean_ctor_get(v___x_3098_, 6);
v_infoState_3106_ = lean_ctor_get(v___x_3098_, 7);
v_snapshotTasks_3107_ = lean_ctor_get(v___x_3098_, 8);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3109_ = v___x_3098_;
v_isShared_3110_ = v_isSharedCheck_3126_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_snapshotTasks_3107_);
lean_inc(v_infoState_3106_);
lean_inc(v_messages_3105_);
lean_inc(v_cache_3104_);
lean_inc(v_traceState_3099_);
lean_inc(v_auxDeclNGen_3103_);
lean_inc(v_ngen_3102_);
lean_inc(v_nextMacroScope_3101_);
lean_inc(v_env_3100_);
lean_dec(v___x_3098_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3126_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
uint64_t v_tid_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3124_; 
v_tid_3111_ = lean_ctor_get_uint64(v_traceState_3099_, sizeof(void*)*1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_traceState_3099_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_traceState_3099_, 0);
lean_dec(v_unused_3125_);
v___x_3113_ = v_traceState_3099_;
v_isShared_3114_ = v_isSharedCheck_3124_;
goto v_resetjp_3112_;
}
else
{
lean_dec(v_traceState_3099_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3124_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3115_);
lean_ctor_set_uint64(v_reuseFailAlloc_3123_, sizeof(void*)*1, v_tid_3111_);
v___x_3117_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3119_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 4, v___x_3117_);
v___x_3119_ = v___x_3109_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_env_3100_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_nextMacroScope_3101_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_ngen_3102_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_auxDeclNGen_3103_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3122_, 5, v_cache_3104_);
lean_ctor_set(v_reuseFailAlloc_3122_, 6, v_messages_3105_);
lean_ctor_set(v_reuseFailAlloc_3122_, 7, v_infoState_3106_);
lean_ctor_set(v_reuseFailAlloc_3122_, 8, v_snapshotTasks_3107_);
v___x_3119_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = lean_st_ref_put(v___y_3093_, v___x_3119_);
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_traces_3097_);
return v___x_3121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___boxed(lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_3127_);
lean_dec(v___y_3127_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_3140_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___boxed(lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
return v_res_3155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(lean_object* v_opts_3156_, lean_object* v_opt_3157_){
_start:
{
lean_object* v_name_3158_; lean_object* v_defValue_3159_; lean_object* v_map_3160_; lean_object* v___x_3161_; 
v_name_3158_ = lean_ctor_get(v_opt_3157_, 0);
v_defValue_3159_ = lean_ctor_get(v_opt_3157_, 1);
v_map_3160_ = lean_ctor_get(v_opts_3156_, 0);
v___x_3161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3160_, v_name_3158_);
if (lean_obj_tag(v___x_3161_) == 0)
{
uint8_t v___x_3162_; 
v___x_3162_ = lean_unbox(v_defValue_3159_);
return v___x_3162_;
}
else
{
lean_object* v_val_3163_; 
v_val_3163_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_val_3163_);
lean_dec_ref_known(v___x_3161_, 1);
if (lean_obj_tag(v_val_3163_) == 1)
{
uint8_t v_v_3164_; 
v_v_3164_ = lean_ctor_get_uint8(v_val_3163_, 0);
lean_dec_ref_known(v_val_3163_, 0);
return v_v_3164_;
}
else
{
uint8_t v___x_3165_; 
lean_dec(v_val_3163_);
v___x_3165_ = lean_unbox(v_defValue_3159_);
return v___x_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3___boxed(lean_object* v_opts_3166_, lean_object* v_opt_3167_){
_start:
{
uint8_t v_res_3168_; lean_object* v_r_3169_; 
v_res_3168_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3166_, v_opt_3167_);
lean_dec_ref(v_opt_3167_);
lean_dec_ref(v_opts_3166_);
v_r_3169_ = lean_box(v_res_3168_);
return v_r_3169_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0));
v___x_3172_ = l_Lean_stringToMessageData(v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(lean_object* v_x_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___boxed(lean_object* v_x_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(v_x_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec_ref(v_x_3188_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(lean_object* v_opts_3202_, lean_object* v_opt_3203_){
_start:
{
lean_object* v_name_3204_; lean_object* v_defValue_3205_; lean_object* v_map_3206_; lean_object* v___x_3207_; 
v_name_3204_ = lean_ctor_get(v_opt_3203_, 0);
v_defValue_3205_ = lean_ctor_get(v_opt_3203_, 1);
v_map_3206_ = lean_ctor_get(v_opts_3202_, 0);
v___x_3207_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3206_, v_name_3204_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_inc(v_defValue_3205_);
return v_defValue_3205_;
}
else
{
lean_object* v_val_3208_; 
v_val_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_val_3208_);
lean_dec_ref_known(v___x_3207_, 1);
if (lean_obj_tag(v_val_3208_) == 3)
{
lean_object* v_v_3209_; 
v_v_3209_ = lean_ctor_get(v_val_3208_, 0);
lean_inc(v_v_3209_);
lean_dec_ref_known(v_val_3208_, 1);
return v_v_3209_;
}
else
{
lean_dec(v_val_3208_);
lean_inc(v_defValue_3205_);
return v_defValue_3205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8___boxed(lean_object* v_opts_3210_, lean_object* v_opt_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3210_, v_opt_3211_);
lean_dec_ref(v_opt_3211_);
lean_dec_ref(v_opts_3210_);
return v_res_3212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(lean_object* v_e_3213_){
_start:
{
if (lean_obj_tag(v_e_3213_) == 0)
{
uint8_t v___x_3214_; 
v___x_3214_ = 2;
return v___x_3214_;
}
else
{
uint8_t v___x_3215_; 
v___x_3215_ = 0;
return v___x_3215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___boxed(lean_object* v_e_3216_){
_start:
{
uint8_t v_res_3217_; lean_object* v_r_3218_; 
v_res_3217_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(v_e_3216_);
lean_dec_ref(v_e_3216_);
v_r_3218_ = lean_box(v_res_3217_);
return v_r_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(size_t v_sz_3219_, size_t v_i_3220_, lean_object* v_bs_3221_){
_start:
{
uint8_t v___x_3222_; 
v___x_3222_ = lean_usize_dec_lt(v_i_3220_, v_sz_3219_);
if (v___x_3222_ == 0)
{
return v_bs_3221_;
}
else
{
lean_object* v_v_3223_; lean_object* v_msg_3224_; lean_object* v___x_3225_; lean_object* v_bs_x27_3226_; size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v_v_3223_ = lean_array_uget_borrowed(v_bs_3221_, v_i_3220_);
v_msg_3224_ = lean_ctor_get(v_v_3223_, 1);
lean_inc_ref(v_msg_3224_);
v___x_3225_ = lean_unsigned_to_nat(0u);
v_bs_x27_3226_ = lean_array_uset(v_bs_3221_, v_i_3220_, v___x_3225_);
v___x_3227_ = ((size_t)1ULL);
v___x_3228_ = lean_usize_add(v_i_3220_, v___x_3227_);
v___x_3229_ = lean_array_uset(v_bs_x27_3226_, v_i_3220_, v_msg_3224_);
v_i_3220_ = v___x_3228_;
v_bs_3221_ = v___x_3229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_3231_, lean_object* v_i_3232_, lean_object* v_bs_3233_){
_start:
{
size_t v_sz_boxed_3234_; size_t v_i_boxed_3235_; lean_object* v_res_3236_; 
v_sz_boxed_3234_ = lean_unbox_usize(v_sz_3231_);
lean_dec(v_sz_3231_);
v_i_boxed_3235_ = lean_unbox_usize(v_i_3232_);
lean_dec(v_i_3232_);
v_res_3236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(v_sz_boxed_3234_, v_i_boxed_3235_, v_bs_3233_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(lean_object* v_oldTraces_3237_, lean_object* v_data_3238_, lean_object* v_ref_3239_, lean_object* v_msg_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_toCold_3246_; lean_object* v_currRecDepth_3247_; lean_object* v_ref_3248_; uint8_t v_diag_3249_; uint8_t v_suppressElabErrors_3250_; lean_object* v___x_3251_; lean_object* v_traceState_3252_; lean_object* v_traces_3253_; lean_object* v_ref_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; size_t v_sz_3257_; size_t v___x_3258_; lean_object* v___x_3259_; lean_object* v_msg_3260_; lean_object* v___x_3261_; lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3299_; 
v_toCold_3246_ = lean_ctor_get(v___y_3243_, 0);
v_currRecDepth_3247_ = lean_ctor_get(v___y_3243_, 1);
v_ref_3248_ = lean_ctor_get(v___y_3243_, 2);
v_diag_3249_ = lean_ctor_get_uint8(v___y_3243_, sizeof(void*)*3);
v_suppressElabErrors_3250_ = lean_ctor_get_uint8(v___y_3243_, sizeof(void*)*3 + 1);
v___x_3251_ = lean_st_ref_get(v___y_3244_);
v_traceState_3252_ = lean_ctor_get(v___x_3251_, 4);
lean_inc_ref(v_traceState_3252_);
lean_dec(v___x_3251_);
v_traces_3253_ = lean_ctor_get(v_traceState_3252_, 0);
lean_inc_ref(v_traces_3253_);
lean_dec_ref(v_traceState_3252_);
v_ref_3254_ = l_Lean_replaceRef(v_ref_3239_, v_ref_3248_);
lean_inc(v_currRecDepth_3247_);
lean_inc_ref(v_toCold_3246_);
v___x_3255_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3255_, 0, v_toCold_3246_);
lean_ctor_set(v___x_3255_, 1, v_currRecDepth_3247_);
lean_ctor_set(v___x_3255_, 2, v_ref_3254_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*3, v_diag_3249_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*3 + 1, v_suppressElabErrors_3250_);
v___x_3256_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3253_);
lean_dec_ref(v_traces_3253_);
v_sz_3257_ = lean_array_size(v___x_3256_);
v___x_3258_ = ((size_t)0ULL);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(v_sz_3257_, v___x_3258_, v___x_3256_);
v_msg_3260_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3260_, 0, v_data_3238_);
lean_ctor_set(v_msg_3260_, 1, v_msg_3240_);
lean_ctor_set(v_msg_3260_, 2, v___x_3259_);
v___x_3261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_3260_, v___y_3241_, v___y_3242_, v___x_3255_, v___y_3244_);
lean_dec_ref_known(v___x_3255_, 3);
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3264_ = v___x_3261_;
v_isShared_3265_ = v_isSharedCheck_3299_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3299_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v_traceState_3267_; lean_object* v_env_3268_; lean_object* v_nextMacroScope_3269_; lean_object* v_ngen_3270_; lean_object* v_auxDeclNGen_3271_; lean_object* v_cache_3272_; lean_object* v_messages_3273_; lean_object* v_infoState_3274_; lean_object* v_snapshotTasks_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3298_; 
v___x_3266_ = lean_st_ref_take(v___y_3244_);
v_traceState_3267_ = lean_ctor_get(v___x_3266_, 4);
v_env_3268_ = lean_ctor_get(v___x_3266_, 0);
v_nextMacroScope_3269_ = lean_ctor_get(v___x_3266_, 1);
v_ngen_3270_ = lean_ctor_get(v___x_3266_, 2);
v_auxDeclNGen_3271_ = lean_ctor_get(v___x_3266_, 3);
v_cache_3272_ = lean_ctor_get(v___x_3266_, 5);
v_messages_3273_ = lean_ctor_get(v___x_3266_, 6);
v_infoState_3274_ = lean_ctor_get(v___x_3266_, 7);
v_snapshotTasks_3275_ = lean_ctor_get(v___x_3266_, 8);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3277_ = v___x_3266_;
v_isShared_3278_ = v_isSharedCheck_3298_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_snapshotTasks_3275_);
lean_inc(v_infoState_3274_);
lean_inc(v_messages_3273_);
lean_inc(v_cache_3272_);
lean_inc(v_traceState_3267_);
lean_inc(v_auxDeclNGen_3271_);
lean_inc(v_ngen_3270_);
lean_inc(v_nextMacroScope_3269_);
lean_inc(v_env_3268_);
lean_dec(v___x_3266_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3298_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
uint64_t v_tid_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3296_; 
v_tid_3279_ = lean_ctor_get_uint64(v_traceState_3267_, sizeof(void*)*1);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_traceState_3267_);
if (v_isSharedCheck_3296_ == 0)
{
lean_object* v_unused_3297_; 
v_unused_3297_ = lean_ctor_get(v_traceState_3267_, 0);
lean_dec(v_unused_3297_);
v___x_3281_ = v_traceState_3267_;
v_isShared_3282_ = v_isSharedCheck_3296_;
goto v_resetjp_3280_;
}
else
{
lean_dec(v_traceState_3267_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3296_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_ref_3239_);
lean_ctor_set(v___x_3283_, 1, v_a_3262_);
v___x_3284_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3237_, v___x_3283_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v___x_3284_);
v___x_3286_ = v___x_3281_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3284_);
lean_ctor_set_uint64(v_reuseFailAlloc_3295_, sizeof(void*)*1, v_tid_3279_);
v___x_3286_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3288_; 
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 4, v___x_3286_);
v___x_3288_ = v___x_3277_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_env_3268_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_nextMacroScope_3269_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_ngen_3270_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v_auxDeclNGen_3271_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3294_, 5, v_cache_3272_);
lean_ctor_set(v_reuseFailAlloc_3294_, 6, v_messages_3273_);
lean_ctor_set(v_reuseFailAlloc_3294_, 7, v_infoState_3274_);
lean_ctor_set(v_reuseFailAlloc_3294_, 8, v_snapshotTasks_3275_);
v___x_3288_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3289_ = lean_st_ref_put(v___y_3244_, v___x_3288_);
v___x_3290_ = lean_box(0);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 0, v___x_3290_);
v___x_3292_ = v___x_3264_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg___boxed(lean_object* v_oldTraces_3300_, lean_object* v_data_3301_, lean_object* v_ref_3302_, lean_object* v_msg_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3300_, v_data_3301_, v_ref_3302_, v_msg_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(lean_object* v_x_3310_){
_start:
{
if (lean_obj_tag(v_x_3310_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
v_a_3312_ = lean_ctor_get(v_x_3310_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_x_3310_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v_x_3310_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v_x_3310_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 1);
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
v_a_3320_ = lean_ctor_get(v_x_3310_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_x_3310_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v_x_3310_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v_x_3310_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set_tag(v___x_3322_, 0);
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg___boxed(lean_object* v_x_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_x_3328_);
return v_res_3330_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0(void){
_start:
{
lean_object* v___x_3331_; double v___x_3332_; 
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = lean_float_of_nat(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3336_; double v___x_3337_; 
v___x_3336_ = lean_unsigned_to_nat(1000u);
v___x_3337_ = lean_float_of_nat(v___x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(lean_object* v_cls_3338_, uint8_t v_collapsed_3339_, lean_object* v_tag_3340_, lean_object* v_opts_3341_, uint8_t v_clsEnabled_3342_, lean_object* v_oldTraces_3343_, lean_object* v_msg_3344_, lean_object* v_resStartStop_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_fst_3358_; lean_object* v_snd_3359_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v_data_3363_; lean_object* v_fst_3366_; lean_object* v_snd_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; lean_object* v___y_3371_; lean_object* v_a_3372_; uint8_t v___y_3387_; double v___y_3418_; 
v_fst_3358_ = lean_ctor_get(v_resStartStop_3345_, 0);
lean_inc(v_fst_3358_);
v_snd_3359_ = lean_ctor_get(v_resStartStop_3345_, 1);
lean_inc(v_snd_3359_);
lean_dec_ref(v_resStartStop_3345_);
v_fst_3366_ = lean_ctor_get(v_snd_3359_, 0);
lean_inc(v_fst_3366_);
v_snd_3367_ = lean_ctor_get(v_snd_3359_, 1);
lean_inc(v_snd_3367_);
lean_dec(v_snd_3359_);
v___x_3368_ = l_Lean_trace_profiler;
v___x_3369_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3341_, v___x_3368_);
if (v___x_3369_ == 0)
{
v___y_3387_ = v___x_3369_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3423_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3424_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3341_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; double v___x_3427_; double v___x_3428_; double v___x_3429_; 
v___x_3425_ = l_Lean_trace_profiler_threshold;
v___x_3426_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3341_, v___x_3425_);
v___x_3427_ = lean_float_of_nat(v___x_3426_);
v___x_3428_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3);
v___x_3429_ = lean_float_div(v___x_3427_, v___x_3428_);
v___y_3418_ = v___x_3429_;
goto v___jp_3417_;
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; double v___x_3432_; 
v___x_3430_ = l_Lean_trace_profiler_threshold;
v___x_3431_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3341_, v___x_3430_);
v___x_3432_ = lean_float_of_nat(v___x_3431_);
v___y_3418_ = v___x_3432_;
goto v___jp_3417_;
}
}
v___jp_3360_:
{
lean_object* v___x_3364_; 
lean_inc(v___y_3361_);
v___x_3364_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3343_, v_data_3363_, v___y_3361_, v___y_3362_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v___x_3365_; 
lean_dec_ref_known(v___x_3364_, 1);
v___x_3365_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_fst_3358_);
return v___x_3365_;
}
else
{
lean_dec(v_fst_3358_);
return v___x_3364_;
}
}
v___jp_3370_:
{
uint8_t v_result_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; double v___x_3376_; lean_object* v_data_3377_; 
v_result_3373_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(v_fst_3358_);
v___x_3374_ = lean_box(v_result_3373_);
v___x_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
v___x_3376_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0);
lean_inc_ref(v_tag_3340_);
lean_inc_ref(v___x_3375_);
lean_inc(v_cls_3338_);
v_data_3377_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3377_, 0, v_cls_3338_);
lean_ctor_set(v_data_3377_, 1, v___x_3375_);
lean_ctor_set(v_data_3377_, 2, v_tag_3340_);
lean_ctor_set_float(v_data_3377_, sizeof(void*)*3, v___x_3376_);
lean_ctor_set_float(v_data_3377_, sizeof(void*)*3 + 8, v___x_3376_);
lean_ctor_set_uint8(v_data_3377_, sizeof(void*)*3 + 16, v_collapsed_3339_);
if (v___x_3369_ == 0)
{
lean_dec_ref_known(v___x_3375_, 1);
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
lean_dec_ref(v_tag_3340_);
lean_dec(v_cls_3338_);
v___y_3361_ = v___y_3371_;
v___y_3362_ = v_a_3372_;
v_data_3363_ = v_data_3377_;
goto v___jp_3360_;
}
else
{
lean_object* v_data_3378_; double v___x_3379_; double v___x_3380_; 
lean_dec_ref_known(v_data_3377_, 3);
v_data_3378_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3378_, 0, v_cls_3338_);
lean_ctor_set(v_data_3378_, 1, v___x_3375_);
lean_ctor_set(v_data_3378_, 2, v_tag_3340_);
v___x_3379_ = lean_unbox_float(v_fst_3366_);
lean_dec(v_fst_3366_);
lean_ctor_set_float(v_data_3378_, sizeof(void*)*3, v___x_3379_);
v___x_3380_ = lean_unbox_float(v_snd_3367_);
lean_dec(v_snd_3367_);
lean_ctor_set_float(v_data_3378_, sizeof(void*)*3 + 8, v___x_3380_);
lean_ctor_set_uint8(v_data_3378_, sizeof(void*)*3 + 16, v_collapsed_3339_);
v___y_3361_ = v___y_3371_;
v___y_3362_ = v_a_3372_;
v_data_3363_ = v_data_3378_;
goto v___jp_3360_;
}
}
v___jp_3381_:
{
lean_object* v_ref_3382_; lean_object* v___x_3383_; 
v_ref_3382_ = lean_ctor_get(v___y_3355_, 2);
lean_inc(v___y_3356_);
lean_inc_ref(v___y_3355_);
lean_inc(v___y_3354_);
lean_inc_ref(v___y_3353_);
lean_inc(v___y_3352_);
lean_inc_ref(v___y_3351_);
lean_inc(v___y_3350_);
lean_inc_ref(v___y_3349_);
lean_inc(v___y_3348_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
lean_inc(v_fst_3358_);
v___x_3383_ = lean_apply_13(v_msg_3344_, v_fst_3358_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, lean_box(0));
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v___y_3371_ = v_ref_3382_;
v_a_3372_ = v_a_3384_;
goto v___jp_3370_;
}
else
{
lean_object* v___x_3385_; 
lean_dec_ref_known(v___x_3383_, 1);
v___x_3385_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2);
v___y_3371_ = v_ref_3382_;
v_a_3372_ = v___x_3385_;
goto v___jp_3370_;
}
}
v___jp_3386_:
{
if (v_clsEnabled_3342_ == 0)
{
if (v___y_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v_traceState_3389_; lean_object* v_env_3390_; lean_object* v_nextMacroScope_3391_; lean_object* v_ngen_3392_; lean_object* v_auxDeclNGen_3393_; lean_object* v_cache_3394_; lean_object* v_messages_3395_; lean_object* v_infoState_3396_; lean_object* v_snapshotTasks_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_snd_3367_);
lean_dec(v_fst_3366_);
lean_dec_ref(v_msg_3344_);
lean_dec_ref(v_tag_3340_);
lean_dec(v_cls_3338_);
v___x_3388_ = lean_st_ref_take(v___y_3356_);
v_traceState_3389_ = lean_ctor_get(v___x_3388_, 4);
v_env_3390_ = lean_ctor_get(v___x_3388_, 0);
v_nextMacroScope_3391_ = lean_ctor_get(v___x_3388_, 1);
v_ngen_3392_ = lean_ctor_get(v___x_3388_, 2);
v_auxDeclNGen_3393_ = lean_ctor_get(v___x_3388_, 3);
v_cache_3394_ = lean_ctor_get(v___x_3388_, 5);
v_messages_3395_ = lean_ctor_get(v___x_3388_, 6);
v_infoState_3396_ = lean_ctor_get(v___x_3388_, 7);
v_snapshotTasks_3397_ = lean_ctor_get(v___x_3388_, 8);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3399_ = v___x_3388_;
v_isShared_3400_ = v_isSharedCheck_3416_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_snapshotTasks_3397_);
lean_inc(v_infoState_3396_);
lean_inc(v_messages_3395_);
lean_inc(v_cache_3394_);
lean_inc(v_traceState_3389_);
lean_inc(v_auxDeclNGen_3393_);
lean_inc(v_ngen_3392_);
lean_inc(v_nextMacroScope_3391_);
lean_inc(v_env_3390_);
lean_dec(v___x_3388_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3416_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
uint64_t v_tid_3401_; lean_object* v_traces_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3415_; 
v_tid_3401_ = lean_ctor_get_uint64(v_traceState_3389_, sizeof(void*)*1);
v_traces_3402_ = lean_ctor_get(v_traceState_3389_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_traceState_3389_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3404_ = v_traceState_3389_;
v_isShared_3405_ = v_isSharedCheck_3415_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_traces_3402_);
lean_dec(v_traceState_3389_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3415_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3406_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3343_, v_traces_3402_);
lean_dec_ref(v_traces_3402_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3406_);
v___x_3408_ = v___x_3404_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3406_);
lean_ctor_set_uint64(v_reuseFailAlloc_3414_, sizeof(void*)*1, v_tid_3401_);
v___x_3408_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3410_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 4, v___x_3408_);
v___x_3410_ = v___x_3399_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_env_3390_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_nextMacroScope_3391_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_ngen_3392_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_auxDeclNGen_3393_);
lean_ctor_set(v_reuseFailAlloc_3413_, 4, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3413_, 5, v_cache_3394_);
lean_ctor_set(v_reuseFailAlloc_3413_, 6, v_messages_3395_);
lean_ctor_set(v_reuseFailAlloc_3413_, 7, v_infoState_3396_);
lean_ctor_set(v_reuseFailAlloc_3413_, 8, v_snapshotTasks_3397_);
v___x_3410_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = lean_st_ref_put(v___y_3356_, v___x_3410_);
v___x_3412_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_fst_3358_);
return v___x_3412_;
}
}
}
}
}
else
{
goto v___jp_3381_;
}
}
else
{
goto v___jp_3381_;
}
}
v___jp_3417_:
{
double v___x_3419_; double v___x_3420_; double v___x_3421_; uint8_t v___x_3422_; 
v___x_3419_ = lean_unbox_float(v_snd_3367_);
v___x_3420_ = lean_unbox_float(v_fst_3366_);
v___x_3421_ = lean_float_sub(v___x_3419_, v___x_3420_);
v___x_3422_ = lean_float_decLt(v___y_3418_, v___x_3421_);
v___y_3387_ = v___x_3422_;
goto v___jp_3386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___boxed(lean_object** _args){
lean_object* v_cls_3433_ = _args[0];
lean_object* v_collapsed_3434_ = _args[1];
lean_object* v_tag_3435_ = _args[2];
lean_object* v_opts_3436_ = _args[3];
lean_object* v_clsEnabled_3437_ = _args[4];
lean_object* v_oldTraces_3438_ = _args[5];
lean_object* v_msg_3439_ = _args[6];
lean_object* v_resStartStop_3440_ = _args[7];
lean_object* v___y_3441_ = _args[8];
lean_object* v___y_3442_ = _args[9];
lean_object* v___y_3443_ = _args[10];
lean_object* v___y_3444_ = _args[11];
lean_object* v___y_3445_ = _args[12];
lean_object* v___y_3446_ = _args[13];
lean_object* v___y_3447_ = _args[14];
lean_object* v___y_3448_ = _args[15];
lean_object* v___y_3449_ = _args[16];
lean_object* v___y_3450_ = _args[17];
lean_object* v___y_3451_ = _args[18];
lean_object* v___y_3452_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_3453_; uint8_t v_clsEnabled_boxed_3454_; lean_object* v_res_3455_; 
v_collapsed_boxed_3453_ = lean_unbox(v_collapsed_3434_);
v_clsEnabled_boxed_3454_ = lean_unbox(v_clsEnabled_3437_);
v_res_3455_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v_cls_3433_, v_collapsed_boxed_3453_, v_tag_3435_, v_opts_3436_, v_clsEnabled_boxed_3454_, v_oldTraces_3438_, v_msg_3439_, v_resStartStop_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v_opts_3436_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(lean_object* v_cls_3459_, lean_object* v_msg_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_ref_3466_; lean_object* v___x_3467_; lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3512_; 
v_ref_3466_ = lean_ctor_get(v___y_3463_, 2);
v___x_3467_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3512_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3512_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v_traceState_3473_; lean_object* v_env_3474_; lean_object* v_nextMacroScope_3475_; lean_object* v_ngen_3476_; lean_object* v_auxDeclNGen_3477_; lean_object* v_cache_3478_; lean_object* v_messages_3479_; lean_object* v_infoState_3480_; lean_object* v_snapshotTasks_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3511_; 
v___x_3472_ = lean_st_ref_take(v___y_3464_);
v_traceState_3473_ = lean_ctor_get(v___x_3472_, 4);
v_env_3474_ = lean_ctor_get(v___x_3472_, 0);
v_nextMacroScope_3475_ = lean_ctor_get(v___x_3472_, 1);
v_ngen_3476_ = lean_ctor_get(v___x_3472_, 2);
v_auxDeclNGen_3477_ = lean_ctor_get(v___x_3472_, 3);
v_cache_3478_ = lean_ctor_get(v___x_3472_, 5);
v_messages_3479_ = lean_ctor_get(v___x_3472_, 6);
v_infoState_3480_ = lean_ctor_get(v___x_3472_, 7);
v_snapshotTasks_3481_ = lean_ctor_get(v___x_3472_, 8);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3483_ = v___x_3472_;
v_isShared_3484_ = v_isSharedCheck_3511_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_snapshotTasks_3481_);
lean_inc(v_infoState_3480_);
lean_inc(v_messages_3479_);
lean_inc(v_cache_3478_);
lean_inc(v_traceState_3473_);
lean_inc(v_auxDeclNGen_3477_);
lean_inc(v_ngen_3476_);
lean_inc(v_nextMacroScope_3475_);
lean_inc(v_env_3474_);
lean_dec(v___x_3472_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3511_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
uint64_t v_tid_3485_; lean_object* v_traces_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3510_; 
v_tid_3485_ = lean_ctor_get_uint64(v_traceState_3473_, sizeof(void*)*1);
v_traces_3486_ = lean_ctor_get(v_traceState_3473_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_traceState_3473_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3488_ = v_traceState_3473_;
v_isShared_3489_ = v_isSharedCheck_3510_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_traces_3486_);
lean_dec(v_traceState_3473_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3510_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; double v___x_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3490_ = lean_box(0);
v___x_3491_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0);
v___x_3492_ = 0;
v___x_3493_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0));
v___x_3494_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3494_, 0, v_cls_3459_);
lean_ctor_set(v___x_3494_, 1, v___x_3490_);
lean_ctor_set(v___x_3494_, 2, v___x_3493_);
lean_ctor_set_float(v___x_3494_, sizeof(void*)*3, v___x_3491_);
lean_ctor_set_float(v___x_3494_, sizeof(void*)*3 + 8, v___x_3491_);
lean_ctor_set_uint8(v___x_3494_, sizeof(void*)*3 + 16, v___x_3492_);
v___x_3495_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1));
v___x_3496_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3494_);
lean_ctor_set(v___x_3496_, 1, v_a_3468_);
lean_ctor_set(v___x_3496_, 2, v___x_3495_);
lean_inc(v_ref_3466_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v_ref_3466_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = l_Lean_PersistentArray_push___redArg(v_traces_3486_, v___x_3497_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3498_);
v___x_3500_ = v___x_3488_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3498_);
lean_ctor_set_uint64(v_reuseFailAlloc_3509_, sizeof(void*)*1, v_tid_3485_);
v___x_3500_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 4, v___x_3500_);
v___x_3502_ = v___x_3483_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_env_3474_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_nextMacroScope_3475_);
lean_ctor_set(v_reuseFailAlloc_3508_, 2, v_ngen_3476_);
lean_ctor_set(v_reuseFailAlloc_3508_, 3, v_auxDeclNGen_3477_);
lean_ctor_set(v_reuseFailAlloc_3508_, 4, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3508_, 5, v_cache_3478_);
lean_ctor_set(v_reuseFailAlloc_3508_, 6, v_messages_3479_);
lean_ctor_set(v_reuseFailAlloc_3508_, 7, v_infoState_3480_);
lean_ctor_set(v_reuseFailAlloc_3508_, 8, v_snapshotTasks_3481_);
v___x_3502_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3506_; 
v___x_3503_ = lean_st_ref_put(v___y_3464_, v___x_3502_);
v___x_3504_ = lean_box(0);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3504_);
v___x_3506_ = v___x_3470_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___boxed(lean_object* v_cls_3513_, lean_object* v_msg_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v_cls_3513_, v_msg_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3520_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__5));
v___x_3533_ = l_Lean_Name_append(v___x_3532_, v___x_3531_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(lean_object* v_as_3534_, size_t v_i_3535_, size_t v_stop_3536_, lean_object* v_b_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_a_3551_; uint8_t v___x_3557_; 
v___x_3557_ = lean_usize_dec_eq(v_i_3535_, v_stop_3536_);
if (v___x_3557_ == 0)
{
lean_object* v_toCold_3558_; lean_object* v_options_3559_; uint8_t v_hasTrace_3560_; 
v_toCold_3558_ = lean_ctor_get(v___y_3547_, 0);
v_options_3559_ = lean_ctor_get(v_toCold_3558_, 2);
v_hasTrace_3560_ = lean_ctor_get_uint8(v_options_3559_, sizeof(void*)*1);
if (v_hasTrace_3560_ == 0)
{
goto v___jp_3555_;
}
else
{
lean_object* v_inheritedTraceOptions_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_inheritedTraceOptions_3561_ = lean_ctor_get(v_toCold_3558_, 11);
v___x_3562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3563_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3561_, v_options_3559_, v___x_3563_);
if (v___x_3564_ == 0)
{
goto v___jp_3555_;
}
else
{
lean_object* v___x_3565_; lean_object* v_type_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3565_ = lean_array_uget_borrowed(v_as_3534_, v_i_3535_);
v_type_3566_ = lean_ctor_get(v___x_3565_, 1);
lean_inc_ref(v_type_3566_);
v___x_3567_ = l_Lean_MessageData_ofExpr(v_type_3566_);
v___x_3568_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v___x_3562_, v___x_3567_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
v_a_3551_ = v_a_3569_;
goto v___jp_3550_;
}
else
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3570_, 0, v_b_3537_);
return v___x_3570_;
}
v___jp_3550_:
{
size_t v___x_3552_; size_t v___x_3553_; 
v___x_3552_ = ((size_t)1ULL);
v___x_3553_ = lean_usize_add(v_i_3535_, v___x_3552_);
v_i_3535_ = v___x_3553_;
v_b_3537_ = v_a_3551_;
goto _start;
}
v___jp_3555_:
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_box(0);
v_a_3551_ = v___x_3556_;
goto v___jp_3550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___boxed(lean_object* v_as_3571_, lean_object* v_i_3572_, lean_object* v_stop_3573_, lean_object* v_b_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
size_t v_i_boxed_3587_; size_t v_stop_boxed_3588_; lean_object* v_res_3589_; 
v_i_boxed_3587_ = lean_unbox_usize(v_i_3572_);
lean_dec(v_i_3572_);
v_stop_boxed_3588_ = lean_unbox_usize(v_stop_3573_);
lean_dec(v_stop_3573_);
v_res_3589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(v_as_3571_, v_i_boxed_3587_, v_stop_boxed_3588_, v_b_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec_ref(v_as_3571_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(lean_object* v_as_3590_, size_t v_i_3591_, size_t v_stop_3592_, lean_object* v_b_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_a_3607_; uint8_t v___x_3613_; 
v___x_3613_ = lean_usize_dec_eq(v_i_3591_, v_stop_3592_);
if (v___x_3613_ == 0)
{
lean_object* v_toCold_3614_; lean_object* v_options_3615_; uint8_t v_hasTrace_3616_; 
v_toCold_3614_ = lean_ctor_get(v___y_3603_, 0);
v_options_3615_ = lean_ctor_get(v_toCold_3614_, 2);
v_hasTrace_3616_ = lean_ctor_get_uint8(v_options_3615_, sizeof(void*)*1);
if (v_hasTrace_3616_ == 0)
{
goto v___jp_3611_;
}
else
{
lean_object* v_inheritedTraceOptions_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; 
v_inheritedTraceOptions_3617_ = lean_ctor_get(v_toCold_3614_, 11);
v___x_3618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3620_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3617_, v_options_3615_, v___x_3619_);
if (v___x_3620_ == 0)
{
goto v___jp_3611_;
}
else
{
lean_object* v___x_3621_; lean_object* v_type_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3621_ = lean_array_uget_borrowed(v_as_3590_, v_i_3591_);
v_type_3622_ = lean_ctor_get(v___x_3621_, 1);
lean_inc_ref(v_type_3622_);
v___x_3623_ = l_Lean_MessageData_ofExpr(v_type_3622_);
v___x_3624_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v___x_3618_, v___x_3623_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v_a_3607_ = v_a_3625_;
goto v___jp_3606_;
}
else
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v___x_3626_; 
v___x_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3626_, 0, v_b_3593_);
return v___x_3626_;
}
v___jp_3606_:
{
size_t v___x_3608_; size_t v___x_3609_; lean_object* v___x_3610_; 
v___x_3608_ = ((size_t)1ULL);
v___x_3609_ = lean_usize_add(v_i_3591_, v___x_3608_);
v___x_3610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(v_as_3590_, v___x_3609_, v_stop_3592_, v_a_3607_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
return v___x_3610_;
}
v___jp_3611_:
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_box(0);
v_a_3607_ = v___x_3612_;
goto v___jp_3606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1___boxed(lean_object* v_as_3627_, lean_object* v_i_3628_, lean_object* v_stop_3629_, lean_object* v_b_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
size_t v_i_boxed_3643_; size_t v_stop_boxed_3644_; lean_object* v_res_3645_; 
v_i_boxed_3643_ = lean_unbox_usize(v_i_3628_);
lean_dec(v_i_3628_);
v_stop_boxed_3644_ = lean_unbox_usize(v_stop_3629_);
lean_dec(v_stop_3629_);
v_res_3645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_as_3627_, v_i_boxed_3643_, v_stop_boxed_3644_, v_b_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v_as_3627_);
return v_res_3645_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1(void){
_start:
{
lean_object* v___x_3647_; double v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(1000000000u);
v___x_3648_ = lean_float_of_nat(v___x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3827_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3827_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3827_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
if (lean_obj_tag(v_a_3662_) == 1)
{
lean_object* v_val_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3821_; 
v_val_3666_ = lean_ctor_get(v_a_3662_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_a_3662_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3668_ = v_a_3662_;
v_isShared_3669_ = v_isSharedCheck_3821_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_val_3666_);
lean_dec(v_a_3662_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3821_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___y_3691_; lean_object* v_toCold_3700_; lean_object* v_options_3701_; lean_object* v_inheritedTraceOptions_3702_; uint8_t v_hasTrace_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v_toCold_3700_ = lean_ctor_get(v_a_3658_, 0);
v_options_3701_ = lean_ctor_get(v_toCold_3700_, 2);
v_inheritedTraceOptions_3702_ = lean_ctor_get(v_toCold_3700_, 11);
v_hasTrace_3703_ = lean_ctor_get_uint8(v_options_3701_, sizeof(void*)*1);
v___x_3704_ = lean_unsigned_to_nat(0u);
v___x_3705_ = lean_array_get_size(v_val_3666_);
if (v_hasTrace_3703_ == 0)
{
uint8_t v___x_3706_; 
lean_del_object(v___x_3668_);
v___x_3706_ = lean_nat_dec_lt(v___x_3704_, v___x_3705_);
if (v___x_3706_ == 0)
{
goto v___jp_3670_;
}
else
{
lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = lean_box(0);
v___x_3708_ = lean_nat_dec_le(v___x_3705_, v___x_3705_);
if (v___x_3708_ == 0)
{
if (v___x_3706_ == 0)
{
goto v___jp_3670_;
}
else
{
size_t v___x_3709_; size_t v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = ((size_t)0ULL);
v___x_3710_ = lean_usize_of_nat(v___x_3705_);
v___x_3711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3666_, v___x_3709_, v___x_3710_, v___x_3707_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3691_ = v___x_3711_;
goto v___jp_3690_;
}
}
else
{
size_t v___x_3712_; size_t v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = ((size_t)0ULL);
v___x_3713_ = lean_usize_of_nat(v___x_3705_);
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3666_, v___x_3712_, v___x_3713_, v___x_3707_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3691_ = v___x_3714_;
goto v___jp_3690_;
}
}
}
else
{
lean_object* v___f_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v_a_3723_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v_a_3738_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v_a_3758_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v_a_3770_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; 
v___f_3715_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0));
v___x_3716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3717_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0));
v___x_3718_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3702_, v_options_3701_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3810_; uint8_t v___x_3811_; 
v___x_3810_ = l_Lean_trace_profiler;
v___x_3811_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_options_3701_, v___x_3810_);
if (v___x_3811_ == 0)
{
uint8_t v___x_3812_; 
lean_del_object(v___x_3668_);
v___x_3812_ = lean_nat_dec_lt(v___x_3704_, v___x_3705_);
if (v___x_3812_ == 0)
{
goto v___jp_3670_;
}
else
{
lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3813_ = lean_box(0);
v___x_3814_ = lean_nat_dec_le(v___x_3705_, v___x_3705_);
if (v___x_3814_ == 0)
{
if (v___x_3812_ == 0)
{
goto v___jp_3670_;
}
else
{
size_t v___x_3815_; size_t v___x_3816_; lean_object* v___x_3817_; 
v___x_3815_ = ((size_t)0ULL);
v___x_3816_ = lean_usize_of_nat(v___x_3705_);
v___x_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3666_, v___x_3815_, v___x_3816_, v___x_3813_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3691_ = v___x_3817_;
goto v___jp_3690_;
}
}
else
{
size_t v___x_3818_; size_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = ((size_t)0ULL);
v___x_3819_ = lean_usize_of_nat(v___x_3705_);
v___x_3820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3666_, v___x_3818_, v___x_3819_, v___x_3813_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3691_ = v___x_3820_;
goto v___jp_3690_;
}
}
}
else
{
goto v___jp_3785_;
}
}
else
{
goto v___jp_3785_;
}
v___jp_3720_:
{
lean_object* v___x_3724_; double v___x_3725_; double v___x_3726_; double v___x_3727_; double v___x_3728_; double v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3724_ = lean_io_mono_nanos_now();
v___x_3725_ = lean_float_of_nat(v___y_3722_);
v___x_3726_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1);
v___x_3727_ = lean_float_div(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_float_of_nat(v___x_3724_);
v___x_3729_ = lean_float_div(v___x_3728_, v___x_3726_);
v___x_3730_ = lean_box_float(v___x_3727_);
v___x_3731_ = lean_box_float(v___x_3729_);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_a_3723_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v___x_3716_, v_hasTrace_3703_, v___x_3717_, v_options_3701_, v___x_3719_, v___y_3721_, v___f_3715_, v___x_3733_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3691_ = v___x_3734_;
goto v___jp_3690_;
}
v___jp_3735_:
{
lean_object* v___x_3740_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v_a_3738_);
v___x_3740_ = v___x_3668_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
v___y_3721_ = v___y_3736_;
v___y_3722_ = v___y_3737_;
v_a_3723_ = v___x_3740_;
goto v___jp_3720_;
}
}
v___jp_3742_:
{
if (lean_obj_tag(v___y_3745_) == 0)
{
lean_object* v_a_3746_; 
v_a_3746_ = lean_ctor_get(v___y_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___y_3745_, 1);
v___y_3736_ = v___y_3743_;
v___y_3737_ = v___y_3744_;
v_a_3738_ = v_a_3746_;
goto v___jp_3735_;
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_del_object(v___x_3668_);
v_a_3747_ = lean_ctor_get(v___y_3745_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___y_3745_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___y_3745_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___y_3745_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 0);
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
v___y_3721_ = v___y_3743_;
v___y_3722_ = v___y_3744_;
v_a_3723_ = v___x_3752_;
goto v___jp_3720_;
}
}
}
}
v___jp_3755_:
{
lean_object* v___x_3759_; double v___x_3760_; double v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3759_ = lean_io_get_num_heartbeats();
v___x_3760_ = lean_float_of_nat(v___y_3757_);
v___x_3761_ = lean_float_of_nat(v___x_3759_);
v___x_3762_ = lean_box_float(v___x_3760_);
v___x_3763_ = lean_box_float(v___x_3761_);
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v_a_3758_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v___x_3716_, v_hasTrace_3703_, v___x_3717_, v_options_3701_, v___x_3719_, v___y_3756_, v___f_3715_, v___x_3765_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3691_ = v___x_3766_;
goto v___jp_3690_;
}
v___jp_3767_:
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v_a_3770_);
v___y_3756_ = v___y_3768_;
v___y_3757_ = v___y_3769_;
v_a_3758_ = v___x_3771_;
goto v___jp_3755_;
}
v___jp_3772_:
{
if (lean_obj_tag(v___y_3775_) == 0)
{
lean_object* v_a_3776_; 
v_a_3776_ = lean_ctor_get(v___y_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___y_3775_, 1);
v___y_3768_ = v___y_3773_;
v___y_3769_ = v___y_3774_;
v_a_3770_ = v_a_3776_;
goto v___jp_3767_;
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
v_a_3777_ = lean_ctor_get(v___y_3775_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___y_3775_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___y_3775_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___y_3775_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set_tag(v___x_3779_, 0);
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
v___y_3756_ = v___y_3773_;
v___y_3757_ = v___y_3774_;
v_a_3758_ = v___x_3782_;
goto v___jp_3755_;
}
}
}
}
v___jp_3785_:
{
lean_object* v___x_3786_; lean_object* v_a_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3786_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v_a_3659_);
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3789_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_options_3701_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3790_ = lean_io_mono_nanos_now();
v___x_3791_ = lean_box(0);
v___x_3792_ = lean_nat_dec_lt(v___x_3704_, v___x_3705_);
if (v___x_3792_ == 0)
{
v___y_3736_ = v_a_3787_;
v___y_3737_ = v___x_3790_;
v_a_3738_ = v___x_3791_;
goto v___jp_3735_;
}
else
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_nat_dec_le(v___x_3705_, v___x_3705_);
if (v___x_3793_ == 0)
{
if (v___x_3792_ == 0)
{
v___y_3736_ = v_a_3787_;
v___y_3737_ = v___x_3790_;
v_a_3738_ = v___x_3791_;
goto v___jp_3735_;
}
else
{
size_t v___x_3794_; size_t v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = ((size_t)0ULL);
v___x_3795_ = lean_usize_of_nat(v___x_3705_);
v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3666_, v___x_3794_, v___x_3795_, v___x_3791_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3743_ = v_a_3787_;
v___y_3744_ = v___x_3790_;
v___y_3745_ = v___x_3796_;
goto v___jp_3742_;
}
}
else
{
size_t v___x_3797_; size_t v___x_3798_; lean_object* v___x_3799_; 
v___x_3797_ = ((size_t)0ULL);
v___x_3798_ = lean_usize_of_nat(v___x_3705_);
v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3666_, v___x_3797_, v___x_3798_, v___x_3791_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3743_ = v_a_3787_;
v___y_3744_ = v___x_3790_;
v___y_3745_ = v___x_3799_;
goto v___jp_3742_;
}
}
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
lean_del_object(v___x_3668_);
v___x_3800_ = lean_io_get_num_heartbeats();
v___x_3801_ = lean_box(0);
v___x_3802_ = lean_nat_dec_lt(v___x_3704_, v___x_3705_);
if (v___x_3802_ == 0)
{
v___y_3768_ = v_a_3787_;
v___y_3769_ = v___x_3800_;
v_a_3770_ = v___x_3801_;
goto v___jp_3767_;
}
else
{
uint8_t v___x_3803_; 
v___x_3803_ = lean_nat_dec_le(v___x_3705_, v___x_3705_);
if (v___x_3803_ == 0)
{
if (v___x_3802_ == 0)
{
v___y_3768_ = v_a_3787_;
v___y_3769_ = v___x_3800_;
v_a_3770_ = v___x_3801_;
goto v___jp_3767_;
}
else
{
size_t v___x_3804_; size_t v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = ((size_t)0ULL);
v___x_3805_ = lean_usize_of_nat(v___x_3705_);
v___x_3806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3666_, v___x_3804_, v___x_3805_, v___x_3801_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3773_ = v_a_3787_;
v___y_3774_ = v___x_3800_;
v___y_3775_ = v___x_3806_;
goto v___jp_3772_;
}
}
else
{
size_t v___x_3807_; size_t v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = ((size_t)0ULL);
v___x_3808_ = lean_usize_of_nat(v___x_3705_);
v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3666_, v___x_3807_, v___x_3808_, v___x_3801_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
v___y_3773_ = v_a_3787_;
v___y_3774_ = v___x_3800_;
v___y_3775_ = v___x_3809_;
goto v___jp_3772_;
}
}
}
}
}
v___jp_3670_:
{
lean_object* v___x_3671_; lean_object* v_caches_3672_; lean_object* v_typeAnalysis_3673_; lean_object* v_target_3674_; uint8_t v_didChange_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3688_; 
v___x_3671_ = lean_st_ref_take(v_a_3650_);
v_caches_3672_ = lean_ctor_get(v___x_3671_, 0);
v_typeAnalysis_3673_ = lean_ctor_get(v___x_3671_, 1);
v_target_3674_ = lean_ctor_get(v___x_3671_, 2);
v_didChange_3675_ = lean_ctor_get_uint8(v___x_3671_, sizeof(void*)*4);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; 
v_unused_3689_ = lean_ctor_get(v___x_3671_, 3);
lean_dec(v_unused_3689_);
v___x_3677_ = v___x_3671_;
v_isShared_3678_ = v_isSharedCheck_3688_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_target_3674_);
lean_inc(v_typeAnalysis_3673_);
lean_inc(v_caches_3672_);
lean_dec(v___x_3671_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3688_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 3, v_val_3666_);
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_caches_3672_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_typeAnalysis_3673_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_target_3674_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_val_3666_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*4, v_didChange_3675_);
v___x_3680_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3681_; uint8_t v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
v___x_3681_ = lean_st_ref_put(v_a_3650_, v___x_3680_);
v___x_3682_ = 0;
v___x_3683_ = lean_box(v___x_3682_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3683_);
v___x_3685_ = v___x_3664_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
v___jp_3690_:
{
if (lean_obj_tag(v___y_3691_) == 0)
{
lean_dec_ref_known(v___y_3691_, 1);
goto v___jp_3670_;
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_val_3666_);
lean_del_object(v___x_3664_);
v_a_3692_ = lean_ctor_get(v___y_3691_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___y_3691_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___y_3691_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___y_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
}
else
{
uint8_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
lean_dec(v_a_3662_);
v___x_3822_ = 1;
v___x_3823_ = lean_box(v___x_3822_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3823_);
v___x_3825_ = v___x_3664_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
v_a_3828_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3661_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3661_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___boxed(lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
lean_dec(v_a_3844_);
lean_dec_ref(v_a_3843_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec_ref(v_a_3836_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(lean_object* v_cls_3849_, lean_object* v_msg_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v_cls_3849_, v_msg_3850_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___boxed(lean_object* v_cls_3864_, lean_object* v_msg_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(v_cls_3864_, v_msg_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(lean_object* v_00_u03b1_3879_, lean_object* v_x_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_x_3880_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3894_, lean_object* v_x_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(v_00_u03b1_3894_, v_x_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5(lean_object* v_oldTraces_3909_, lean_object* v_data_3910_, lean_object* v_ref_3911_, lean_object* v_msg_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3909_, v_data_3910_, v_ref_3911_, v_msg_3912_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___boxed(lean_object* v_oldTraces_3926_, lean_object* v_data_3927_, lean_object* v_ref_3928_, lean_object* v_msg_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5(v_oldTraces_3926_, v_data_3927_, v_ref_3928_, v_msg_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
return v_res_3942_;
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
