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
uint8_t v___x_11151__boxed_133_; lean_object* v_res_134_; 
v___x_11151__boxed_133_ = lean_unbox(v___x_131_);
v_res_134_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectNumBits_spec__0(v___x_11151__boxed_133_, v_x_132_);
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
uint8_t v___y_52000__boxed_808_; lean_object* v_res_809_; 
v___y_52000__boxed_808_ = lean_unbox(v___y_793_);
v_res_809_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0___redArg(v_val_792_, v___y_52000__boxed_808_, v_as_x27_794_, v_b_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
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
uint8_t v___y_53155__boxed_1493_; lean_object* v_res_1494_; 
v___y_53155__boxed_1493_ = lean_unbox(v___y_1475_);
v_res_1494_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps_collectRelevantEqualities_spec__0(v_val_1474_, v___y_53155__boxed_1493_, v_as_1476_, v_as_x27_1477_, v_b_1478_, v_a_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
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
lean_object* v___x_1954_; lean_object* v___x_8007__overap_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1___closed__0);
v___x_8007__overap_1955_ = lean_panic_fn_borrowed(v___x_1954_, v_msg_1946_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
v___x_1956_ = lean_apply_7(v___x_8007__overap_1955_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, lean_box(0));
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
lean_object* v___x_2041_; lean_object* v_env_2042_; lean_object* v___x_2043_; lean_object* v_mctx_2044_; lean_object* v_lctx_2045_; lean_object* v_options_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2041_ = lean_st_ref_get(v___y_2039_);
v_env_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_ref(v_env_2042_);
lean_dec(v___x_2041_);
v___x_2043_ = lean_st_ref_get(v___y_2037_);
v_mctx_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_ref(v_mctx_2044_);
lean_dec(v___x_2043_);
v_lctx_2045_ = lean_ctor_get(v___y_2036_, 2);
v_options_2046_ = lean_ctor_get(v___y_2038_, 2);
lean_inc_ref(v_options_2046_);
lean_inc_ref(v_lctx_2045_);
v___x_2047_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2047_, 0, v_env_2042_);
lean_ctor_set(v___x_2047_, 1, v_mctx_2044_);
lean_ctor_set(v___x_2047_, 2, v_lctx_2045_);
lean_ctor_set(v___x_2047_, 3, v_options_2046_);
v___x_2048_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v_msgData_2035_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0___boxed(lean_object* v_msgData_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msgData_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(lean_object* v_msg_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_ref_2063_; lean_object* v___x_2064_; lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2073_; 
v_ref_2063_ = lean_ctor_get(v___y_2060_, 5);
v___x_2064_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
lean_inc(v_ref_2063_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_ref_2063_);
lean_ctor_set(v___x_2069_, 1, v_a_2065_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set_tag(v___x_2067_, 1);
lean_ctor_set(v___x_2067_, 0, v___x_2069_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg___boxed(lean_object* v_msg_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v_msg_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__0));
v___x_2083_ = l_Lean_stringToMessageData(v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__4));
v___x_2088_ = lean_unsigned_to_nat(37u);
v___x_2089_ = lean_unsigned_to_nat(200u);
v___x_2090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__3));
v___x_2091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__2));
v___x_2092_ = l_mkPanicMessageWithDecl(v___x_2091_, v___x_2090_, v___x_2089_, v___x_2088_, v___x_2087_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0(lean_object* v_snd_2093_, lean_object* v_fst_2094_, uint8_t v___x_2095_, lean_object* v_____x_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
lean_inc(v_snd_2093_);
v___x_2104_ = l_Lean_MVarId_getType(v_snd_2093_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc_n(v_a_2105_, 2);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = l_Lean_Meta_isProp(v_a_2105_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2197_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2197_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2197_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
uint8_t v___x_2111_; 
v___x_2111_ = lean_unbox(v_a_2107_);
lean_dec(v_a_2107_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_del_object(v___x_2109_);
lean_dec(v_a_2105_);
lean_dec_ref(v_____x_2096_);
v___x_2112_ = l_Lean_MVarId_exfalso(v_snd_2093_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = l_Lean_Meta_Sym_preprocessMVar(v_a_2113_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2123_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v_fst_2094_);
lean_ctor_set(v___x_2119_, 1, v_a_2115_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_fst_2094_);
v_a_2124_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2114_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2114_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_fst_2094_);
v_a_2132_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2112_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2112_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
uint8_t v___x_2140_; 
v___x_2140_ = l_Lean_Expr_isFalse(v_a_2105_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_del_object(v___x_2109_);
lean_dec_ref(v_____x_2096_);
v___x_2141_ = l_Lean_MVarId_byContra_x3f(v_snd_2093_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
if (lean_obj_tag(v_a_2142_) == 1)
{
lean_object* v_val_2143_; lean_object* v___x_2144_; 
v_val_2143_ = lean_ctor_get(v_a_2142_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v_a_2142_, 1);
v___x_2144_ = l_Lean_Meta_Sym_preprocessMVar(v_val_2143_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = l_Lean_Meta_Sym_introN(v_a_2145_, v___x_2146_, v___x_2095_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2167_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2150_ = v___x_2147_;
v_isShared_2151_ = v_isSharedCheck_2167_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2167_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
if (lean_obj_tag(v_a_2148_) == 1)
{
lean_object* v_newDecls_2152_; lean_object* v_mvarId_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2164_; 
v_newDecls_2152_ = lean_ctor_get(v_a_2148_, 0);
v_mvarId_2153_ = lean_ctor_get(v_a_2148_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_a_2148_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2155_ = v_a_2148_;
v_isShared_2156_ = v_isSharedCheck_2164_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_mvarId_2153_);
lean_inc(v_newDecls_2152_);
lean_dec(v_a_2148_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2164_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = l_Array_append___redArg(v_fst_2094_, v_newDecls_2152_);
lean_dec_ref(v_newDecls_2152_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2157_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_mvarId_2153_);
v___x_2159_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2159_);
v___x_2161_ = v___x_2150_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_del_object(v___x_2150_);
lean_dec(v_a_2148_);
lean_dec_ref(v_fst_2094_);
v___x_2165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__1);
v___x_2166_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v___x_2165_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
return v___x_2166_;
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v_fst_2094_);
v_a_2168_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2147_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2147_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_fst_2094_);
v_a_2176_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2144_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2144_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec(v_a_2142_);
lean_dec_ref(v_fst_2094_);
v___x_2184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___closed__5);
v___x_2185_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__1(v___x_2184_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
return v___x_2185_;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_fst_2094_);
v_a_2186_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2141_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2141_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v___x_2195_; 
lean_dec_ref(v_fst_2094_);
lean_dec(v_snd_2093_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v_____x_2096_);
v___x_2195_ = v___x_2109_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_____x_2096_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_a_2105_);
lean_dec_ref(v_____x_2096_);
lean_dec_ref(v_fst_2094_);
lean_dec(v_snd_2093_);
v_a_2198_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2106_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2106_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref(v_____x_2096_);
lean_dec_ref(v_fst_2094_);
lean_dec(v_snd_2093_);
v_a_2206_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2104_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2104_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0___boxed(lean_object* v_snd_2214_, lean_object* v_fst_2215_, lean_object* v___x_2216_, lean_object* v_____x_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
uint8_t v___x_9693__boxed_2225_; lean_object* v_res_2226_; 
v___x_9693__boxed_2225_ = lean_unbox(v___x_2216_);
v_res_2226_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___lam__0(v_snd_2214_, v_fst_2215_, v___x_9693__boxed_2225_, v_____x_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(lean_object* v_goal_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0));
v___x_2238_ = 1;
lean_inc(v_goal_2229_);
v___x_2239_ = l_Lean_Meta_Sym_intros(v_goal_2229_, v___x_2237_, v___x_2238_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v_____x_2242_; lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
if (lean_obj_tag(v_a_2240_) == 0)
{
lean_object* v___x_2254_; 
lean_inc(v_goal_2229_);
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2237_);
lean_ctor_set(v___x_2254_, 1, v_goal_2229_);
v_____x_2242_ = v___x_2254_;
v_fst_2243_ = v___x_2237_;
v_snd_2244_ = v_goal_2229_;
v___y_2245_ = v_a_2230_;
v___y_2246_ = v_a_2231_;
v___y_2247_ = v_a_2232_;
v___y_2248_ = v_a_2233_;
v___y_2249_ = v_a_2234_;
v___y_2250_ = v_a_2235_;
goto v___jp_2241_;
}
else
{
lean_object* v_newDecls_2255_; lean_object* v_mvarId_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_goal_2229_);
v_newDecls_2255_ = lean_ctor_get(v_a_2240_, 0);
v_mvarId_2256_ = lean_ctor_get(v_a_2240_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v_a_2240_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_mvarId_2256_);
lean_inc(v_newDecls_2255_);
lean_dec(v_a_2240_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
lean_inc(v_mvarId_2256_);
lean_inc_ref(v_newDecls_2255_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set_tag(v___x_2258_, 0);
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_newDecls_2255_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_mvarId_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
v_____x_2242_ = v___x_2261_;
v_fst_2243_ = v_newDecls_2255_;
v_snd_2244_ = v_mvarId_2256_;
v___y_2245_ = v_a_2230_;
v___y_2246_ = v_a_2231_;
v___y_2247_ = v_a_2232_;
v___y_2248_ = v_a_2233_;
v___y_2249_ = v_a_2234_;
v___y_2250_ = v_a_2235_;
goto v___jp_2241_;
}
}
}
v___jp_2241_:
{
lean_object* v___x_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_box(v___x_2238_);
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
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_goal_2229_);
v_a_2264_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2239_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2239_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___boxed(lean_object* v_goal_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_goal_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0(lean_object* v_00_u03b1_2281_, lean_object* v_msg_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___redArg(v_msg_2282_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0___boxed(lean_object* v_00_u03b1_2291_, lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0(v_00_u03b1_2291_, v_msg_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(lean_object* v_goal_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_toGoalState_2309_; lean_object* v_mvarId_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2343_; 
v_toGoalState_2309_ = lean_ctor_get(v_goal_2301_, 0);
v_mvarId_2310_ = lean_ctor_get(v_goal_2301_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_goal_2301_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2312_ = v_goal_2301_;
v_isShared_2313_ = v_isSharedCheck_2343_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_mvarId_2310_);
lean_inc(v_toGoalState_2309_);
lean_dec(v_goal_2301_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2343_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; 
v___x_2314_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_mvarId_2310_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2334_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2334_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2334_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v_fst_2319_; lean_object* v_snd_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2333_; 
v_fst_2319_ = lean_ctor_get(v_a_2315_, 0);
v_snd_2320_ = lean_ctor_get(v_a_2315_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_a_2315_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2322_ = v_a_2315_;
v_isShared_2323_ = v_isSharedCheck_2333_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_snd_2320_);
lean_inc(v_fst_2319_);
lean_dec(v_a_2315_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2333_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 1, v_snd_2320_);
v___x_2325_ = v___x_2312_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_toGoalState_2309_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_snd_2320_);
v___x_2325_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v___x_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_fst_2319_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2327_);
v___x_2329_ = v___x_2317_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_del_object(v___x_2312_);
lean_dec_ref(v_toGoalState_2309_);
v_a_2335_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2314_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2314_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg___boxed(lean_object* v_goal_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget(lean_object* v_goal_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2353_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___boxed(lean_object* v_goal_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget(v_goal_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec(v_a_2366_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0(lean_object* v_x_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
v___x_2388_ = lean_apply_10(v_x_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, lean_box(0));
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0___boxed(lean_object* v_x_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0(v_x_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(lean_object* v_mvarId_2401_, lean_object* v_x_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___f_2413_; lean_object* v___x_2414_; 
lean_inc(v___y_2407_);
lean_inc_ref(v___y_2406_);
lean_inc(v___y_2405_);
lean_inc_ref(v___y_2404_);
lean_inc(v___y_2403_);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2413_, 0, v_x_2402_);
lean_closure_set(v___f_2413_, 1, v___y_2403_);
lean_closure_set(v___f_2413_, 2, v___y_2404_);
lean_closure_set(v___f_2413_, 3, v___y_2405_);
lean_closure_set(v___f_2413_, 4, v___y_2406_);
lean_closure_set(v___f_2413_, 5, v___y_2407_);
v___x_2414_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2401_, v___f_2413_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2414_) == 0)
{
return v___x_2414_;
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg___boxed(lean_object* v_mvarId_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2423_, v_x_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1(lean_object* v_00_u03b1_2436_, lean_object* v_mvarId_2437_, lean_object* v_x_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2437_, v_x_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___boxed(lean_object* v_00_u03b1_2450_, lean_object* v_mvarId_2451_, lean_object* v_x_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1(v_00_u03b1_2450_, v_mvarId_2451_, v_x_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0(lean_object* v_x_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
lean_inc(v___y_2471_);
lean_inc_ref(v___y_2470_);
lean_inc(v___y_2469_);
lean_inc_ref(v___y_2468_);
lean_inc(v___y_2467_);
lean_inc(v___y_2466_);
lean_inc_ref(v___y_2465_);
v___x_2477_ = lean_apply_12(v_x_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, lean_box(0));
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0___boxed(lean_object* v_x_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0(v_x_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(lean_object* v_mvarId_2492_, lean_object* v_x_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v___f_2506_; lean_object* v___x_2507_; 
lean_inc(v___y_2500_);
lean_inc_ref(v___y_2499_);
lean_inc(v___y_2498_);
lean_inc_ref(v___y_2497_);
lean_inc(v___y_2496_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_2506_, 0, v_x_2493_);
lean_closure_set(v___f_2506_, 1, v___y_2494_);
lean_closure_set(v___f_2506_, 2, v___y_2495_);
lean_closure_set(v___f_2506_, 3, v___y_2496_);
lean_closure_set(v___f_2506_, 4, v___y_2497_);
lean_closure_set(v___f_2506_, 5, v___y_2498_);
lean_closure_set(v___f_2506_, 6, v___y_2499_);
lean_closure_set(v___f_2506_, 7, v___y_2500_);
v___x_2507_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2492_, v___f_2506_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2507_) == 0)
{
return v___x_2507_;
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg___boxed(lean_object* v_mvarId_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_mvarId_2516_, v_x_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3(lean_object* v_00_u03b1_2531_, lean_object* v_mvarId_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_mvarId_2532_, v_x_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___boxed(lean_object* v_00_u03b1_2547_, lean_object* v_mvarId_2548_, lean_object* v_x_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3(v_00_u03b1_2547_, v_mvarId_2548_, v_x_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(size_t v_sz_2563_, size_t v_i_2564_, lean_object* v_bs_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
uint8_t v___x_2573_; 
v___x_2573_ = lean_usize_dec_lt(v_i_2564_, v_sz_2563_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v_bs_2565_);
return v___x_2574_;
}
else
{
lean_object* v_v_2575_; lean_object* v___x_2576_; 
v_v_2575_ = lean_array_uget(v_bs_2565_, v_i_2564_);
lean_inc(v_v_2575_);
v___x_2576_ = l_Lean_FVarId_getUserName___redArg(v_v_2575_, v___y_2568_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
lean_inc(v_v_2575_);
v___x_2578_ = l_Lean_FVarId_getType___redArg(v_v_2575_, v___y_2568_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2580_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v___x_2580_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_2579_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; lean_object* v_bs_x27_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = lean_unsigned_to_nat(0u);
v_bs_x27_2583_ = lean_array_uset(v_bs_2565_, v_i_2564_, v___x_2582_);
lean_inc(v_v_2575_);
v___x_2584_ = l_Lean_mkFVar(v_v_2575_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_v_2575_);
v___x_2586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2586_, 0, v_a_2577_);
lean_ctor_set(v___x_2586_, 1, v_a_2581_);
lean_ctor_set(v___x_2586_, 2, v___x_2584_);
lean_ctor_set(v___x_2586_, 3, v___x_2585_);
v___x_2587_ = ((size_t)1ULL);
v___x_2588_ = lean_usize_add(v_i_2564_, v___x_2587_);
v___x_2589_ = lean_array_uset(v_bs_x27_2583_, v_i_2564_, v___x_2586_);
v_i_2564_ = v___x_2588_;
v_bs_2565_ = v___x_2589_;
goto _start;
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_a_2577_);
lean_dec(v_v_2575_);
lean_dec_ref(v_bs_2565_);
v_a_2591_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2580_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2580_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_a_2577_);
lean_dec(v_v_2575_);
lean_dec_ref(v_bs_2565_);
v_a_2599_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2578_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2578_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_v_2575_);
lean_dec_ref(v_bs_2565_);
v_a_2607_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2576_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2576_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg___boxed(lean_object* v_sz_2615_, lean_object* v_i_2616_, lean_object* v_bs_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
size_t v_sz_boxed_2625_; size_t v_i_boxed_2626_; lean_object* v_res_2627_; 
v_sz_boxed_2625_ = lean_unbox_usize(v_sz_2615_);
lean_dec(v_sz_2615_);
v_i_boxed_2626_ = lean_unbox_usize(v_i_2616_);
lean_dec(v_i_2616_);
v_res_2627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_boxed_2625_, v_i_boxed_2626_, v_bs_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_Meta_getPropHyps(v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; size_t v_sz_2642_; size_t v___x_2643_; lean_object* v___x_2644_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v_sz_2642_ = lean_array_size(v_a_2641_);
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_2642_, v___x_2643_, v_a_2641_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2653_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_a_2645_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2644_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2644_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
v_a_2662_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2640_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2640_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed(lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(lean_object* v_as_2683_, size_t v_i_2684_, size_t v_stop_2685_, lean_object* v_b_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_a_2698_; uint8_t v___x_2702_; 
v___x_2702_ = lean_usize_dec_eq(v_i_2684_, v_stop_2685_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_array_uget_borrowed(v_as_2683_, v_i_2684_);
lean_inc(v___x_2703_);
v___x_2704_ = l_Lean_FVarId_getType___redArg(v___x_2703_, v___y_2692_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v___x_2706_ = l_Lean_Meta_isProp(v_a_2705_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; uint8_t v___x_2708_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2706_, 1);
v___x_2708_ = lean_unbox(v_a_2707_);
lean_dec(v_a_2707_);
if (v___x_2708_ == 0)
{
v_a_2698_ = v_b_2686_;
goto v___jp_2697_;
}
else
{
lean_object* v___x_2709_; 
lean_inc(v___x_2703_);
v___x_2709_ = l_Lean_FVarId_getUserName___redArg(v___x_2703_, v___y_2692_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
lean_inc(v___x_2703_);
v___x_2711_ = l_Lean_FVarId_getType___redArg(v___x_2703_, v___y_2692_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2713_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_2712_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
lean_inc_n(v___x_2703_, 2);
v___x_2715_ = l_Lean_mkFVar(v___x_2703_);
v___x_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2703_);
v___x_2717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2717_, 0, v_a_2710_);
lean_ctor_set(v___x_2717_, 1, v_a_2714_);
lean_ctor_set(v___x_2717_, 2, v___x_2715_);
lean_ctor_set(v___x_2717_, 3, v___x_2716_);
v___x_2718_ = lean_array_push(v_b_2686_, v___x_2717_);
v_a_2698_ = v___x_2718_;
goto v___jp_2697_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_a_2710_);
lean_dec_ref(v_b_2686_);
v_a_2719_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2713_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2713_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v_a_2710_);
lean_dec_ref(v_b_2686_);
v_a_2727_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2711_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2711_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v_b_2686_);
v_a_2735_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2709_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2709_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_b_2686_);
v_a_2743_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2706_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2706_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v_b_2686_);
v_a_2751_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2704_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2704_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
else
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_b_2686_);
return v___x_2759_;
}
v___jp_2697_:
{
size_t v___x_2699_; size_t v___x_2700_; 
v___x_2699_ = ((size_t)1ULL);
v___x_2700_ = lean_usize_add(v_i_2684_, v___x_2699_);
v_i_2684_ = v___x_2700_;
v_b_2686_ = v_a_2698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg___boxed(lean_object* v_as_2760_, lean_object* v_i_2761_, lean_object* v_stop_2762_, lean_object* v_b_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
size_t v_i_boxed_2774_; size_t v_stop_boxed_2775_; lean_object* v_res_2776_; 
v_i_boxed_2774_ = lean_unbox_usize(v_i_2761_);
lean_dec(v_i_2761_);
v_stop_boxed_2775_ = lean_unbox_usize(v_stop_2762_);
lean_dec(v_stop_2762_);
v_res_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2760_, v_i_boxed_2774_, v_stop_boxed_2775_, v_b_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v_as_2760_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(lean_object* v_as_2777_, lean_object* v_start_2778_, lean_object* v_stop_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps___closed__0));
v___x_2792_ = lean_nat_dec_lt(v_start_2778_, v_stop_2779_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
return v___x_2793_;
}
else
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = lean_array_get_size(v_as_2777_);
v___x_2795_ = lean_nat_dec_le(v_stop_2779_, v___x_2794_);
if (v___x_2795_ == 0)
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_nat_dec_lt(v_start_2778_, v___x_2794_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2791_);
return v___x_2797_;
}
else
{
size_t v___x_2798_; size_t v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = lean_usize_of_nat(v_start_2778_);
v___x_2799_ = lean_usize_of_nat(v___x_2794_);
v___x_2800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2777_, v___x_2798_, v___x_2799_, v___x_2791_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
return v___x_2800_;
}
}
else
{
size_t v___x_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = lean_usize_of_nat(v_start_2778_);
v___x_2802_ = lean_usize_of_nat(v_stop_2779_);
v___x_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_2777_, v___x_2801_, v___x_2802_, v___x_2791_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
return v___x_2803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___boxed(lean_object* v_as_2804_, lean_object* v_start_2805_, lean_object* v_stop_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(v_as_2804_, v_start_2805_, v_stop_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v_stop_2806_);
lean_dec(v_start_2805_);
lean_dec_ref(v_as_2804_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(lean_object* v_snd_2819_, lean_object* v_config_2820_, lean_object* v_fst_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v___x_2832_; lean_object* v_a_2834_; lean_object* v___y_2839_; lean_object* v___x_2849_; 
v___x_2832_ = lean_st_mk_ref(v_snd_2819_);
v___x_2849_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_collectGoalHyps(v_config_2820_, v___x_2832_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = lean_unsigned_to_nat(0u);
v___x_2852_ = lean_array_get_size(v_fst_2821_);
v___x_2853_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(v_fst_2821_, v___x_2851_, v___x_2852_, v___x_2832_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = l_Array_append___redArg(v_a_2850_, v_a_2854_);
lean_dec(v_a_2854_);
v_a_2834_ = v___x_2855_;
goto v___jp_2833_;
}
else
{
lean_dec(v_a_2850_);
v___y_2839_ = v___x_2853_;
goto v___jp_2838_;
}
}
else
{
v___y_2839_ = v___x_2849_;
goto v___jp_2838_;
}
v___jp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = lean_st_ref_get(v___x_2832_);
lean_dec(v___x_2832_);
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v_a_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
v___jp_2838_:
{
if (lean_obj_tag(v___y_2839_) == 0)
{
lean_object* v_a_2840_; 
v_a_2840_ = lean_ctor_get(v___y_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___y_2839_, 1);
v_a_2834_ = v_a_2840_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v___x_2832_);
v_a_2841_ = lean_ctor_get(v___y_2839_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___y_2839_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___y_2839_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___y_2839_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed(lean_object* v_snd_2856_, lean_object* v_config_2857_, lean_object* v_fst_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(v_snd_2856_, v_config_2857_, v_fst_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v_fst_2858_);
lean_dec_ref(v_config_2857_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___x_2939_; lean_object* v_target_2940_; 
v___x_2939_ = lean_st_ref_get(v_a_2872_);
v_target_2940_ = lean_ctor_get(v___x_2939_, 2);
lean_inc_ref(v_target_2940_);
lean_dec(v___x_2939_);
if (lean_obj_tag(v_target_2940_) == 0)
{
lean_object* v_mvar_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2985_; 
v_mvar_2941_ = lean_ctor_get(v_target_2940_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_target_2940_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2943_ = v_target_2940_;
v_isShared_2944_ = v_isSharedCheck_2985_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_mvar_2941_);
lean_dec(v_target_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2985_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; 
v___x_2945_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction(v_mvar_2941_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v_snd_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v_snd_2947_ = lean_ctor_get(v_a_2946_, 1);
lean_inc(v_snd_2947_);
lean_dec(v_a_2946_);
v___x_2948_ = l_Lean_Meta_Sym_preprocessMVar(v_snd_2947_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; lean_object* v_caches_2951_; lean_object* v_typeAnalysis_2952_; lean_object* v_hypotheses_2953_; uint8_t v_didChange_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2967_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = lean_st_ref_take(v_a_2872_);
v_caches_2951_ = lean_ctor_get(v___x_2950_, 0);
v_typeAnalysis_2952_ = lean_ctor_get(v___x_2950_, 1);
v_hypotheses_2953_ = lean_ctor_get(v___x_2950_, 3);
v_didChange_2954_ = lean_ctor_get_uint8(v___x_2950_, sizeof(void*)*4);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2967_ == 0)
{
lean_object* v_unused_2968_; 
v_unused_2968_ = lean_ctor_get(v___x_2950_, 2);
lean_dec(v_unused_2968_);
v___x_2956_ = v___x_2950_;
v_isShared_2957_ = v_isSharedCheck_2967_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_hypotheses_2953_);
lean_inc(v_typeAnalysis_2952_);
lean_inc(v_caches_2951_);
lean_dec(v___x_2950_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2967_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
lean_inc(v_a_2949_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v_a_2949_);
v___x_2959_ = v___x_2943_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2949_);
v___x_2959_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2961_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 2, v___x_2959_);
v___x_2961_ = v___x_2956_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_caches_2951_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_typeAnalysis_2952_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2965_, 3, v_hypotheses_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2965_, sizeof(void*)*4, v_didChange_2954_);
v___x_2961_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___f_2963_; lean_object* v___x_2964_; 
v___x_2962_ = lean_st_ref_put(v_a_2872_, v___x_2961_);
v___f_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0));
v___x_2964_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__3___redArg(v_a_2949_, v___f_2963_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_2964_;
}
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_del_object(v___x_2943_);
v_a_2969_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2948_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2948_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_del_object(v___x_2943_);
v_a_2977_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2945_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2945_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
else
{
lean_object* v_goal_2986_; lean_object* v_mode_2987_; uint8_t v___x_2988_; 
v_goal_2986_ = lean_ctor_get(v_target_2940_, 0);
lean_inc_ref(v_goal_2986_);
lean_dec_ref_known(v_target_2940_, 1);
v_mode_2987_ = lean_ctor_get(v_a_2871_, 1);
v___x_2988_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; 
v___x_2989_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupGrindTarget___redArg(v_goal_2986_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v_fst_2991_; lean_object* v_snd_2992_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v_fst_2991_ = lean_ctor_get(v_a_2990_, 0);
lean_inc(v_fst_2991_);
v_snd_2992_ = lean_ctor_get(v_a_2990_, 1);
lean_inc(v_snd_2992_);
lean_dec(v_a_2990_);
v_fst_2884_ = v_fst_2991_;
v_snd_2885_ = v_snd_2992_;
v___y_2886_ = v_a_2871_;
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
goto v___jp_2883_;
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
v_a_2993_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2989_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2989_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_object* v___x_3001_; 
v___x_3001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction___closed__0));
v_fst_2884_ = v___x_3001_;
v_snd_2885_ = v_goal_2986_;
v___y_2886_ = v_a_2871_;
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
goto v___jp_2883_;
}
}
v___jp_2883_:
{
lean_object* v_toGoalState_2897_; uint8_t v_inconsistent_2898_; 
v_toGoalState_2897_ = lean_ctor_get(v_snd_2885_, 0);
v_inconsistent_2898_ = lean_ctor_get_uint8(v_toGoalState_2897_, sizeof(void*)*17);
if (v_inconsistent_2898_ == 0)
{
lean_object* v_mvarId_2899_; lean_object* v_config_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v_mvarId_2899_ = lean_ctor_get(v_snd_2885_, 1);
lean_inc(v_mvarId_2899_);
v_config_2900_ = lean_ctor_get(v___y_2886_, 0);
lean_inc_ref(v_config_2900_);
v___f_2901_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed), 13, 3);
lean_closure_set(v___f_2901_, 0, v_snd_2885_);
lean_closure_set(v___f_2901_, 1, v_config_2900_);
lean_closure_set(v___f_2901_, 2, v_fst_2884_);
v___x_2902_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__1___redArg(v_mvarId_2899_, v___f_2901_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2928_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2928_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2928_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_fst_2907_; lean_object* v_snd_2908_; lean_object* v___x_2909_; lean_object* v_caches_2910_; lean_object* v_typeAnalysis_2911_; lean_object* v_hypotheses_2912_; uint8_t v_didChange_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2926_; 
v_fst_2907_ = lean_ctor_get(v_a_2903_, 0);
lean_inc(v_fst_2907_);
v_snd_2908_ = lean_ctor_get(v_a_2903_, 1);
lean_inc(v_snd_2908_);
lean_dec(v_a_2903_);
v___x_2909_ = lean_st_ref_take(v___y_2887_);
v_caches_2910_ = lean_ctor_get(v___x_2909_, 0);
v_typeAnalysis_2911_ = lean_ctor_get(v___x_2909_, 1);
v_hypotheses_2912_ = lean_ctor_get(v___x_2909_, 3);
v_didChange_2913_ = lean_ctor_get_uint8(v___x_2909_, sizeof(void*)*4);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v___x_2909_, 2);
lean_dec(v_unused_2927_);
v___x_2915_ = v___x_2909_;
v_isShared_2916_ = v_isSharedCheck_2926_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_hypotheses_2912_);
lean_inc(v_typeAnalysis_2911_);
lean_inc(v_caches_2910_);
lean_dec(v___x_2909_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2926_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2919_; 
v___x_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_snd_2908_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 2, v___x_2917_);
v___x_2919_ = v___x_2915_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_caches_2910_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_typeAnalysis_2911_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_hypotheses_2912_);
lean_ctor_set_uint8(v_reuseFailAlloc_2925_, sizeof(void*)*4, v_didChange_2913_);
v___x_2919_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2920_ = lean_st_ref_put(v___y_2887_, v___x_2919_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_fst_2907_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2921_);
v___x_2923_ = v___x_2905_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
v_a_2929_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2902_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2902_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_dec_ref(v_snd_2885_);
lean_dec_ref(v_fst_2884_);
v___x_2937_ = lean_box(0);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___boxed(lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec(v_a_3003_);
lean_dec_ref(v_a_3002_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2(size_t v_sz_3015_, size_t v_i_3016_, lean_object* v_bs_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___redArg(v_sz_3015_, v_i_3016_, v_bs_3017_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2___boxed(lean_object* v_sz_3031_, lean_object* v_i_3032_, lean_object* v_bs_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
size_t v_sz_boxed_3046_; size_t v_i_boxed_3047_; lean_object* v_res_3048_; 
v_sz_boxed_3046_ = lean_unbox_usize(v_sz_3031_);
lean_dec(v_sz_3031_);
v_i_boxed_3047_ = lean_unbox_usize(v_i_3032_);
lean_dec(v_i_3032_);
v_res_3048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__2(v_sz_boxed_3046_, v_i_boxed_3047_, v_bs_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(lean_object* v_as_3049_, size_t v_i_3050_, size_t v_stop_3051_, lean_object* v_b_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___redArg(v_as_3049_, v_i_3050_, v_stop_3051_, v_b_3052_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___boxed(lean_object* v_as_3065_, lean_object* v_i_3066_, lean_object* v_stop_3067_, lean_object* v_b_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
size_t v_i_boxed_3080_; size_t v_stop_boxed_3081_; lean_object* v_res_3082_; 
v_i_boxed_3080_ = lean_unbox_usize(v_i_3066_);
lean_dec(v_i_3066_);
v_stop_boxed_3081_ = lean_unbox_usize(v_stop_3067_);
lean_dec(v_stop_3067_);
v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(v_as_3065_, v_i_boxed_3080_, v_stop_boxed_3081_, v_b_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v_as_3065_);
return v_res_3082_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_unsigned_to_nat(32u);
v___x_3084_ = lean_mk_empty_array_with_capacity(v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3086_ = ((size_t)5ULL);
v___x_3087_ = lean_unsigned_to_nat(0u);
v___x_3088_ = lean_unsigned_to_nat(32u);
v___x_3089_ = lean_mk_empty_array_with_capacity(v___x_3088_);
v___x_3090_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__0);
v___x_3091_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___x_3089_);
lean_ctor_set(v___x_3091_, 2, v___x_3087_);
lean_ctor_set(v___x_3091_, 3, v___x_3087_);
lean_ctor_set_usize(v___x_3091_, 4, v___x_3086_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(lean_object* v___y_3092_){
_start:
{
lean_object* v___x_3094_; lean_object* v_traceState_3095_; lean_object* v_traces_3096_; lean_object* v___x_3097_; lean_object* v_traceState_3098_; lean_object* v_env_3099_; lean_object* v_nextMacroScope_3100_; lean_object* v_ngen_3101_; lean_object* v_auxDeclNGen_3102_; lean_object* v_cache_3103_; lean_object* v_messages_3104_; lean_object* v_infoState_3105_; lean_object* v_snapshotTasks_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3125_; 
v___x_3094_ = lean_st_ref_get(v___y_3092_);
v_traceState_3095_ = lean_ctor_get(v___x_3094_, 4);
lean_inc_ref(v_traceState_3095_);
lean_dec(v___x_3094_);
v_traces_3096_ = lean_ctor_get(v_traceState_3095_, 0);
lean_inc_ref(v_traces_3096_);
lean_dec_ref(v_traceState_3095_);
v___x_3097_ = lean_st_ref_take(v___y_3092_);
v_traceState_3098_ = lean_ctor_get(v___x_3097_, 4);
v_env_3099_ = lean_ctor_get(v___x_3097_, 0);
v_nextMacroScope_3100_ = lean_ctor_get(v___x_3097_, 1);
v_ngen_3101_ = lean_ctor_get(v___x_3097_, 2);
v_auxDeclNGen_3102_ = lean_ctor_get(v___x_3097_, 3);
v_cache_3103_ = lean_ctor_get(v___x_3097_, 5);
v_messages_3104_ = lean_ctor_get(v___x_3097_, 6);
v_infoState_3105_ = lean_ctor_get(v___x_3097_, 7);
v_snapshotTasks_3106_ = lean_ctor_get(v___x_3097_, 8);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3108_ = v___x_3097_;
v_isShared_3109_ = v_isSharedCheck_3125_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_snapshotTasks_3106_);
lean_inc(v_infoState_3105_);
lean_inc(v_messages_3104_);
lean_inc(v_cache_3103_);
lean_inc(v_traceState_3098_);
lean_inc(v_auxDeclNGen_3102_);
lean_inc(v_ngen_3101_);
lean_inc(v_nextMacroScope_3100_);
lean_inc(v_env_3099_);
lean_dec(v___x_3097_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3125_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
uint64_t v_tid_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3123_; 
v_tid_3110_ = lean_ctor_get_uint64(v_traceState_3098_, sizeof(void*)*1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_traceState_3098_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v_traceState_3098_, 0);
lean_dec(v_unused_3124_);
v___x_3112_ = v_traceState_3098_;
v_isShared_3113_ = v_isSharedCheck_3123_;
goto v_resetjp_3111_;
}
else
{
lean_dec(v_traceState_3098_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3123_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3114_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___closed__1);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3114_);
v___x_3116_ = v___x_3112_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3114_);
lean_ctor_set_uint64(v_reuseFailAlloc_3122_, sizeof(void*)*1, v_tid_3110_);
v___x_3116_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3118_; 
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 4, v___x_3116_);
v___x_3118_ = v___x_3108_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_env_3099_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_nextMacroScope_3100_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_ngen_3101_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_auxDeclNGen_3102_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3121_, 5, v_cache_3103_);
lean_ctor_set(v_reuseFailAlloc_3121_, 6, v_messages_3104_);
lean_ctor_set(v_reuseFailAlloc_3121_, 7, v_infoState_3105_);
lean_ctor_set(v_reuseFailAlloc_3121_, 8, v_snapshotTasks_3106_);
v___x_3118_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_st_ref_put(v___y_3092_, v___x_3118_);
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v_traces_3096_);
return v___x_3120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg___boxed(lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_3126_);
lean_dec(v___y_3126_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v___y_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___boxed(lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2(v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
return v_res_3154_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(lean_object* v_opts_3155_, lean_object* v_opt_3156_){
_start:
{
lean_object* v_name_3157_; lean_object* v_defValue_3158_; lean_object* v_map_3159_; lean_object* v___x_3160_; 
v_name_3157_ = lean_ctor_get(v_opt_3156_, 0);
v_defValue_3158_ = lean_ctor_get(v_opt_3156_, 1);
v_map_3159_ = lean_ctor_get(v_opts_3155_, 0);
v___x_3160_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3159_, v_name_3157_);
if (lean_obj_tag(v___x_3160_) == 0)
{
uint8_t v___x_3161_; 
v___x_3161_ = lean_unbox(v_defValue_3158_);
return v___x_3161_;
}
else
{
lean_object* v_val_3162_; 
v_val_3162_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_val_3162_);
lean_dec_ref_known(v___x_3160_, 1);
if (lean_obj_tag(v_val_3162_) == 1)
{
uint8_t v_v_3163_; 
v_v_3163_ = lean_ctor_get_uint8(v_val_3162_, 0);
lean_dec_ref_known(v_val_3162_, 0);
return v_v_3163_;
}
else
{
uint8_t v___x_3164_; 
lean_dec(v_val_3162_);
v___x_3164_ = lean_unbox(v_defValue_3158_);
return v___x_3164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3___boxed(lean_object* v_opts_3165_, lean_object* v_opt_3166_){
_start:
{
uint8_t v_res_3167_; lean_object* v_r_3168_; 
v_res_3167_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3165_, v_opt_3166_);
lean_dec_ref(v_opt_3166_);
lean_dec_ref(v_opts_3165_);
v_r_3168_ = lean_box(v_res_3167_);
return v_r_3168_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__0));
v___x_3171_ = l_Lean_stringToMessageData(v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(lean_object* v_x_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___closed__1);
v___x_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0___boxed(lean_object* v_x_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___lam__0(v_x_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec_ref(v_x_3187_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(lean_object* v_opts_3201_, lean_object* v_opt_3202_){
_start:
{
lean_object* v_name_3203_; lean_object* v_defValue_3204_; lean_object* v_map_3205_; lean_object* v___x_3206_; 
v_name_3203_ = lean_ctor_get(v_opt_3202_, 0);
v_defValue_3204_ = lean_ctor_get(v_opt_3202_, 1);
v_map_3205_ = lean_ctor_get(v_opts_3201_, 0);
v___x_3206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3205_, v_name_3203_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_inc(v_defValue_3204_);
return v_defValue_3204_;
}
else
{
lean_object* v_val_3207_; 
v_val_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_val_3207_);
lean_dec_ref_known(v___x_3206_, 1);
if (lean_obj_tag(v_val_3207_) == 3)
{
lean_object* v_v_3208_; 
v_v_3208_ = lean_ctor_get(v_val_3207_, 0);
lean_inc(v_v_3208_);
lean_dec_ref_known(v_val_3207_, 1);
return v_v_3208_;
}
else
{
lean_dec(v_val_3207_);
lean_inc(v_defValue_3204_);
return v_defValue_3204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8___boxed(lean_object* v_opts_3209_, lean_object* v_opt_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3209_, v_opt_3210_);
lean_dec_ref(v_opt_3210_);
lean_dec_ref(v_opts_3209_);
return v_res_3211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(lean_object* v_e_3212_){
_start:
{
if (lean_obj_tag(v_e_3212_) == 0)
{
uint8_t v___x_3213_; 
v___x_3213_ = 2;
return v___x_3213_;
}
else
{
uint8_t v___x_3214_; 
v___x_3214_ = 0;
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7___boxed(lean_object* v_e_3215_){
_start:
{
uint8_t v_res_3216_; lean_object* v_r_3217_; 
v_res_3216_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(v_e_3215_);
lean_dec_ref(v_e_3215_);
v_r_3217_ = lean_box(v_res_3216_);
return v_r_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(size_t v_sz_3218_, size_t v_i_3219_, lean_object* v_bs_3220_){
_start:
{
uint8_t v___x_3221_; 
v___x_3221_ = lean_usize_dec_lt(v_i_3219_, v_sz_3218_);
if (v___x_3221_ == 0)
{
return v_bs_3220_;
}
else
{
lean_object* v_v_3222_; lean_object* v_msg_3223_; lean_object* v___x_3224_; lean_object* v_bs_x27_3225_; size_t v___x_3226_; size_t v___x_3227_; lean_object* v___x_3228_; 
v_v_3222_ = lean_array_uget_borrowed(v_bs_3220_, v_i_3219_);
v_msg_3223_ = lean_ctor_get(v_v_3222_, 1);
lean_inc_ref(v_msg_3223_);
v___x_3224_ = lean_unsigned_to_nat(0u);
v_bs_x27_3225_ = lean_array_uset(v_bs_3220_, v_i_3219_, v___x_3224_);
v___x_3226_ = ((size_t)1ULL);
v___x_3227_ = lean_usize_add(v_i_3219_, v___x_3226_);
v___x_3228_ = lean_array_uset(v_bs_x27_3225_, v_i_3219_, v_msg_3223_);
v_i_3219_ = v___x_3227_;
v_bs_3220_ = v___x_3228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_3230_, lean_object* v_i_3231_, lean_object* v_bs_3232_){
_start:
{
size_t v_sz_boxed_3233_; size_t v_i_boxed_3234_; lean_object* v_res_3235_; 
v_sz_boxed_3233_ = lean_unbox_usize(v_sz_3230_);
lean_dec(v_sz_3230_);
v_i_boxed_3234_ = lean_unbox_usize(v_i_3231_);
lean_dec(v_i_3231_);
v_res_3235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(v_sz_boxed_3233_, v_i_boxed_3234_, v_bs_3232_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(lean_object* v_oldTraces_3236_, lean_object* v_data_3237_, lean_object* v_ref_3238_, lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_fileName_3245_; lean_object* v_fileMap_3246_; lean_object* v_options_3247_; lean_object* v_currRecDepth_3248_; lean_object* v_maxRecDepth_3249_; lean_object* v_ref_3250_; lean_object* v_currNamespace_3251_; lean_object* v_openDecls_3252_; lean_object* v_initHeartbeats_3253_; lean_object* v_maxHeartbeats_3254_; lean_object* v_quotContext_3255_; lean_object* v_currMacroScope_3256_; uint8_t v_diag_3257_; lean_object* v_cancelTk_x3f_3258_; uint8_t v_suppressElabErrors_3259_; lean_object* v_inheritedTraceOptions_3260_; lean_object* v___x_3261_; lean_object* v_traceState_3262_; lean_object* v_traces_3263_; lean_object* v_ref_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; size_t v_sz_3267_; size_t v___x_3268_; lean_object* v___x_3269_; lean_object* v_msg_3270_; lean_object* v___x_3271_; lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3309_; 
v_fileName_3245_ = lean_ctor_get(v___y_3242_, 0);
v_fileMap_3246_ = lean_ctor_get(v___y_3242_, 1);
v_options_3247_ = lean_ctor_get(v___y_3242_, 2);
v_currRecDepth_3248_ = lean_ctor_get(v___y_3242_, 3);
v_maxRecDepth_3249_ = lean_ctor_get(v___y_3242_, 4);
v_ref_3250_ = lean_ctor_get(v___y_3242_, 5);
v_currNamespace_3251_ = lean_ctor_get(v___y_3242_, 6);
v_openDecls_3252_ = lean_ctor_get(v___y_3242_, 7);
v_initHeartbeats_3253_ = lean_ctor_get(v___y_3242_, 8);
v_maxHeartbeats_3254_ = lean_ctor_get(v___y_3242_, 9);
v_quotContext_3255_ = lean_ctor_get(v___y_3242_, 10);
v_currMacroScope_3256_ = lean_ctor_get(v___y_3242_, 11);
v_diag_3257_ = lean_ctor_get_uint8(v___y_3242_, sizeof(void*)*14);
v_cancelTk_x3f_3258_ = lean_ctor_get(v___y_3242_, 12);
v_suppressElabErrors_3259_ = lean_ctor_get_uint8(v___y_3242_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3260_ = lean_ctor_get(v___y_3242_, 13);
v___x_3261_ = lean_st_ref_get(v___y_3243_);
v_traceState_3262_ = lean_ctor_get(v___x_3261_, 4);
lean_inc_ref(v_traceState_3262_);
lean_dec(v___x_3261_);
v_traces_3263_ = lean_ctor_get(v_traceState_3262_, 0);
lean_inc_ref(v_traces_3263_);
lean_dec_ref(v_traceState_3262_);
v_ref_3264_ = l_Lean_replaceRef(v_ref_3238_, v_ref_3250_);
lean_inc_ref(v_inheritedTraceOptions_3260_);
lean_inc(v_cancelTk_x3f_3258_);
lean_inc(v_currMacroScope_3256_);
lean_inc(v_quotContext_3255_);
lean_inc(v_maxHeartbeats_3254_);
lean_inc(v_initHeartbeats_3253_);
lean_inc(v_openDecls_3252_);
lean_inc(v_currNamespace_3251_);
lean_inc(v_maxRecDepth_3249_);
lean_inc(v_currRecDepth_3248_);
lean_inc_ref(v_options_3247_);
lean_inc_ref(v_fileMap_3246_);
lean_inc_ref(v_fileName_3245_);
v___x_3265_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3265_, 0, v_fileName_3245_);
lean_ctor_set(v___x_3265_, 1, v_fileMap_3246_);
lean_ctor_set(v___x_3265_, 2, v_options_3247_);
lean_ctor_set(v___x_3265_, 3, v_currRecDepth_3248_);
lean_ctor_set(v___x_3265_, 4, v_maxRecDepth_3249_);
lean_ctor_set(v___x_3265_, 5, v_ref_3264_);
lean_ctor_set(v___x_3265_, 6, v_currNamespace_3251_);
lean_ctor_set(v___x_3265_, 7, v_openDecls_3252_);
lean_ctor_set(v___x_3265_, 8, v_initHeartbeats_3253_);
lean_ctor_set(v___x_3265_, 9, v_maxHeartbeats_3254_);
lean_ctor_set(v___x_3265_, 10, v_quotContext_3255_);
lean_ctor_set(v___x_3265_, 11, v_currMacroScope_3256_);
lean_ctor_set(v___x_3265_, 12, v_cancelTk_x3f_3258_);
lean_ctor_set(v___x_3265_, 13, v_inheritedTraceOptions_3260_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*14, v_diag_3257_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*14 + 1, v_suppressElabErrors_3259_);
v___x_3266_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3263_);
lean_dec_ref(v_traces_3263_);
v_sz_3267_ = lean_array_size(v___x_3266_);
v___x_3268_ = ((size_t)0ULL);
v___x_3269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5_spec__6(v_sz_3267_, v___x_3268_, v___x_3266_);
v_msg_3270_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3270_, 0, v_data_3237_);
lean_ctor_set(v_msg_3270_, 1, v_msg_3239_);
lean_ctor_set(v_msg_3270_, 2, v___x_3269_);
v___x_3271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_3270_, v___y_3240_, v___y_3241_, v___x_3265_, v___y_3243_);
lean_dec_ref_known(v___x_3265_, 14);
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3309_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3309_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v_traceState_3277_; lean_object* v_env_3278_; lean_object* v_nextMacroScope_3279_; lean_object* v_ngen_3280_; lean_object* v_auxDeclNGen_3281_; lean_object* v_cache_3282_; lean_object* v_messages_3283_; lean_object* v_infoState_3284_; lean_object* v_snapshotTasks_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3308_; 
v___x_3276_ = lean_st_ref_take(v___y_3243_);
v_traceState_3277_ = lean_ctor_get(v___x_3276_, 4);
v_env_3278_ = lean_ctor_get(v___x_3276_, 0);
v_nextMacroScope_3279_ = lean_ctor_get(v___x_3276_, 1);
v_ngen_3280_ = lean_ctor_get(v___x_3276_, 2);
v_auxDeclNGen_3281_ = lean_ctor_get(v___x_3276_, 3);
v_cache_3282_ = lean_ctor_get(v___x_3276_, 5);
v_messages_3283_ = lean_ctor_get(v___x_3276_, 6);
v_infoState_3284_ = lean_ctor_get(v___x_3276_, 7);
v_snapshotTasks_3285_ = lean_ctor_get(v___x_3276_, 8);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3287_ = v___x_3276_;
v_isShared_3288_ = v_isSharedCheck_3308_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_snapshotTasks_3285_);
lean_inc(v_infoState_3284_);
lean_inc(v_messages_3283_);
lean_inc(v_cache_3282_);
lean_inc(v_traceState_3277_);
lean_inc(v_auxDeclNGen_3281_);
lean_inc(v_ngen_3280_);
lean_inc(v_nextMacroScope_3279_);
lean_inc(v_env_3278_);
lean_dec(v___x_3276_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3308_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
uint64_t v_tid_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3306_; 
v_tid_3289_ = lean_ctor_get_uint64(v_traceState_3277_, sizeof(void*)*1);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_traceState_3277_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v_traceState_3277_, 0);
lean_dec(v_unused_3307_);
v___x_3291_ = v_traceState_3277_;
v_isShared_3292_ = v_isSharedCheck_3306_;
goto v_resetjp_3290_;
}
else
{
lean_dec(v_traceState_3277_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3306_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_ref_3238_);
lean_ctor_set(v___x_3293_, 1, v_a_3272_);
v___x_3294_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3236_, v___x_3293_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3294_);
v___x_3296_ = v___x_3291_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3294_);
lean_ctor_set_uint64(v_reuseFailAlloc_3305_, sizeof(void*)*1, v_tid_3289_);
v___x_3296_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 4, v___x_3296_);
v___x_3298_ = v___x_3287_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_env_3278_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_nextMacroScope_3279_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_ngen_3280_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_auxDeclNGen_3281_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3304_, 5, v_cache_3282_);
lean_ctor_set(v_reuseFailAlloc_3304_, 6, v_messages_3283_);
lean_ctor_set(v_reuseFailAlloc_3304_, 7, v_infoState_3284_);
lean_ctor_set(v_reuseFailAlloc_3304_, 8, v_snapshotTasks_3285_);
v___x_3298_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3299_ = lean_st_ref_put(v___y_3243_, v___x_3298_);
v___x_3300_ = lean_box(0);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3300_);
v___x_3302_ = v___x_3274_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg___boxed(lean_object* v_oldTraces_3310_, lean_object* v_data_3311_, lean_object* v_ref_3312_, lean_object* v_msg_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3310_, v_data_3311_, v_ref_3312_, v_msg_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(lean_object* v_x_3320_){
_start:
{
if (lean_obj_tag(v_x_3320_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
v_a_3322_ = lean_ctor_get(v_x_3320_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_x_3320_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v_x_3320_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v_x_3320_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 1);
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_a_3330_ = lean_ctor_get(v_x_3320_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_x_3320_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v_x_3320_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v_x_3320_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 0);
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg___boxed(lean_object* v_x_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_x_3338_);
return v_res_3340_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0(void){
_start:
{
lean_object* v___x_3341_; double v___x_3342_; 
v___x_3341_ = lean_unsigned_to_nat(0u);
v___x_3342_ = lean_float_of_nat(v___x_3341_);
return v___x_3342_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__1));
v___x_3345_ = l_Lean_stringToMessageData(v___x_3344_);
return v___x_3345_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3346_; double v___x_3347_; 
v___x_3346_ = lean_unsigned_to_nat(1000u);
v___x_3347_ = lean_float_of_nat(v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(lean_object* v_cls_3348_, uint8_t v_collapsed_3349_, lean_object* v_tag_3350_, lean_object* v_opts_3351_, uint8_t v_clsEnabled_3352_, lean_object* v_oldTraces_3353_, lean_object* v_msg_3354_, lean_object* v_resStartStop_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v_data_3373_; lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___y_3381_; lean_object* v_a_3382_; uint8_t v___y_3397_; double v___y_3428_; 
v_fst_3368_ = lean_ctor_get(v_resStartStop_3355_, 0);
lean_inc(v_fst_3368_);
v_snd_3369_ = lean_ctor_get(v_resStartStop_3355_, 1);
lean_inc(v_snd_3369_);
lean_dec_ref(v_resStartStop_3355_);
v_fst_3376_ = lean_ctor_get(v_snd_3369_, 0);
lean_inc(v_fst_3376_);
v_snd_3377_ = lean_ctor_get(v_snd_3369_, 1);
lean_inc(v_snd_3377_);
lean_dec(v_snd_3369_);
v___x_3378_ = l_Lean_trace_profiler;
v___x_3379_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3351_, v___x_3378_);
if (v___x_3379_ == 0)
{
v___y_3397_ = v___x_3379_;
goto v___jp_3396_;
}
else
{
lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3434_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_opts_3351_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; double v___x_3437_; double v___x_3438_; double v___x_3439_; 
v___x_3435_ = l_Lean_trace_profiler_threshold;
v___x_3436_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3351_, v___x_3435_);
v___x_3437_ = lean_float_of_nat(v___x_3436_);
v___x_3438_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__3);
v___x_3439_ = lean_float_div(v___x_3437_, v___x_3438_);
v___y_3428_ = v___x_3439_;
goto v___jp_3427_;
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; double v___x_3442_; 
v___x_3440_ = l_Lean_trace_profiler_threshold;
v___x_3441_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__8(v_opts_3351_, v___x_3440_);
v___x_3442_ = lean_float_of_nat(v___x_3441_);
v___y_3428_ = v___x_3442_;
goto v___jp_3427_;
}
}
v___jp_3370_:
{
lean_object* v___x_3374_; 
lean_inc(v___y_3372_);
v___x_3374_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3353_, v_data_3373_, v___y_3372_, v___y_3371_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v___x_3375_; 
lean_dec_ref_known(v___x_3374_, 1);
v___x_3375_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_fst_3368_);
return v___x_3375_;
}
else
{
lean_dec(v_fst_3368_);
return v___x_3374_;
}
}
v___jp_3380_:
{
uint8_t v_result_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; double v___x_3386_; lean_object* v_data_3387_; 
v_result_3383_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__7(v_fst_3368_);
v___x_3384_ = lean_box(v_result_3383_);
v___x_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
v___x_3386_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0);
lean_inc_ref(v_tag_3350_);
lean_inc_ref(v___x_3385_);
lean_inc(v_cls_3348_);
v_data_3387_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3387_, 0, v_cls_3348_);
lean_ctor_set(v_data_3387_, 1, v___x_3385_);
lean_ctor_set(v_data_3387_, 2, v_tag_3350_);
lean_ctor_set_float(v_data_3387_, sizeof(void*)*3, v___x_3386_);
lean_ctor_set_float(v_data_3387_, sizeof(void*)*3 + 8, v___x_3386_);
lean_ctor_set_uint8(v_data_3387_, sizeof(void*)*3 + 16, v_collapsed_3349_);
if (v___x_3379_ == 0)
{
lean_dec_ref_known(v___x_3385_, 1);
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec_ref(v_tag_3350_);
lean_dec(v_cls_3348_);
v___y_3371_ = v_a_3382_;
v___y_3372_ = v___y_3381_;
v_data_3373_ = v_data_3387_;
goto v___jp_3370_;
}
else
{
lean_object* v_data_3388_; double v___x_3389_; double v___x_3390_; 
lean_dec_ref_known(v_data_3387_, 3);
v_data_3388_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3388_, 0, v_cls_3348_);
lean_ctor_set(v_data_3388_, 1, v___x_3385_);
lean_ctor_set(v_data_3388_, 2, v_tag_3350_);
v___x_3389_ = lean_unbox_float(v_fst_3376_);
lean_dec(v_fst_3376_);
lean_ctor_set_float(v_data_3388_, sizeof(void*)*3, v___x_3389_);
v___x_3390_ = lean_unbox_float(v_snd_3377_);
lean_dec(v_snd_3377_);
lean_ctor_set_float(v_data_3388_, sizeof(void*)*3 + 8, v___x_3390_);
lean_ctor_set_uint8(v_data_3388_, sizeof(void*)*3 + 16, v_collapsed_3349_);
v___y_3371_ = v_a_3382_;
v___y_3372_ = v___y_3381_;
v_data_3373_ = v_data_3388_;
goto v___jp_3370_;
}
}
v___jp_3391_:
{
lean_object* v_ref_3392_; lean_object* v___x_3393_; 
v_ref_3392_ = lean_ctor_get(v___y_3365_, 5);
lean_inc(v___y_3366_);
lean_inc_ref(v___y_3365_);
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3363_);
lean_inc(v___y_3362_);
lean_inc_ref(v___y_3361_);
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
lean_inc(v___y_3358_);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
lean_inc(v_fst_3368_);
v___x_3393_ = lean_apply_13(v_msg_3354_, v_fst_3368_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, lean_box(0));
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v___y_3381_ = v_ref_3392_;
v_a_3382_ = v_a_3394_;
goto v___jp_3380_;
}
else
{
lean_object* v___x_3395_; 
lean_dec_ref_known(v___x_3393_, 1);
v___x_3395_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__2);
v___y_3381_ = v_ref_3392_;
v_a_3382_ = v___x_3395_;
goto v___jp_3380_;
}
}
v___jp_3396_:
{
if (v_clsEnabled_3352_ == 0)
{
if (v___y_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v_traceState_3399_; lean_object* v_env_3400_; lean_object* v_nextMacroScope_3401_; lean_object* v_ngen_3402_; lean_object* v_auxDeclNGen_3403_; lean_object* v_cache_3404_; lean_object* v_messages_3405_; lean_object* v_infoState_3406_; lean_object* v_snapshotTasks_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_snd_3377_);
lean_dec(v_fst_3376_);
lean_dec_ref(v_msg_3354_);
lean_dec_ref(v_tag_3350_);
lean_dec(v_cls_3348_);
v___x_3398_ = lean_st_ref_take(v___y_3366_);
v_traceState_3399_ = lean_ctor_get(v___x_3398_, 4);
v_env_3400_ = lean_ctor_get(v___x_3398_, 0);
v_nextMacroScope_3401_ = lean_ctor_get(v___x_3398_, 1);
v_ngen_3402_ = lean_ctor_get(v___x_3398_, 2);
v_auxDeclNGen_3403_ = lean_ctor_get(v___x_3398_, 3);
v_cache_3404_ = lean_ctor_get(v___x_3398_, 5);
v_messages_3405_ = lean_ctor_get(v___x_3398_, 6);
v_infoState_3406_ = lean_ctor_get(v___x_3398_, 7);
v_snapshotTasks_3407_ = lean_ctor_get(v___x_3398_, 8);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3409_ = v___x_3398_;
v_isShared_3410_ = v_isSharedCheck_3426_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_snapshotTasks_3407_);
lean_inc(v_infoState_3406_);
lean_inc(v_messages_3405_);
lean_inc(v_cache_3404_);
lean_inc(v_traceState_3399_);
lean_inc(v_auxDeclNGen_3403_);
lean_inc(v_ngen_3402_);
lean_inc(v_nextMacroScope_3401_);
lean_inc(v_env_3400_);
lean_dec(v___x_3398_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3426_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
uint64_t v_tid_3411_; lean_object* v_traces_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3425_; 
v_tid_3411_ = lean_ctor_get_uint64(v_traceState_3399_, sizeof(void*)*1);
v_traces_3412_ = lean_ctor_get(v_traceState_3399_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_traceState_3399_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3414_ = v_traceState_3399_;
v_isShared_3415_ = v_isSharedCheck_3425_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_traces_3412_);
lean_dec(v_traceState_3399_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3425_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3353_, v_traces_3412_);
lean_dec_ref(v_traces_3412_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3416_);
lean_ctor_set_uint64(v_reuseFailAlloc_3424_, sizeof(void*)*1, v_tid_3411_);
v___x_3418_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 4, v___x_3418_);
v___x_3420_ = v___x_3409_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_env_3400_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_nextMacroScope_3401_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_ngen_3402_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v_auxDeclNGen_3403_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3423_, 5, v_cache_3404_);
lean_ctor_set(v_reuseFailAlloc_3423_, 6, v_messages_3405_);
lean_ctor_set(v_reuseFailAlloc_3423_, 7, v_infoState_3406_);
lean_ctor_set(v_reuseFailAlloc_3423_, 8, v_snapshotTasks_3407_);
v___x_3420_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_st_ref_put(v___y_3366_, v___x_3420_);
v___x_3422_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_fst_3368_);
return v___x_3422_;
}
}
}
}
}
else
{
goto v___jp_3391_;
}
}
else
{
goto v___jp_3391_;
}
}
v___jp_3427_:
{
double v___x_3429_; double v___x_3430_; double v___x_3431_; uint8_t v___x_3432_; 
v___x_3429_ = lean_unbox_float(v_snd_3377_);
v___x_3430_ = lean_unbox_float(v_fst_3376_);
v___x_3431_ = lean_float_sub(v___x_3429_, v___x_3430_);
v___x_3432_ = lean_float_decLt(v___y_3428_, v___x_3431_);
v___y_3397_ = v___x_3432_;
goto v___jp_3396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___boxed(lean_object** _args){
lean_object* v_cls_3443_ = _args[0];
lean_object* v_collapsed_3444_ = _args[1];
lean_object* v_tag_3445_ = _args[2];
lean_object* v_opts_3446_ = _args[3];
lean_object* v_clsEnabled_3447_ = _args[4];
lean_object* v_oldTraces_3448_ = _args[5];
lean_object* v_msg_3449_ = _args[6];
lean_object* v_resStartStop_3450_ = _args[7];
lean_object* v___y_3451_ = _args[8];
lean_object* v___y_3452_ = _args[9];
lean_object* v___y_3453_ = _args[10];
lean_object* v___y_3454_ = _args[11];
lean_object* v___y_3455_ = _args[12];
lean_object* v___y_3456_ = _args[13];
lean_object* v___y_3457_ = _args[14];
lean_object* v___y_3458_ = _args[15];
lean_object* v___y_3459_ = _args[16];
lean_object* v___y_3460_ = _args[17];
lean_object* v___y_3461_ = _args[18];
lean_object* v___y_3462_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_3463_; uint8_t v_clsEnabled_boxed_3464_; lean_object* v_res_3465_; 
v_collapsed_boxed_3463_ = lean_unbox(v_collapsed_3444_);
v_clsEnabled_boxed_3464_ = lean_unbox(v_clsEnabled_3447_);
v_res_3465_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v_cls_3443_, v_collapsed_boxed_3463_, v_tag_3445_, v_opts_3446_, v_clsEnabled_boxed_3464_, v_oldTraces_3448_, v_msg_3449_, v_resStartStop_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec_ref(v_opts_3446_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(lean_object* v_cls_3469_, lean_object* v_msg_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_ref_3476_; lean_object* v___x_3477_; lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3522_; 
v_ref_3476_ = lean_ctor_get(v___y_3473_, 5);
v___x_3477_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_symByContradiction_spec__0_spec__0(v_msg_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3522_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3522_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; lean_object* v_traceState_3483_; lean_object* v_env_3484_; lean_object* v_nextMacroScope_3485_; lean_object* v_ngen_3486_; lean_object* v_auxDeclNGen_3487_; lean_object* v_cache_3488_; lean_object* v_messages_3489_; lean_object* v_infoState_3490_; lean_object* v_snapshotTasks_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3521_; 
v___x_3482_ = lean_st_ref_take(v___y_3474_);
v_traceState_3483_ = lean_ctor_get(v___x_3482_, 4);
v_env_3484_ = lean_ctor_get(v___x_3482_, 0);
v_nextMacroScope_3485_ = lean_ctor_get(v___x_3482_, 1);
v_ngen_3486_ = lean_ctor_get(v___x_3482_, 2);
v_auxDeclNGen_3487_ = lean_ctor_get(v___x_3482_, 3);
v_cache_3488_ = lean_ctor_get(v___x_3482_, 5);
v_messages_3489_ = lean_ctor_get(v___x_3482_, 6);
v_infoState_3490_ = lean_ctor_get(v___x_3482_, 7);
v_snapshotTasks_3491_ = lean_ctor_get(v___x_3482_, 8);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3493_ = v___x_3482_;
v_isShared_3494_ = v_isSharedCheck_3521_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_snapshotTasks_3491_);
lean_inc(v_infoState_3490_);
lean_inc(v_messages_3489_);
lean_inc(v_cache_3488_);
lean_inc(v_traceState_3483_);
lean_inc(v_auxDeclNGen_3487_);
lean_inc(v_ngen_3486_);
lean_inc(v_nextMacroScope_3485_);
lean_inc(v_env_3484_);
lean_dec(v___x_3482_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3521_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
uint64_t v_tid_3495_; lean_object* v_traces_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3520_; 
v_tid_3495_ = lean_ctor_get_uint64(v_traceState_3483_, sizeof(void*)*1);
v_traces_3496_ = lean_ctor_get(v_traceState_3483_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_traceState_3483_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3498_ = v_traceState_3483_;
v_isShared_3499_ = v_isSharedCheck_3520_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_traces_3496_);
lean_dec(v_traceState_3483_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3520_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; double v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4___closed__0);
v___x_3502_ = 0;
v___x_3503_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0));
v___x_3504_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3504_, 0, v_cls_3469_);
lean_ctor_set(v___x_3504_, 1, v___x_3500_);
lean_ctor_set(v___x_3504_, 2, v___x_3503_);
lean_ctor_set_float(v___x_3504_, sizeof(void*)*3, v___x_3501_);
lean_ctor_set_float(v___x_3504_, sizeof(void*)*3 + 8, v___x_3501_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*3 + 16, v___x_3502_);
v___x_3505_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__1));
v___x_3506_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set(v___x_3506_, 1, v_a_3478_);
lean_ctor_set(v___x_3506_, 2, v___x_3505_);
lean_inc(v_ref_3476_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v_ref_3476_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = l_Lean_PersistentArray_push___redArg(v_traces_3496_, v___x_3507_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3508_);
v___x_3510_ = v___x_3498_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3508_);
lean_ctor_set_uint64(v_reuseFailAlloc_3519_, sizeof(void*)*1, v_tid_3495_);
v___x_3510_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v___x_3510_);
v___x_3512_ = v___x_3493_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_env_3484_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_nextMacroScope_3485_);
lean_ctor_set(v_reuseFailAlloc_3518_, 2, v_ngen_3486_);
lean_ctor_set(v_reuseFailAlloc_3518_, 3, v_auxDeclNGen_3487_);
lean_ctor_set(v_reuseFailAlloc_3518_, 4, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3518_, 5, v_cache_3488_);
lean_ctor_set(v_reuseFailAlloc_3518_, 6, v_messages_3489_);
lean_ctor_set(v_reuseFailAlloc_3518_, 7, v_infoState_3490_);
lean_ctor_set(v_reuseFailAlloc_3518_, 8, v_snapshotTasks_3491_);
v___x_3512_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3513_ = lean_st_ref_put(v___y_3474_, v___x_3512_);
v___x_3514_ = lean_box(0);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3514_);
v___x_3516_ = v___x_3480_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___boxed(lean_object* v_cls_3523_, lean_object* v_msg_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v_cls_3523_, v_msg_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
return v_res_3530_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__5));
v___x_3543_ = l_Lean_Name_append(v___x_3542_, v___x_3541_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(lean_object* v_as_3544_, size_t v_i_3545_, size_t v_stop_3546_, lean_object* v_b_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_a_3561_; uint8_t v___x_3567_; 
v___x_3567_ = lean_usize_dec_eq(v_i_3545_, v_stop_3546_);
if (v___x_3567_ == 0)
{
lean_object* v_options_3568_; uint8_t v_hasTrace_3569_; 
v_options_3568_ = lean_ctor_get(v___y_3557_, 2);
v_hasTrace_3569_ = lean_ctor_get_uint8(v_options_3568_, sizeof(void*)*1);
if (v_hasTrace_3569_ == 0)
{
goto v___jp_3565_;
}
else
{
lean_object* v_inheritedTraceOptions_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; 
v_inheritedTraceOptions_3570_ = lean_ctor_get(v___y_3557_, 13);
v___x_3571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3572_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3573_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3570_, v_options_3568_, v___x_3572_);
if (v___x_3573_ == 0)
{
goto v___jp_3565_;
}
else
{
lean_object* v___x_3574_; lean_object* v_type_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3574_ = lean_array_uget_borrowed(v_as_3544_, v_i_3545_);
v_type_3575_ = lean_ctor_get(v___x_3574_, 1);
lean_inc_ref(v_type_3575_);
v___x_3576_ = l_Lean_MessageData_ofExpr(v_type_3575_);
v___x_3577_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v___x_3571_, v___x_3576_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v_a_3561_ = v_a_3578_;
goto v___jp_3560_;
}
else
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v___x_3579_; 
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v_b_3547_);
return v___x_3579_;
}
v___jp_3560_:
{
size_t v___x_3562_; size_t v___x_3563_; 
v___x_3562_ = ((size_t)1ULL);
v___x_3563_ = lean_usize_add(v_i_3545_, v___x_3562_);
v_i_3545_ = v___x_3563_;
v_b_3547_ = v_a_3561_;
goto _start;
}
v___jp_3565_:
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_box(0);
v_a_3561_ = v___x_3566_;
goto v___jp_3560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___boxed(lean_object* v_as_3580_, lean_object* v_i_3581_, lean_object* v_stop_3582_, lean_object* v_b_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
size_t v_i_boxed_3596_; size_t v_stop_boxed_3597_; lean_object* v_res_3598_; 
v_i_boxed_3596_ = lean_unbox_usize(v_i_3581_);
lean_dec(v_i_3581_);
v_stop_boxed_3597_ = lean_unbox_usize(v_stop_3582_);
lean_dec(v_stop_3582_);
v_res_3598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(v_as_3580_, v_i_boxed_3596_, v_stop_boxed_3597_, v_b_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec_ref(v_as_3580_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(lean_object* v_as_3599_, size_t v_i_3600_, size_t v_stop_3601_, lean_object* v_b_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_a_3616_; uint8_t v___x_3622_; 
v___x_3622_ = lean_usize_dec_eq(v_i_3600_, v_stop_3601_);
if (v___x_3622_ == 0)
{
lean_object* v_options_3623_; uint8_t v_hasTrace_3624_; 
v_options_3623_ = lean_ctor_get(v___y_3612_, 2);
v_hasTrace_3624_ = lean_ctor_get_uint8(v_options_3623_, sizeof(void*)*1);
if (v_hasTrace_3624_ == 0)
{
goto v___jp_3620_;
}
else
{
lean_object* v_inheritedTraceOptions_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v_inheritedTraceOptions_3625_ = lean_ctor_get(v___y_3612_, 13);
v___x_3626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3627_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3628_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3625_, v_options_3623_, v___x_3627_);
if (v___x_3628_ == 0)
{
goto v___jp_3620_;
}
else
{
lean_object* v___x_3629_; lean_object* v_type_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3629_ = lean_array_uget_borrowed(v_as_3599_, v_i_3600_);
v_type_3630_ = lean_ctor_get(v___x_3629_, 1);
lean_inc_ref(v_type_3630_);
v___x_3631_ = l_Lean_MessageData_ofExpr(v_type_3630_);
v___x_3632_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v___x_3626_, v___x_3631_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v_a_3616_ = v_a_3633_;
goto v___jp_3615_;
}
else
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v___x_3634_; 
v___x_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3634_, 0, v_b_3602_);
return v___x_3634_;
}
v___jp_3615_:
{
size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = ((size_t)1ULL);
v___x_3618_ = lean_usize_add(v_i_3600_, v___x_3617_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1(v_as_3599_, v___x_3618_, v_stop_3601_, v_a_3616_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
return v___x_3619_;
}
v___jp_3620_:
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_box(0);
v_a_3616_ = v___x_3621_;
goto v___jp_3615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1___boxed(lean_object* v_as_3635_, lean_object* v_i_3636_, lean_object* v_stop_3637_, lean_object* v_b_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
size_t v_i_boxed_3651_; size_t v_stop_boxed_3652_; lean_object* v_res_3653_; 
v_i_boxed_3651_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_stop_boxed_3652_ = lean_unbox_usize(v_stop_3637_);
lean_dec(v_stop_3637_);
v_res_3653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_as_3635_, v_i_boxed_3651_, v_stop_boxed_3652_, v_b_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v_as_3635_);
return v_res_3653_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1(void){
_start:
{
lean_object* v___x_3655_; double v___x_3656_; 
v___x_3655_ = lean_unsigned_to_nat(1000000000u);
v___x_3656_ = lean_float_of_nat(v___x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3834_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3834_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3834_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
if (lean_obj_tag(v_a_3670_) == 1)
{
lean_object* v_val_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3828_; 
v_val_3674_ = lean_ctor_get(v_a_3670_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_a_3670_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3676_ = v_a_3670_;
v_isShared_3677_ = v_isSharedCheck_3828_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_val_3674_);
lean_dec(v_a_3670_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3828_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___y_3699_; lean_object* v_options_3708_; lean_object* v_inheritedTraceOptions_3709_; uint8_t v_hasTrace_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_options_3708_ = lean_ctor_get(v_a_3666_, 2);
v_inheritedTraceOptions_3709_ = lean_ctor_get(v_a_3666_, 13);
v_hasTrace_3710_ = lean_ctor_get_uint8(v_options_3708_, sizeof(void*)*1);
v___x_3711_ = lean_unsigned_to_nat(0u);
v___x_3712_ = lean_array_get_size(v_val_3674_);
if (v_hasTrace_3710_ == 0)
{
uint8_t v___x_3713_; 
lean_del_object(v___x_3676_);
v___x_3713_ = lean_nat_dec_lt(v___x_3711_, v___x_3712_);
if (v___x_3713_ == 0)
{
goto v___jp_3678_;
}
else
{
lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3714_ = lean_box(0);
v___x_3715_ = lean_nat_dec_le(v___x_3712_, v___x_3712_);
if (v___x_3715_ == 0)
{
if (v___x_3713_ == 0)
{
goto v___jp_3678_;
}
else
{
size_t v___x_3716_; size_t v___x_3717_; lean_object* v___x_3718_; 
v___x_3716_ = ((size_t)0ULL);
v___x_3717_ = lean_usize_of_nat(v___x_3712_);
v___x_3718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3674_, v___x_3716_, v___x_3717_, v___x_3714_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3699_ = v___x_3718_;
goto v___jp_3698_;
}
}
else
{
size_t v___x_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = ((size_t)0ULL);
v___x_3720_ = lean_usize_of_nat(v___x_3712_);
v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3674_, v___x_3719_, v___x_3720_, v___x_3714_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3699_ = v___x_3721_;
goto v___jp_3698_;
}
}
}
else
{
lean_object* v___f_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v_a_3730_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v_a_3745_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_a_3765_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v_a_3777_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; 
v___f_3722_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__0));
v___x_3723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__3));
v___x_3724_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg___closed__0));
v___x_3725_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1_spec__1___closed__6);
v___x_3726_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3709_, v_options_3708_, v___x_3725_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3817_ = l_Lean_trace_profiler;
v___x_3818_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_options_3708_, v___x_3817_);
if (v___x_3818_ == 0)
{
uint8_t v___x_3819_; 
lean_del_object(v___x_3676_);
v___x_3819_ = lean_nat_dec_lt(v___x_3711_, v___x_3712_);
if (v___x_3819_ == 0)
{
goto v___jp_3678_;
}
else
{
lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3820_ = lean_box(0);
v___x_3821_ = lean_nat_dec_le(v___x_3712_, v___x_3712_);
if (v___x_3821_ == 0)
{
if (v___x_3819_ == 0)
{
goto v___jp_3678_;
}
else
{
size_t v___x_3822_; size_t v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = ((size_t)0ULL);
v___x_3823_ = lean_usize_of_nat(v___x_3712_);
v___x_3824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3674_, v___x_3822_, v___x_3823_, v___x_3820_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3699_ = v___x_3824_;
goto v___jp_3698_;
}
}
else
{
size_t v___x_3825_; size_t v___x_3826_; lean_object* v___x_3827_; 
v___x_3825_ = ((size_t)0ULL);
v___x_3826_ = lean_usize_of_nat(v___x_3712_);
v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3674_, v___x_3825_, v___x_3826_, v___x_3820_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3699_ = v___x_3827_;
goto v___jp_3698_;
}
}
}
else
{
goto v___jp_3792_;
}
}
else
{
goto v___jp_3792_;
}
v___jp_3727_:
{
lean_object* v___x_3731_; double v___x_3732_; double v___x_3733_; double v___x_3734_; double v___x_3735_; double v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3731_ = lean_io_mono_nanos_now();
v___x_3732_ = lean_float_of_nat(v___y_3729_);
v___x_3733_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___closed__1);
v___x_3734_ = lean_float_div(v___x_3732_, v___x_3733_);
v___x_3735_ = lean_float_of_nat(v___x_3731_);
v___x_3736_ = lean_float_div(v___x_3735_, v___x_3733_);
v___x_3737_ = lean_box_float(v___x_3734_);
v___x_3738_ = lean_box_float(v___x_3736_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v_a_3730_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v___x_3723_, v_hasTrace_3710_, v___x_3724_, v_options_3708_, v___x_3726_, v___y_3728_, v___f_3722_, v___x_3740_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3699_ = v___x_3741_;
goto v___jp_3698_;
}
v___jp_3742_:
{
lean_object* v___x_3747_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v_a_3745_);
v___x_3747_ = v___x_3676_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
v___y_3728_ = v___y_3744_;
v___y_3729_ = v___y_3743_;
v_a_3730_ = v___x_3747_;
goto v___jp_3727_;
}
}
v___jp_3749_:
{
if (lean_obj_tag(v___y_3752_) == 0)
{
lean_object* v_a_3753_; 
v_a_3753_ = lean_ctor_get(v___y_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___y_3752_, 1);
v___y_3743_ = v___y_3751_;
v___y_3744_ = v___y_3750_;
v_a_3745_ = v_a_3753_;
goto v___jp_3742_;
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_del_object(v___x_3676_);
v_a_3754_ = lean_ctor_get(v___y_3752_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___y_3752_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___y_3752_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___y_3752_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
lean_ctor_set_tag(v___x_3756_, 0);
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
v___y_3728_ = v___y_3750_;
v___y_3729_ = v___y_3751_;
v_a_3730_ = v___x_3759_;
goto v___jp_3727_;
}
}
}
}
v___jp_3762_:
{
lean_object* v___x_3766_; double v___x_3767_; double v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3766_ = lean_io_get_num_heartbeats();
v___x_3767_ = lean_float_of_nat(v___y_3763_);
v___x_3768_ = lean_float_of_nat(v___x_3766_);
v___x_3769_ = lean_box_float(v___x_3767_);
v___x_3770_ = lean_box_float(v___x_3768_);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3772_, 0, v_a_3765_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4(v___x_3723_, v_hasTrace_3710_, v___x_3724_, v_options_3708_, v___x_3726_, v___y_3764_, v___f_3722_, v___x_3772_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3699_ = v___x_3773_;
goto v___jp_3698_;
}
v___jp_3774_:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3778_, 0, v_a_3777_);
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v_a_3765_ = v___x_3778_;
goto v___jp_3762_;
}
v___jp_3779_:
{
if (lean_obj_tag(v___y_3782_) == 0)
{
lean_object* v_a_3783_; 
v_a_3783_ = lean_ctor_get(v___y_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___y_3782_, 1);
v___y_3775_ = v___y_3780_;
v___y_3776_ = v___y_3781_;
v_a_3777_ = v_a_3783_;
goto v___jp_3774_;
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_a_3784_ = lean_ctor_get(v___y_3782_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___y_3782_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___y_3782_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___y_3782_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set_tag(v___x_3786_, 0);
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
v___y_3763_ = v___y_3780_;
v___y_3764_ = v___y_3781_;
v_a_3765_ = v___x_3789_;
goto v___jp_3762_;
}
}
}
}
v___jp_3792_:
{
lean_object* v___x_3793_; lean_object* v_a_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
v___x_3793_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__2___redArg(v_a_3667_);
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3796_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__3(v_options_3708_, v___x_3795_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; 
v___x_3797_ = lean_io_mono_nanos_now();
v___x_3798_ = lean_box(0);
v___x_3799_ = lean_nat_dec_lt(v___x_3711_, v___x_3712_);
if (v___x_3799_ == 0)
{
v___y_3743_ = v___x_3797_;
v___y_3744_ = v_a_3794_;
v_a_3745_ = v___x_3798_;
goto v___jp_3742_;
}
else
{
uint8_t v___x_3800_; 
v___x_3800_ = lean_nat_dec_le(v___x_3712_, v___x_3712_);
if (v___x_3800_ == 0)
{
if (v___x_3799_ == 0)
{
v___y_3743_ = v___x_3797_;
v___y_3744_ = v_a_3794_;
v_a_3745_ = v___x_3798_;
goto v___jp_3742_;
}
else
{
size_t v___x_3801_; size_t v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = ((size_t)0ULL);
v___x_3802_ = lean_usize_of_nat(v___x_3712_);
v___x_3803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3674_, v___x_3801_, v___x_3802_, v___x_3798_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3750_ = v_a_3794_;
v___y_3751_ = v___x_3797_;
v___y_3752_ = v___x_3803_;
goto v___jp_3749_;
}
}
else
{
size_t v___x_3804_; size_t v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = ((size_t)0ULL);
v___x_3805_ = lean_usize_of_nat(v___x_3712_);
v___x_3806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3674_, v___x_3804_, v___x_3805_, v___x_3798_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3750_ = v_a_3794_;
v___y_3751_ = v___x_3797_;
v___y_3752_ = v___x_3806_;
goto v___jp_3749_;
}
}
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
lean_del_object(v___x_3676_);
v___x_3807_ = lean_io_get_num_heartbeats();
v___x_3808_ = lean_box(0);
v___x_3809_ = lean_nat_dec_lt(v___x_3711_, v___x_3712_);
if (v___x_3809_ == 0)
{
v___y_3775_ = v___x_3807_;
v___y_3776_ = v_a_3794_;
v_a_3777_ = v___x_3808_;
goto v___jp_3774_;
}
else
{
uint8_t v___x_3810_; 
v___x_3810_ = lean_nat_dec_le(v___x_3712_, v___x_3712_);
if (v___x_3810_ == 0)
{
if (v___x_3809_ == 0)
{
v___y_3775_ = v___x_3807_;
v___y_3776_ = v_a_3794_;
v_a_3777_ = v___x_3808_;
goto v___jp_3774_;
}
else
{
size_t v___x_3811_; size_t v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = ((size_t)0ULL);
v___x_3812_ = lean_usize_of_nat(v___x_3712_);
v___x_3813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3674_, v___x_3811_, v___x_3812_, v___x_3808_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3780_ = v___x_3807_;
v___y_3781_ = v_a_3794_;
v___y_3782_ = v___x_3813_;
goto v___jp_3779_;
}
}
else
{
size_t v___x_3814_; size_t v___x_3815_; lean_object* v___x_3816_; 
v___x_3814_ = ((size_t)0ULL);
v___x_3815_ = lean_usize_of_nat(v___x_3712_);
v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__1(v_val_3674_, v___x_3814_, v___x_3815_, v___x_3808_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
v___y_3780_ = v___x_3807_;
v___y_3781_ = v_a_3794_;
v___y_3782_ = v___x_3816_;
goto v___jp_3779_;
}
}
}
}
}
v___jp_3678_:
{
lean_object* v___x_3679_; lean_object* v_caches_3680_; lean_object* v_typeAnalysis_3681_; lean_object* v_target_3682_; uint8_t v_didChange_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3696_; 
v___x_3679_ = lean_st_ref_take(v_a_3658_);
v_caches_3680_ = lean_ctor_get(v___x_3679_, 0);
v_typeAnalysis_3681_ = lean_ctor_get(v___x_3679_, 1);
v_target_3682_ = lean_ctor_get(v___x_3679_, 2);
v_didChange_3683_ = lean_ctor_get_uint8(v___x_3679_, sizeof(void*)*4);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; 
v_unused_3697_ = lean_ctor_get(v___x_3679_, 3);
lean_dec(v_unused_3697_);
v___x_3685_ = v___x_3679_;
v_isShared_3686_ = v_isSharedCheck_3696_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_target_3682_);
lean_inc(v_typeAnalysis_3681_);
lean_inc(v_caches_3680_);
lean_dec(v___x_3679_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3696_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 3, v_val_3674_);
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_caches_3680_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_typeAnalysis_3681_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v_target_3682_);
lean_ctor_set(v_reuseFailAlloc_3695_, 3, v_val_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3695_, sizeof(void*)*4, v_didChange_3683_);
v___x_3688_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3689_ = lean_st_ref_put(v_a_3658_, v___x_3688_);
v___x_3690_ = 0;
v___x_3691_ = lean_box(v___x_3690_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3691_);
v___x_3693_ = v___x_3672_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
v___jp_3698_:
{
if (lean_obj_tag(v___y_3699_) == 0)
{
lean_dec_ref_known(v___y_3699_, 1);
goto v___jp_3678_;
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v_val_3674_);
lean_del_object(v___x_3672_);
v_a_3700_ = lean_ctor_get(v___y_3699_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___y_3699_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___y_3699_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___y_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
}
else
{
uint8_t v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
lean_dec(v_a_3670_);
v___x_3829_ = 1;
v___x_3830_ = lean_box(v___x_3829_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3830_);
v___x_3832_ = v___x_3672_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
v_a_3835_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3669_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3669_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps___boxed(lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec(v_a_3845_);
lean_dec(v_a_3844_);
lean_dec_ref(v_a_3843_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(lean_object* v_cls_3856_, lean_object* v_msg_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___redArg(v_cls_3856_, v_msg_3857_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0___boxed(lean_object* v_cls_3871_, lean_object* v_msg_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__0(v_cls_3871_, v_msg_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(lean_object* v_00_u03b1_3886_, lean_object* v_x_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___redArg(v_x_3887_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3901_, lean_object* v_x_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__6(v_00_u03b1_3901_, v_x_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5(lean_object* v_oldTraces_3916_, lean_object* v_data_3917_, lean_object* v_ref_3918_, lean_object* v_msg_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___redArg(v_oldTraces_3916_, v_data_3917_, v_ref_3918_, v_msg_3919_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5___boxed(lean_object* v_oldTraces_3933_, lean_object* v_data_3934_, lean_object* v_ref_3935_, lean_object* v_msg_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps_spec__4_spec__5(v_oldTraces_3933_, v_data_3934_, v_ref_3935_, v_msg_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
return v_res_3949_;
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
