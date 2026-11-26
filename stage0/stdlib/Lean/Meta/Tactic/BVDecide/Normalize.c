// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic public import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow public import Lean.Meta.Tactic.BVDecide.Normalize.Simproc public import Lean.Meta.Tactic.BVDecide.Normalize.Rewrite public import Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten public import Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint public import Lean.Meta.Tactic.BVDecide.Normalize.AC public import Lean.Meta.Tactic.BVDecide.Normalize.Structures public import Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec public import Lean.Meta.Tactic.BVDecide.Normalize.Enums public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis public import Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit public import Lean.Meta.Tactic.BVDecide.Normalize.Reduction public import Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps public import Lean.Meta.Tactic.BVDecide.EPR.Pass import Lean.Meta.Sym.Util import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.Intro import Lean.Meta.Sym.Grind import Lean.Meta.Tactic.Grind.BVDecide.Types
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass;
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Meta_Grind_BVDecide_bvExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpExpr___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__0 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__0_value;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__1 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__1_value;
static const lean_ctor_object l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__2_value_aux_0),((lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 109, 21, 40, 70, 113, 251, 6)}};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__2 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__2_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__3;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__4;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__5;
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "epr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 19, 168, 128, 92, 3, 227, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "normalized quantified fact: "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Tactic.BVDecide.Normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 124, .m_capacity = 124, .m_length = 123, .m_data = "_private.Lean.Meta.Tactic.BVDecide.Normalize.0.Lean.Meta.Tactic.BVDecide.Normalize.normalizeEprQuantifiers.normalizeEprFact"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: xs.size == 2 * n\n      "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Normalizing quantified facts"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0___boxed(lean_object**);
static const lean_array_object l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___boxed(lean_object**);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___boxed(lean_object**);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Running preprocessing pipeline"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Preprocessing goal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass;
v___x_6_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_passPipeline_9_; 
v___x_7_ = lean_box(0);
v___x_8_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
v_passPipeline_9_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_passPipeline_9_, 0, v___x_8_);
lean_ctor_set(v_passPipeline_9_, 1, v___x_7_);
return v_passPipeline_9_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_box(0);
v___x_11_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass;
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4(void){
_start:
{
lean_object* v___x_13_; lean_object* v_passPipeline_14_; lean_object* v___x_15_; 
v___x_13_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3);
v_passPipeline_14_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
v___x_15_ = l_List_appendTR___redArg(v_passPipeline_14_, v___x_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(lean_object* v_a_16_){
_start:
{
lean_object* v_config_18_; uint8_t v_acNf_19_; uint8_t v_andFlattening_20_; uint8_t v_embeddedConstraintSubst_21_; lean_object* v_passPipeline_23_; lean_object* v_passPipeline_29_; lean_object* v_passPipeline_32_; 
v_config_18_ = lean_ctor_get(v_a_16_, 0);
v_acNf_19_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*3 + 2);
v_andFlattening_20_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_21_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*3 + 4);
v_passPipeline_32_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
if (v_acNf_19_ == 0)
{
v_passPipeline_29_ = v_passPipeline_32_;
goto v___jp_28_;
}
else
{
lean_object* v___x_33_; 
v___x_33_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4);
v_passPipeline_29_ = v___x_33_;
goto v___jp_28_;
}
v___jp_22_:
{
if (v_embeddedConstraintSubst_21_ == 0)
{
lean_object* v___x_24_; 
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v_passPipeline_23_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0);
v___x_26_ = l_List_appendTR___redArg(v_passPipeline_23_, v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
v___jp_28_:
{
if (v_embeddedConstraintSubst_21_ == 0)
{
lean_inc(v_passPipeline_29_);
v_passPipeline_23_ = v_passPipeline_29_;
goto v___jp_22_;
}
else
{
if (v_andFlattening_20_ == 0)
{
lean_inc(v_passPipeline_29_);
v_passPipeline_23_ = v_passPipeline_29_;
goto v___jp_22_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1);
lean_inc(v_passPipeline_29_);
v___x_31_ = l_List_appendTR___redArg(v_passPipeline_29_, v___x_30_);
v_passPipeline_23_ = v___x_31_;
goto v___jp_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___boxed(lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_34_);
lean_dec_ref(v_a_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_37_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0(lean_object* v_x_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
lean_inc(v___y_68_);
lean_inc_ref(v___y_67_);
lean_inc(v___y_66_);
lean_inc_ref(v___y_65_);
lean_inc(v___y_64_);
v___x_74_ = lean_apply_10(v_x_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, lean_box(0));
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0___boxed(lean_object* v_x_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0(v_x_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(lean_object* v_mvarId_87_, lean_object* v_x_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___f_99_; lean_object* v___x_100_; 
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
lean_inc(v___y_89_);
v___f_99_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_99_, 0, v_x_88_);
lean_closure_set(v___f_99_, 1, v___y_89_);
lean_closure_set(v___f_99_, 2, v___y_90_);
lean_closure_set(v___f_99_, 3, v___y_91_);
lean_closure_set(v___f_99_, 4, v___y_92_);
lean_closure_set(v___f_99_, 5, v___y_93_);
v___x_100_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_87_, v___f_99_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
return v___x_100_;
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___boxed(lean_object* v_mvarId_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(v_mvarId_109_, v_x_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0(lean_object* v_00_u03b1_122_, lean_object* v_mvarId_123_, lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(v_mvarId_123_, v_x_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___boxed(lean_object* v_00_u03b1_136_, lean_object* v_mvarId_137_, lean_object* v_x_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0(v_00_u03b1_136_, v_mvarId_137_, v_x_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0(lean_object* v_caches_150_, lean_object* v_x_151_){
_start:
{
lean_inc_ref(v_caches_150_);
return v_caches_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0___boxed(lean_object* v_caches_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0(v_caches_152_, v_x_153_);
lean_dec_ref(v_x_153_);
lean_dec_ref(v_caches_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1(lean_object* v_goal_155_, lean_object* v___f_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_st_mk_ref(v_goal_155_);
v___x_168_ = l_Lean_Meta_Grind_BVDecide_bvExt;
v___x_169_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_168_, v___f_156_, v___x_167_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_179_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_179_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = lean_st_ref_get(v___x_167_);
lean_dec(v___x_167_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_a_170_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v___x_167_);
v_a_180_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_169_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_169_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1___boxed(lean_object* v_goal_188_, lean_object* v___f_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1(v_goal_188_, v___f_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2(lean_object* v_goal_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_st_mk_ref(v_goal_201_);
v___x_213_ = l_Lean_Meta_Grind_BVDecide_getCaches___redArg(v___x_212_, v___y_209_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_223_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_223_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_218_ = lean_st_ref_get(v___x_212_);
lean_dec(v___x_212_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_a_214_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_219_);
v___x_221_ = v___x_216_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec(v___x_212_);
v_a_224_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_213_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_213_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2___boxed(lean_object* v_goal_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2(v_goal_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(lean_object* v_x_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___x_329_; lean_object* v_target_330_; 
v___x_329_ = lean_st_ref_get(v_a_246_);
v_target_330_ = lean_ctor_get(v___x_329_, 2);
lean_inc_ref(v_target_330_);
lean_dec(v___x_329_);
if (lean_obj_tag(v_target_330_) == 2)
{
lean_object* v_goal_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_382_; 
v_goal_331_ = lean_ctor_get(v_target_330_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v_target_330_);
if (v_isSharedCheck_382_ == 0)
{
v___x_333_ = v_target_330_;
v_isShared_334_ = v_isSharedCheck_382_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_goal_331_);
lean_dec(v_target_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_382_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_mvarId_335_; lean_object* v___f_336_; lean_object* v___x_337_; 
v_mvarId_335_ = lean_ctor_get(v_goal_331_, 1);
lean_inc(v_mvarId_335_);
v___f_336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2___boxed), 11, 1);
lean_closure_set(v___f_336_, 0, v_goal_331_);
v___x_337_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(v_mvarId_335_, v___f_336_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v___x_342_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v_fst_339_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_fst_339_);
v_snd_340_ = lean_ctor_get(v_a_338_, 1);
lean_inc(v_snd_340_);
lean_dec(v_a_338_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v_snd_340_);
v___x_342_ = v___x_333_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_snd_340_);
v___x_342_ = v_reuseFailAlloc_373_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v_caches_344_; lean_object* v_typeAnalysis_345_; lean_object* v_hypotheses_346_; uint8_t v_didChange_347_; lean_object* v_eprBvProblem_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_371_; 
v___x_343_ = lean_st_ref_take(v_a_246_);
v_caches_344_ = lean_ctor_get(v___x_343_, 0);
v_typeAnalysis_345_ = lean_ctor_get(v___x_343_, 1);
v_hypotheses_346_ = lean_ctor_get(v___x_343_, 3);
v_didChange_347_ = lean_ctor_get_uint8(v___x_343_, sizeof(void*)*5);
v_eprBvProblem_348_ = lean_ctor_get(v___x_343_, 4);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_343_, 2);
lean_dec(v_unused_372_);
v___x_350_ = v___x_343_;
v_isShared_351_ = v_isSharedCheck_371_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_eprBvProblem_348_);
lean_inc(v_hypotheses_346_);
lean_inc(v_typeAnalysis_345_);
lean_inc(v_caches_344_);
lean_dec(v___x_343_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_371_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 2, v___x_342_);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_caches_344_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_typeAnalysis_345_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_hypotheses_346_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_eprBvProblem_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*5, v_didChange_347_);
v___x_353_ = v_reuseFailAlloc_370_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_typeAnalysis_356_; lean_object* v_target_357_; lean_object* v_hypotheses_358_; uint8_t v_didChange_359_; lean_object* v_eprBvProblem_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_368_; 
v___x_354_ = lean_st_ref_put(v_a_246_, v___x_353_);
v___x_355_ = lean_st_ref_take(v_a_246_);
v_typeAnalysis_356_ = lean_ctor_get(v___x_355_, 1);
v_target_357_ = lean_ctor_get(v___x_355_, 2);
v_hypotheses_358_ = lean_ctor_get(v___x_355_, 3);
v_didChange_359_ = lean_ctor_get_uint8(v___x_355_, sizeof(void*)*5);
v_eprBvProblem_360_ = lean_ctor_get(v___x_355_, 4);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_355_, 0);
lean_dec(v_unused_369_);
v___x_362_ = v___x_355_;
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_eprBvProblem_360_);
lean_inc(v_hypotheses_358_);
lean_inc(v_target_357_);
lean_inc(v_typeAnalysis_356_);
lean_dec(v___x_355_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_368_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v_fst_339_);
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_typeAnalysis_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_target_357_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_hypotheses_358_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_eprBvProblem_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_367_, sizeof(void*)*5, v_didChange_359_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_st_ref_put(v_a_246_, v___x_365_);
v___y_258_ = v_a_245_;
v___y_259_ = v_a_246_;
v___y_260_ = v_a_247_;
v___y_261_ = v_a_248_;
v___y_262_ = v_a_249_;
v___y_263_ = v_a_250_;
v___y_264_ = v_a_251_;
v___y_265_ = v_a_252_;
v___y_266_ = v_a_253_;
v___y_267_ = v_a_254_;
v___y_268_ = v_a_255_;
goto v___jp_257_;
}
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_del_object(v___x_333_);
lean_dec_ref(v_x_244_);
v_a_374_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_337_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_337_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
else
{
lean_dec_ref(v_target_330_);
v___y_258_ = v_a_245_;
v___y_259_ = v_a_246_;
v___y_260_ = v_a_247_;
v___y_261_ = v_a_248_;
v___y_262_ = v_a_249_;
v___y_263_ = v_a_250_;
v___y_264_ = v_a_251_;
v___y_265_ = v_a_252_;
v___y_266_ = v_a_253_;
v___y_267_ = v_a_254_;
v___y_268_ = v_a_255_;
goto v___jp_257_;
}
v___jp_257_:
{
lean_object* v___x_269_; 
lean_inc(v___y_268_);
lean_inc_ref(v___y_267_);
lean_inc(v___y_266_);
lean_inc_ref(v___y_265_);
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
lean_inc(v___y_260_);
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
v___x_269_ = lean_apply_12(v_x_244_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, lean_box(0));
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v_mode_271_; uint8_t v___x_272_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
v_mode_271_ = lean_ctor_get(v___y_258_, 1);
v___x_272_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_271_);
if (v___x_272_ == 0)
{
lean_dec(v_a_270_);
return v___x_269_;
}
else
{
lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_327_; 
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_269_, 0);
lean_dec(v_unused_328_);
v___x_274_ = v___x_269_;
v_isShared_275_ = v_isSharedCheck_327_;
goto v_resetjp_273_;
}
else
{
lean_dec(v___x_269_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_327_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v_caches_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v_target_280_; 
v___x_276_ = lean_st_ref_get(v___y_259_);
v_caches_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc_ref(v_caches_277_);
lean_dec(v___x_276_);
v___f_278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_278_, 0, v_caches_277_);
v___x_279_ = lean_st_ref_get(v___y_259_);
v_target_280_ = lean_ctor_get(v___x_279_, 2);
lean_inc_ref(v_target_280_);
lean_dec(v___x_279_);
if (lean_obj_tag(v_target_280_) == 2)
{
lean_object* v_goal_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_323_; 
lean_del_object(v___x_274_);
v_goal_281_ = lean_ctor_get(v_target_280_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_target_280_);
if (v_isSharedCheck_323_ == 0)
{
v___x_283_ = v_target_280_;
v_isShared_284_ = v_isSharedCheck_323_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_goal_281_);
lean_dec(v_target_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_323_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_mvarId_285_; lean_object* v___f_286_; lean_object* v___x_287_; 
v_mvarId_285_ = lean_ctor_get(v_goal_281_, 1);
lean_inc(v_mvarId_285_);
v___f_286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1___boxed), 12, 2);
lean_closure_set(v___f_286_, 0, v_goal_281_);
lean_closure_set(v___f_286_, 1, v___f_278_);
v___x_287_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(v_mvarId_285_, v___f_286_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_314_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_314_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_314_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_314_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_snd_292_; lean_object* v___x_294_; 
v_snd_292_ = lean_ctor_get(v_a_288_, 1);
lean_inc(v_snd_292_);
lean_dec(v_a_288_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_snd_292_);
v___x_294_ = v___x_283_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_snd_292_);
v___x_294_ = v_reuseFailAlloc_313_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v_caches_296_; lean_object* v_typeAnalysis_297_; lean_object* v_hypotheses_298_; uint8_t v_didChange_299_; lean_object* v_eprBvProblem_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_311_; 
v___x_295_ = lean_st_ref_take(v___y_259_);
v_caches_296_ = lean_ctor_get(v___x_295_, 0);
v_typeAnalysis_297_ = lean_ctor_get(v___x_295_, 1);
v_hypotheses_298_ = lean_ctor_get(v___x_295_, 3);
v_didChange_299_ = lean_ctor_get_uint8(v___x_295_, sizeof(void*)*5);
v_eprBvProblem_300_ = lean_ctor_get(v___x_295_, 4);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v___x_295_, 2);
lean_dec(v_unused_312_);
v___x_302_ = v___x_295_;
v_isShared_303_ = v_isSharedCheck_311_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_eprBvProblem_300_);
lean_inc(v_hypotheses_298_);
lean_inc(v_typeAnalysis_297_);
lean_inc(v_caches_296_);
lean_dec(v___x_295_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_311_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 2, v___x_294_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_caches_296_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_typeAnalysis_297_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v_hypotheses_298_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v_eprBvProblem_300_);
lean_ctor_set_uint8(v_reuseFailAlloc_310_, sizeof(void*)*5, v_didChange_299_);
v___x_305_ = v_reuseFailAlloc_310_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_st_ref_put(v___y_259_, v___x_305_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_a_270_);
v___x_308_ = v___x_290_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_270_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_del_object(v___x_283_);
lean_dec(v_a_270_);
v_a_315_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_287_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_287_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
else
{
lean_object* v___x_325_; 
lean_dec_ref(v_target_280_);
lean_dec_ref(v___f_278_);
if (v_isShared_275_ == 0)
{
v___x_325_ = v___x_274_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_270_);
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
else
{
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___boxed(lean_object* v_x_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(v_x_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches(lean_object* v_00_u03b1_397_, lean_object* v_x_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(v_x_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___boxed(lean_object* v_00_u03b1_412_, lean_object* v_x_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches(v_00_u03b1_412_, v_x_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_426_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_instMonadEIO___redArg();
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0(lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_toApplicative_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_515_; 
v___x_445_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0);
v___x_446_ = l_StateRefT_x27_instMonad___redArg(v___x_445_);
v_toApplicative_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v___x_446_, 1);
lean_dec(v_unused_516_);
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_515_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_toApplicative_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_515_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_toFunctor_451_; lean_object* v_toSeq_452_; lean_object* v_toSeqLeft_453_; lean_object* v_toSeqRight_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_513_; 
v_toFunctor_451_ = lean_ctor_get(v_toApplicative_447_, 0);
v_toSeq_452_ = lean_ctor_get(v_toApplicative_447_, 2);
v_toSeqLeft_453_ = lean_ctor_get(v_toApplicative_447_, 3);
v_toSeqRight_454_ = lean_ctor_get(v_toApplicative_447_, 4);
v_isSharedCheck_513_ = !lean_is_exclusive(v_toApplicative_447_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v_toApplicative_447_, 1);
lean_dec(v_unused_514_);
v___x_456_ = v_toApplicative_447_;
v_isShared_457_ = v_isSharedCheck_513_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_toSeqRight_454_);
lean_inc(v_toSeqLeft_453_);
lean_inc(v_toSeq_452_);
lean_inc(v_toFunctor_451_);
lean_dec(v_toApplicative_447_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_513_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___f_458_; lean_object* v___f_459_; lean_object* v___f_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___f_463_; lean_object* v___f_464_; lean_object* v___f_465_; lean_object* v___x_467_; 
v___f_458_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__1));
v___f_459_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__2));
lean_inc_ref(v_toFunctor_451_);
v___f_460_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_460_, 0, v_toFunctor_451_);
v___f_461_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_461_, 0, v_toFunctor_451_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___f_460_);
lean_ctor_set(v___x_462_, 1, v___f_461_);
v___f_463_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_463_, 0, v_toSeqRight_454_);
v___f_464_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_464_, 0, v_toSeqLeft_453_);
v___f_465_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_465_, 0, v_toSeq_452_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 4, v___f_463_);
lean_ctor_set(v___x_456_, 3, v___f_464_);
lean_ctor_set(v___x_456_, 2, v___f_465_);
lean_ctor_set(v___x_456_, 1, v___f_458_);
lean_ctor_set(v___x_456_, 0, v___x_462_);
v___x_467_ = v___x_456_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___f_458_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v___f_465_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v___f_464_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v___f_463_);
v___x_467_ = v_reuseFailAlloc_512_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___f_459_);
lean_ctor_set(v___x_449_, 0, v___x_467_);
v___x_469_ = v___x_449_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___f_459_);
v___x_469_ = v_reuseFailAlloc_511_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v_toApplicative_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_509_; 
v___x_470_ = l_StateRefT_x27_instMonad___redArg(v___x_469_);
v_toApplicative_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_470_, 1);
lean_dec(v_unused_510_);
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_509_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_toApplicative_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_509_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_toFunctor_475_; lean_object* v_toSeq_476_; lean_object* v_toSeqLeft_477_; lean_object* v_toSeqRight_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_507_; 
v_toFunctor_475_ = lean_ctor_get(v_toApplicative_471_, 0);
v_toSeq_476_ = lean_ctor_get(v_toApplicative_471_, 2);
v_toSeqLeft_477_ = lean_ctor_get(v_toApplicative_471_, 3);
v_toSeqRight_478_ = lean_ctor_get(v_toApplicative_471_, 4);
v_isSharedCheck_507_ = !lean_is_exclusive(v_toApplicative_471_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v_toApplicative_471_, 1);
lean_dec(v_unused_508_);
v___x_480_ = v_toApplicative_471_;
v_isShared_481_ = v_isSharedCheck_507_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_toSeqRight_478_);
lean_inc(v_toSeqLeft_477_);
lean_inc(v_toSeq_476_);
lean_inc(v_toFunctor_475_);
lean_dec(v_toApplicative_471_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_507_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___f_484_; lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___f_487_; lean_object* v___f_488_; lean_object* v___f_489_; lean_object* v___x_491_; 
v___f_482_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__3));
v___f_483_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__4));
lean_inc_ref(v_toFunctor_475_);
v___f_484_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_484_, 0, v_toFunctor_475_);
v___f_485_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_485_, 0, v_toFunctor_475_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___f_484_);
lean_ctor_set(v___x_486_, 1, v___f_485_);
v___f_487_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_487_, 0, v_toSeqRight_478_);
v___f_488_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_488_, 0, v_toSeqLeft_477_);
v___f_489_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_489_, 0, v_toSeq_476_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 4, v___f_487_);
lean_ctor_set(v___x_480_, 3, v___f_488_);
lean_ctor_set(v___x_480_, 2, v___f_489_);
lean_ctor_set(v___x_480_, 1, v___f_482_);
lean_ctor_set(v___x_480_, 0, v___x_486_);
v___x_491_ = v___x_480_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___f_482_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v___f_489_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v___f_488_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v___f_487_);
v___x_491_ = v_reuseFailAlloc_506_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___f_483_);
lean_ctor_set(v___x_473_, 0, v___x_491_);
v___x_493_ = v___x_473_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___f_483_);
v___x_493_ = v_reuseFailAlloc_505_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___f_502_; lean_object* v___x_29698__overap_503_; lean_object* v___x_504_; 
v___x_494_ = l_StateRefT_x27_instMonad___redArg(v___x_493_);
v___x_495_ = l_ReaderT_instMonad___redArg(v___x_494_);
v___x_496_ = l_StateRefT_x27_instMonad___redArg(v___x_495_);
v___x_497_ = l_ReaderT_instMonad___redArg(v___x_496_);
v___x_498_ = l_ReaderT_instMonad___redArg(v___x_497_);
v___x_499_ = l_StateRefT_x27_instMonad___redArg(v___x_498_);
v___x_500_ = lean_box(0);
v___x_501_ = l_instInhabitedOfMonad___redArg(v___x_499_, v___x_500_);
v___f_502_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_502_, 0, v___x_501_);
v___x_29698__overap_503_ = lean_panic_fn_borrowed(v___f_502_, v_msg_432_);
lean_dec_ref(v___f_502_);
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
lean_inc(v___y_441_);
lean_inc_ref(v___y_440_);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
lean_inc(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
v___x_504_ = lean_apply_12(v___x_29698__overap_503_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, lean_box(0));
return v___x_504_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___boxed(lean_object* v_msg_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0(v_msg_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg___lam__0(lean_object* v_k_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v_b_539_, lean_object* v_c_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; 
lean_inc(v___y_544_);
lean_inc_ref(v___y_543_);
lean_inc(v___y_542_);
lean_inc_ref(v___y_541_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
v___x_546_ = lean_apply_14(v_k_531_, v_b_539_, v_c_540_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, lean_box(0));
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg___lam__0___boxed(lean_object* v_k_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v_b_555_, lean_object* v_c_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg___lam__0(v_k_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v_b_555_, v_c_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg(lean_object* v_type_563_, lean_object* v_maxFVars_x3f_564_, lean_object* v_k_565_, uint8_t v_cleanupAnnotations_566_, uint8_t v_whnfType_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___f_580_; lean_object* v___x_581_; 
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
v___f_580_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_580_, 0, v_k_565_);
lean_closure_set(v___f_580_, 1, v___y_568_);
lean_closure_set(v___f_580_, 2, v___y_569_);
lean_closure_set(v___f_580_, 3, v___y_570_);
lean_closure_set(v___f_580_, 4, v___y_571_);
lean_closure_set(v___f_580_, 5, v___y_572_);
lean_closure_set(v___f_580_, 6, v___y_573_);
lean_closure_set(v___f_580_, 7, v___y_574_);
v___x_581_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_563_, v_maxFVars_x3f_564_, v___f_580_, v_cleanupAnnotations_566_, v_whnfType_567_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_581_) == 0)
{
return v___x_581_;
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg___boxed(lean_object** _args){
lean_object* v_type_590_ = _args[0];
lean_object* v_maxFVars_x3f_591_ = _args[1];
lean_object* v_k_592_ = _args[2];
lean_object* v_cleanupAnnotations_593_ = _args[3];
lean_object* v_whnfType_594_ = _args[4];
lean_object* v___y_595_ = _args[5];
lean_object* v___y_596_ = _args[6];
lean_object* v___y_597_ = _args[7];
lean_object* v___y_598_ = _args[8];
lean_object* v___y_599_ = _args[9];
lean_object* v___y_600_ = _args[10];
lean_object* v___y_601_ = _args[11];
lean_object* v___y_602_ = _args[12];
lean_object* v___y_603_ = _args[13];
lean_object* v___y_604_ = _args[14];
lean_object* v___y_605_ = _args[15];
lean_object* v___y_606_ = _args[16];
_start:
{
uint8_t v_cleanupAnnotations_boxed_607_; uint8_t v_whnfType_boxed_608_; lean_object* v_res_609_; 
v_cleanupAnnotations_boxed_607_ = lean_unbox(v_cleanupAnnotations_593_);
v_whnfType_boxed_608_ = lean_unbox(v_whnfType_594_);
v_res_609_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg(v_type_590_, v_maxFVars_x3f_591_, v_k_592_, v_cleanupAnnotations_boxed_607_, v_whnfType_boxed_608_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7(lean_object* v_00_u03b1_610_, lean_object* v_type_611_, lean_object* v_maxFVars_x3f_612_, lean_object* v_k_613_, uint8_t v_cleanupAnnotations_614_, uint8_t v_whnfType_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg(v_type_611_, v_maxFVars_x3f_612_, v_k_613_, v_cleanupAnnotations_614_, v_whnfType_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___boxed(lean_object** _args){
lean_object* v_00_u03b1_629_ = _args[0];
lean_object* v_type_630_ = _args[1];
lean_object* v_maxFVars_x3f_631_ = _args[2];
lean_object* v_k_632_ = _args[3];
lean_object* v_cleanupAnnotations_633_ = _args[4];
lean_object* v_whnfType_634_ = _args[5];
lean_object* v___y_635_ = _args[6];
lean_object* v___y_636_ = _args[7];
lean_object* v___y_637_ = _args[8];
lean_object* v___y_638_ = _args[9];
lean_object* v___y_639_ = _args[10];
lean_object* v___y_640_ = _args[11];
lean_object* v___y_641_ = _args[12];
lean_object* v___y_642_ = _args[13];
lean_object* v___y_643_ = _args[14];
lean_object* v___y_644_ = _args[15];
lean_object* v___y_645_ = _args[16];
lean_object* v___y_646_ = _args[17];
_start:
{
uint8_t v_cleanupAnnotations_boxed_647_; uint8_t v_whnfType_boxed_648_; lean_object* v_res_649_; 
v_cleanupAnnotations_boxed_647_ = lean_unbox(v_cleanupAnnotations_633_);
v_whnfType_boxed_648_ = lean_unbox(v_whnfType_634_);
v_res_649_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7(v_00_u03b1_629_, v_type_630_, v_maxFVars_x3f_631_, v_k_632_, v_cleanupAnnotations_boxed_647_, v_whnfType_boxed_648_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3_spec__3(lean_object* v_msgData_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v_env_657_; uint8_t v___x_658_; lean_object* v_env_659_; lean_object* v___x_660_; lean_object* v_toCold_661_; lean_object* v_mctx_662_; lean_object* v_lctx_663_; lean_object* v_options_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_656_ = lean_st_ref_get(v___y_654_);
v_env_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc_ref(v_env_657_);
lean_dec(v___x_656_);
v___x_658_ = 0;
v_env_659_ = l_Lean_Environment_setRecordingDeps(v_env_657_, v___x_658_);
v___x_660_ = lean_st_ref_get(v___y_652_);
v_toCold_661_ = lean_ctor_get(v___y_653_, 0);
v_mctx_662_ = lean_ctor_get(v___x_660_, 0);
lean_inc_ref(v_mctx_662_);
lean_dec(v___x_660_);
v_lctx_663_ = lean_ctor_get(v___y_651_, 2);
v_options_664_ = lean_ctor_get(v_toCold_661_, 2);
lean_inc_ref(v_options_664_);
lean_inc_ref(v_lctx_663_);
v___x_665_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_665_, 0, v_env_659_);
lean_ctor_set(v___x_665_, 1, v_mctx_662_);
lean_ctor_set(v___x_665_, 2, v_lctx_663_);
lean_ctor_set(v___x_665_, 3, v_options_664_);
v___x_666_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_msgData_650_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3_spec__3___boxed(lean_object* v_msgData_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3_spec__3(v_msgData_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_674_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_675_; double v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_float_of_nat(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg(lean_object* v_cls_680_, lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_ref_687_; lean_object* v___x_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_734_; 
v_ref_687_ = lean_ctor_get(v___y_684_, 2);
v___x_688_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3_spec__3(v_msg_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_734_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_734_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_734_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v_traceState_694_; lean_object* v_env_695_; lean_object* v_nextMacroScope_696_; lean_object* v_ngen_697_; lean_object* v_auxDeclNGen_698_; lean_object* v_cache_699_; lean_object* v_recordedDeps_700_; lean_object* v_messages_701_; lean_object* v_infoState_702_; lean_object* v_snapshotTasks_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_733_; 
v___x_693_ = lean_st_ref_take(v___y_685_);
v_traceState_694_ = lean_ctor_get(v___x_693_, 4);
v_env_695_ = lean_ctor_get(v___x_693_, 0);
v_nextMacroScope_696_ = lean_ctor_get(v___x_693_, 1);
v_ngen_697_ = lean_ctor_get(v___x_693_, 2);
v_auxDeclNGen_698_ = lean_ctor_get(v___x_693_, 3);
v_cache_699_ = lean_ctor_get(v___x_693_, 5);
v_recordedDeps_700_ = lean_ctor_get(v___x_693_, 6);
v_messages_701_ = lean_ctor_get(v___x_693_, 7);
v_infoState_702_ = lean_ctor_get(v___x_693_, 8);
v_snapshotTasks_703_ = lean_ctor_get(v___x_693_, 9);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_733_ == 0)
{
v___x_705_ = v___x_693_;
v_isShared_706_ = v_isSharedCheck_733_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_snapshotTasks_703_);
lean_inc(v_infoState_702_);
lean_inc(v_messages_701_);
lean_inc(v_recordedDeps_700_);
lean_inc(v_cache_699_);
lean_inc(v_traceState_694_);
lean_inc(v_auxDeclNGen_698_);
lean_inc(v_ngen_697_);
lean_inc(v_nextMacroScope_696_);
lean_inc(v_env_695_);
lean_dec(v___x_693_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_733_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint64_t v_tid_707_; lean_object* v_traces_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_732_; 
v_tid_707_ = lean_ctor_get_uint64(v_traceState_694_, sizeof(void*)*1);
v_traces_708_ = lean_ctor_get(v_traceState_694_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_traceState_694_);
if (v_isSharedCheck_732_ == 0)
{
v___x_710_ = v_traceState_694_;
v_isShared_711_ = v_isSharedCheck_732_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_traces_708_);
lean_dec(v_traceState_694_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_732_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; double v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_712_ = lean_box(0);
v___x_713_ = lean_box(0);
v___x_714_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0);
v___x_715_ = 0;
v___x_716_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_717_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_717_, 0, v_cls_680_);
lean_ctor_set(v___x_717_, 1, v___x_713_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
lean_ctor_set_float(v___x_717_, sizeof(void*)*3, v___x_714_);
lean_ctor_set_float(v___x_717_, sizeof(void*)*3 + 8, v___x_714_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*3 + 16, v___x_715_);
v___x_718_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__2));
v___x_719_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v_a_689_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
lean_inc(v_ref_687_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_ref_687_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_PersistentArray_push___redArg(v_traces_708_, v___x_720_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_721_);
v___x_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_721_);
lean_ctor_set_uint64(v_reuseFailAlloc_731_, sizeof(void*)*1, v_tid_707_);
v___x_723_ = v_reuseFailAlloc_731_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v___x_723_);
v___x_725_ = v___x_705_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_env_695_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_nextMacroScope_696_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_ngen_697_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_auxDeclNGen_698_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_730_, 5, v_cache_699_);
lean_ctor_set(v_reuseFailAlloc_730_, 6, v_recordedDeps_700_);
lean_ctor_set(v_reuseFailAlloc_730_, 7, v_messages_701_);
lean_ctor_set(v_reuseFailAlloc_730_, 8, v_infoState_702_);
lean_ctor_set(v_reuseFailAlloc_730_, 9, v_snapshotTasks_703_);
v___x_725_ = v_reuseFailAlloc_730_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_st_ref_put(v___y_685_, v___x_725_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_712_);
v___x_728_ = v___x_691_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_712_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___boxed(lean_object* v_cls_735_, lean_object* v_msg_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg(v_cls_735_, v_msg_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__3(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l_Lean_Level_ofNat(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__4(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_box(0);
v___x_751_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__3);
v___x_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__5(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__4, &l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__4_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__4);
v___x_754_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__2));
v___x_755_ = l_Lean_mkConst(v___x_754_, v___x_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4(lean_object* v_as_756_, lean_object* v_bs_757_, lean_object* v_i_758_, lean_object* v_cs_759_){
_start:
{
lean_object* v___y_761_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_array_get_size(v_as_756_);
v___x_767_ = lean_nat_dec_lt(v_i_758_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v_i_758_);
return v_cs_759_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_array_get_size(v_bs_757_);
v___x_769_ = lean_nat_dec_lt(v_i_758_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec(v_i_758_);
return v_cs_759_;
}
else
{
lean_object* v_b_770_; lean_object* v_type_771_; lean_object* v_type_x27_772_; lean_object* v_proof_x3f_773_; lean_object* v_a_774_; 
v_b_770_ = lean_array_fget_borrowed(v_bs_757_, v_i_758_);
v_type_771_ = lean_ctor_get(v_b_770_, 0);
v_type_x27_772_ = lean_ctor_get(v_b_770_, 1);
v_proof_x3f_773_ = lean_ctor_get(v_b_770_, 2);
v_a_774_ = lean_array_fget_borrowed(v_as_756_, v_i_758_);
if (lean_obj_tag(v_proof_x3f_773_) == 0)
{
lean_inc(v_a_774_);
v___y_761_ = v_a_774_;
goto v___jp_760_;
}
else
{
lean_object* v_val_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_val_775_ = lean_ctor_get(v_proof_x3f_773_, 0);
v___x_776_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___closed__5);
lean_inc(v_a_774_);
lean_inc(v_val_775_);
lean_inc_ref(v_type_x27_772_);
lean_inc_ref(v_type_771_);
v___x_777_ = l_Lean_mkApp4(v___x_776_, v_type_771_, v_type_x27_772_, v_val_775_, v_a_774_);
v___y_761_ = v___x_777_;
goto v___jp_760_;
}
}
}
v___jp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_i_758_, v___x_762_);
lean_dec(v_i_758_);
v___x_764_ = lean_array_push(v_cs_759_, v___y_761_);
v_i_758_ = v___x_763_;
v_cs_759_ = v___x_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4___boxed(lean_object* v_as_778_, lean_object* v_bs_779_, lean_object* v_i_780_, lean_object* v_cs_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4(v_as_778_, v_bs_779_, v_i_780_, v_cs_781_);
lean_dec_ref(v_bs_779_);
lean_dec_ref(v_as_778_);
return v_res_782_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4));
v___x_796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__6));
v___x_797_ = l_Lean_Name_append(v___x_796_, v___x_795_);
return v___x_797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__9(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__8));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0(lean_object* v_args_805_, lean_object* v_type_x27_806_, lean_object* v_name_807_, lean_object* v_source_808_, lean_object* v_boundSorts_809_, uint8_t v___x_810_, uint8_t v___x_811_, lean_object* v_a_812_, lean_object* v___x_813_, lean_object* v___x_814_, lean_object* v_value_815_, lean_object* v_proof_x3f_816_, lean_object* v_type_817_, lean_object* v_newGuards_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_inc_ref(v_args_805_);
v___x_831_ = l_Array_append___redArg(v_args_805_, v_newGuards_818_);
lean_inc_ref(v_type_x27_806_);
lean_inc_ref(v___x_831_);
v___x_832_ = l_Lean_Meta_Sym_mkForallFVarsS(v___x_831_, v_type_x27_806_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_888_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_888_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_888_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_888_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___y_838_; lean_object* v___y_846_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_inc(v___x_813_);
v___x_878_ = l_Array_zipWithMAux___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__4(v_newGuards_818_, v_a_812_, v___x_813_, v___x_814_);
v___x_879_ = l_Array_append___redArg(v_args_805_, v___x_878_);
lean_dec_ref(v___x_878_);
v___x_880_ = l_Lean_mkAppN(v_value_815_, v___x_879_);
lean_dec_ref(v___x_879_);
if (lean_obj_tag(v_proof_x3f_816_) == 0)
{
lean_dec_ref(v_type_817_);
lean_dec(v___x_813_);
lean_dec_ref(v_type_x27_806_);
v___y_846_ = v___x_880_;
goto v___jp_845_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_val_881_ = lean_ctor_get(v_proof_x3f_816_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_proof_x3f_816_, 1);
v___x_882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__11));
v___x_883_ = l_Lean_Level_ofNat(v___x_813_);
lean_dec(v___x_813_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_mkConst(v___x_882_, v___x_885_);
v___x_887_ = l_Lean_mkApp4(v___x_886_, v_type_817_, v_type_x27_806_, v_val_881_, v___x_880_);
v___y_846_ = v___x_887_;
goto v___jp_845_;
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_839_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_839_, 0, v_name_807_);
lean_ctor_set(v___x_839_, 1, v_a_833_);
lean_ctor_set(v___x_839_, 2, v___y_838_);
lean_ctor_set(v___x_839_, 3, v_source_808_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v_boundSorts_809_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_841_);
v___x_843_ = v___x_835_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
v___jp_845_:
{
uint8_t v___x_847_; lean_object* v___x_848_; 
v___x_847_ = 1;
v___x_848_ = l_Lean_Meta_mkLambdaFVars(v___x_831_, v___y_846_, v___x_810_, v___x_811_, v___x_810_, v___x_811_, v___x_847_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec_ref(v___x_831_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_toCold_849_; lean_object* v_options_850_; uint8_t v_hasTrace_851_; 
v_toCold_849_ = lean_ctor_get(v___y_828_, 0);
v_options_850_ = lean_ctor_get(v_toCold_849_, 2);
v_hasTrace_851_ = lean_ctor_get_uint8(v_options_850_, sizeof(void*)*1);
if (v_hasTrace_851_ == 0)
{
lean_object* v_a_852_; 
v_a_852_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_848_, 1);
v___y_838_ = v_a_852_;
goto v___jp_837_;
}
else
{
lean_object* v_a_853_; lean_object* v_inheritedTraceOptions_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_a_853_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_848_, 1);
v_inheritedTraceOptions_854_ = lean_ctor_get(v_toCold_849_, 11);
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4));
v___x_856_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7);
v___x_857_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_854_, v_options_850_, v___x_856_);
if (v___x_857_ == 0)
{
v___y_838_ = v_a_853_;
goto v___jp_837_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__9);
lean_inc(v_a_833_);
v___x_859_ = l_Lean_MessageData_ofExpr(v_a_833_);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg(v___x_855_, v___x_860_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_dec_ref_known(v___x_861_, 1);
v___y_838_ = v_a_853_;
goto v___jp_837_;
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_853_);
lean_del_object(v___x_835_);
lean_dec(v_a_833_);
lean_dec_ref(v_boundSorts_809_);
lean_dec(v_source_808_);
lean_dec(v_name_807_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
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
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_del_object(v___x_835_);
lean_dec(v_a_833_);
lean_dec_ref(v_boundSorts_809_);
lean_dec(v_source_808_);
lean_dec(v_name_807_);
v_a_870_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_848_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_848_);
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
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref(v___x_831_);
lean_dec_ref(v_type_817_);
lean_dec(v_proof_x3f_816_);
lean_dec_ref(v_value_815_);
lean_dec_ref(v___x_814_);
lean_dec(v___x_813_);
lean_dec_ref(v_boundSorts_809_);
lean_dec(v_source_808_);
lean_dec(v_name_807_);
lean_dec_ref(v_type_x27_806_);
lean_dec_ref(v_args_805_);
v_a_889_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_832_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_832_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___boxed(lean_object** _args){
lean_object* v_args_897_ = _args[0];
lean_object* v_type_x27_898_ = _args[1];
lean_object* v_name_899_ = _args[2];
lean_object* v_source_900_ = _args[3];
lean_object* v_boundSorts_901_ = _args[4];
lean_object* v___x_902_ = _args[5];
lean_object* v___x_903_ = _args[6];
lean_object* v_a_904_ = _args[7];
lean_object* v___x_905_ = _args[8];
lean_object* v___x_906_ = _args[9];
lean_object* v_value_907_ = _args[10];
lean_object* v_proof_x3f_908_ = _args[11];
lean_object* v_type_909_ = _args[12];
lean_object* v_newGuards_910_ = _args[13];
lean_object* v___y_911_ = _args[14];
lean_object* v___y_912_ = _args[15];
lean_object* v___y_913_ = _args[16];
lean_object* v___y_914_ = _args[17];
lean_object* v___y_915_ = _args[18];
lean_object* v___y_916_ = _args[19];
lean_object* v___y_917_ = _args[20];
lean_object* v___y_918_ = _args[21];
lean_object* v___y_919_ = _args[22];
lean_object* v___y_920_ = _args[23];
lean_object* v___y_921_ = _args[24];
lean_object* v___y_922_ = _args[25];
_start:
{
uint8_t v___x_43884__boxed_923_; uint8_t v___x_43885__boxed_924_; lean_object* v_res_925_; 
v___x_43884__boxed_923_ = lean_unbox(v___x_902_);
v___x_43885__boxed_924_ = lean_unbox(v___x_903_);
v_res_925_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0(v_args_897_, v_type_x27_898_, v_name_899_, v_source_900_, v_boundSorts_901_, v___x_43884__boxed_923_, v___x_43885__boxed_924_, v_a_904_, v___x_905_, v___x_906_, v_value_907_, v_proof_x3f_908_, v_type_909_, v_newGuards_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec_ref(v_newGuards_910_);
lean_dec_ref(v_a_904_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__1___redArg(lean_object* v_a_926_, lean_object* v_b_927_){
_start:
{
lean_object* v_array_928_; lean_object* v_start_929_; lean_object* v_stop_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_943_; 
v_array_928_ = lean_ctor_get(v_a_926_, 0);
v_start_929_ = lean_ctor_get(v_a_926_, 1);
v_stop_930_ = lean_ctor_get(v_a_926_, 2);
v_isSharedCheck_943_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_943_ == 0)
{
v___x_932_ = v_a_926_;
v_isShared_933_ = v_isSharedCheck_943_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_stop_930_);
lean_inc(v_start_929_);
lean_inc(v_array_928_);
lean_dec(v_a_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_943_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
uint8_t v___x_934_; 
v___x_934_ = lean_nat_dec_lt(v_start_929_, v_stop_930_);
if (v___x_934_ == 0)
{
lean_del_object(v___x_932_);
lean_dec(v_stop_930_);
lean_dec(v_start_929_);
lean_dec_ref(v_array_928_);
return v_b_927_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_nat_add(v_start_929_, v___x_935_);
lean_inc_ref(v_array_928_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_936_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_array_928_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_stop_930_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_array_fget(v_array_928_, v_start_929_);
lean_dec(v_start_929_);
lean_dec_ref(v_array_928_);
v___x_940_ = lean_array_push(v_b_927_, v___x_939_);
v_a_926_ = v___x_938_;
v_b_927_ = v___x_940_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7___lam__0(lean_object* v_snd_944_, lean_object* v_x_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_snd_944_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7___lam__0___boxed(lean_object* v_snd_959_, lean_object* v_x_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7___lam__0(v_snd_959_, v_x_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec_ref(v_x_960_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7(size_t v_sz_974_, size_t v_i_975_, lean_object* v_bs_976_){
_start:
{
uint8_t v___x_977_; 
v___x_977_ = lean_usize_dec_lt(v_i_975_, v_sz_974_);
if (v___x_977_ == 0)
{
return v_bs_976_;
}
else
{
lean_object* v_v_978_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_994_; 
v_v_978_ = lean_array_uget(v_bs_976_, v_i_975_);
v_fst_979_ = lean_ctor_get(v_v_978_, 0);
v_snd_980_ = lean_ctor_get(v_v_978_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_v_978_);
if (v_isSharedCheck_994_ == 0)
{
v___x_982_ = v_v_978_;
v_isShared_983_ = v_isSharedCheck_994_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_snd_980_);
lean_inc(v_fst_979_);
lean_dec(v_v_978_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_994_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v_bs_x27_985_; lean_object* v___f_986_; lean_object* v___x_988_; 
v___x_984_ = lean_unsigned_to_nat(0u);
v_bs_x27_985_ = lean_array_uset(v_bs_976_, v_i_975_, v___x_984_);
v___f_986_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7___lam__0___boxed), 14, 1);
lean_closure_set(v___f_986_, 0, v_snd_980_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___f_986_);
v___x_988_ = v___x_982_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_fst_979_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___f_986_);
v___x_988_ = v_reuseFailAlloc_993_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_add(v_i_975_, v___x_989_);
v___x_991_ = lean_array_uset(v_bs_x27_985_, v_i_975_, v___x_988_);
v_i_975_ = v___x_990_;
v_bs_976_ = v___x_991_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7___boxed(lean_object* v_sz_995_, lean_object* v_i_996_, lean_object* v_bs_997_){
_start:
{
size_t v_sz_boxed_998_; size_t v_i_boxed_999_; lean_object* v_res_1000_; 
v_sz_boxed_998_ = lean_unbox_usize(v_sz_995_);
lean_dec(v_sz_995_);
v_i_boxed_999_ = lean_unbox_usize(v_i_996_);
lean_dec(v_i_996_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7(v_sz_boxed_998_, v_i_boxed_999_, v_bs_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__10(size_t v_sz_1001_, size_t v_i_1002_, lean_object* v_bs_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_lt(v_i_1002_, v_sz_1001_);
if (v___x_1004_ == 0)
{
return v_bs_1003_;
}
else
{
lean_object* v_v_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1023_; 
v_v_1005_ = lean_array_uget(v_bs_1003_, v_i_1002_);
v_fst_1006_ = lean_ctor_get(v_v_1005_, 0);
v_snd_1007_ = lean_ctor_get(v_v_1005_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_v_1005_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1009_ = v_v_1005_;
v_isShared_1010_ = v_isSharedCheck_1023_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_snd_1007_);
lean_inc(v_fst_1006_);
lean_dec(v_v_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1023_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v_bs_x27_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
v_bs_x27_1012_ = lean_array_uset(v_bs_1003_, v_i_1002_, v___x_1011_);
v___x_1013_ = 0;
v___x_1014_ = lean_box(v___x_1013_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1014_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_snd_1007_);
v___x_1016_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v_fst_1006_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_add(v_i_1002_, v___x_1018_);
v___x_1020_ = lean_array_uset(v_bs_x27_1012_, v_i_1002_, v___x_1017_);
v_i_1002_ = v___x_1019_;
v_bs_1003_ = v___x_1020_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__10___boxed(lean_object* v_sz_1024_, lean_object* v_i_1025_, lean_object* v_bs_1026_){
_start:
{
size_t v_sz_boxed_1027_; size_t v_i_boxed_1028_; lean_object* v_res_1029_; 
v_sz_boxed_1027_ = lean_unbox_usize(v_sz_1024_);
lean_dec(v_sz_1024_);
v_i_boxed_1028_ = lean_unbox_usize(v_i_1025_);
lean_dec(v_i_1025_);
v_res_1029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__10(v_sz_boxed_1027_, v_i_boxed_1028_, v_bs_1026_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__0(lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v_a_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_43325__overap_1045_; lean_object* v___x_1046_; 
v___x_43325__overap_1045_ = l_instInhabitedOfMonad___redArg(v___x_1030_, v___x_1031_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
v___x_1046_ = lean_apply_12(v___x_43325__overap_1045_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, lean_box(0));
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__0___boxed(lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v_a_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__0(v___x_1047_, v___x_1048_, v_a_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v_a_1049_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg___lam__0(lean_object* v_k_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v_b_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; 
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
lean_inc(v___y_1070_);
lean_inc_ref(v___y_1069_);
lean_inc(v___y_1068_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
v___x_1077_ = lean_apply_13(v_k_1063_, v_b_1071_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, lean_box(0));
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg___lam__0___boxed(lean_object* v_k_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg___lam__0(v_k_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v_b_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg(lean_object* v_name_1093_, uint8_t v_bi_1094_, lean_object* v_type_1095_, lean_object* v_k_1096_, uint8_t v_kind_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___f_1110_; lean_object* v___x_1111_; 
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc(v___y_1102_);
lean_inc_ref(v___y_1101_);
lean_inc(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_1110_, 0, v_k_1096_);
lean_closure_set(v___f_1110_, 1, v___y_1098_);
lean_closure_set(v___f_1110_, 2, v___y_1099_);
lean_closure_set(v___f_1110_, 3, v___y_1100_);
lean_closure_set(v___f_1110_, 4, v___y_1101_);
lean_closure_set(v___f_1110_, 5, v___y_1102_);
lean_closure_set(v___f_1110_, 6, v___y_1103_);
lean_closure_set(v___f_1110_, 7, v___y_1104_);
v___x_1111_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1093_, v_bi_1094_, v_type_1095_, v___f_1110_, v_kind_1097_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1111_) == 0)
{
return v___x_1111_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg___boxed(lean_object** _args){
lean_object* v_name_1120_ = _args[0];
lean_object* v_bi_1121_ = _args[1];
lean_object* v_type_1122_ = _args[2];
lean_object* v_k_1123_ = _args[3];
lean_object* v_kind_1124_ = _args[4];
lean_object* v___y_1125_ = _args[5];
lean_object* v___y_1126_ = _args[6];
lean_object* v___y_1127_ = _args[7];
lean_object* v___y_1128_ = _args[8];
lean_object* v___y_1129_ = _args[9];
lean_object* v___y_1130_ = _args[10];
lean_object* v___y_1131_ = _args[11];
lean_object* v___y_1132_ = _args[12];
lean_object* v___y_1133_ = _args[13];
lean_object* v___y_1134_ = _args[14];
lean_object* v___y_1135_ = _args[15];
lean_object* v___y_1136_ = _args[16];
_start:
{
uint8_t v_bi_boxed_1137_; uint8_t v_kind_boxed_1138_; lean_object* v_res_1139_; 
v_bi_boxed_1137_ = lean_unbox(v_bi_1121_);
v_kind_boxed_1138_ = lean_unbox(v_kind_1124_);
v_res_1139_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg(v_name_1120_, v_bi_boxed_1137_, v_type_1122_, v_k_1123_, v_kind_boxed_1138_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__1___boxed(lean_object** _args){
lean_object* v_acc_1140_ = _args[0];
lean_object* v_declInfos_1141_ = _args[1];
lean_object* v_k_1142_ = _args[2];
lean_object* v_kind_1143_ = _args[3];
lean_object* v_x_1144_ = _args[4];
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
uint8_t v_kind_boxed_1157_; lean_object* v_res_1158_; 
v_kind_boxed_1157_ = lean_unbox(v_kind_1143_);
v_res_1158_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__1(v_acc_1140_, v_declInfos_1141_, v_k_1142_, v_kind_boxed_1157_, v_x_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
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
lean_dec_ref(v___y_1145_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12(lean_object* v_declInfos_1159_, lean_object* v_k_1160_, uint8_t v_kind_1161_, lean_object* v_acc_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_toApplicative_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1272_; 
v___x_1175_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__0);
v___x_1176_ = l_StateRefT_x27_instMonad___redArg(v___x_1175_);
v_toApplicative_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1176_, 1);
lean_dec(v_unused_1273_);
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1272_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_toApplicative_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1272_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_toFunctor_1181_; lean_object* v_toSeq_1182_; lean_object* v_toSeqLeft_1183_; lean_object* v_toSeqRight_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1270_; 
v_toFunctor_1181_ = lean_ctor_get(v_toApplicative_1177_, 0);
v_toSeq_1182_ = lean_ctor_get(v_toApplicative_1177_, 2);
v_toSeqLeft_1183_ = lean_ctor_get(v_toApplicative_1177_, 3);
v_toSeqRight_1184_ = lean_ctor_get(v_toApplicative_1177_, 4);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_toApplicative_1177_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v_toApplicative_1177_, 1);
lean_dec(v_unused_1271_);
v___x_1186_ = v_toApplicative_1177_;
v_isShared_1187_ = v_isSharedCheck_1270_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_toSeqRight_1184_);
lean_inc(v_toSeqLeft_1183_);
lean_inc(v_toSeq_1182_);
lean_inc(v_toFunctor_1181_);
lean_dec(v_toApplicative_1177_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1270_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; lean_object* v___f_1193_; lean_object* v___f_1194_; lean_object* v___f_1195_; lean_object* v___x_1197_; 
v___f_1188_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__1));
v___f_1189_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1181_);
v___f_1190_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1190_, 0, v_toFunctor_1181_);
v___f_1191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1191_, 0, v_toFunctor_1181_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___f_1190_);
lean_ctor_set(v___x_1192_, 1, v___f_1191_);
v___f_1193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1193_, 0, v_toSeqRight_1184_);
v___f_1194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1194_, 0, v_toSeqLeft_1183_);
v___f_1195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1195_, 0, v_toSeq_1182_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 4, v___f_1193_);
lean_ctor_set(v___x_1186_, 3, v___f_1194_);
lean_ctor_set(v___x_1186_, 2, v___f_1195_);
lean_ctor_set(v___x_1186_, 1, v___f_1188_);
lean_ctor_set(v___x_1186_, 0, v___x_1192_);
v___x_1197_ = v___x_1186_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___f_1188_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v___f_1195_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v___f_1194_);
lean_ctor_set(v_reuseFailAlloc_1269_, 4, v___f_1193_);
v___x_1197_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___f_1189_);
lean_ctor_set(v___x_1179_, 0, v___x_1197_);
v___x_1199_ = v___x_1179_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___f_1189_);
v___x_1199_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v_toApplicative_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1266_; 
v___x_1200_ = l_StateRefT_x27_instMonad___redArg(v___x_1199_);
v_toApplicative_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1200_, 1);
lean_dec(v_unused_1267_);
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1266_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_toApplicative_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1266_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_toFunctor_1205_; lean_object* v_toSeq_1206_; lean_object* v_toSeqLeft_1207_; lean_object* v_toSeqRight_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1264_; 
v_toFunctor_1205_ = lean_ctor_get(v_toApplicative_1201_, 0);
v_toSeq_1206_ = lean_ctor_get(v_toApplicative_1201_, 2);
v_toSeqLeft_1207_ = lean_ctor_get(v_toApplicative_1201_, 3);
v_toSeqRight_1208_ = lean_ctor_get(v_toApplicative_1201_, 4);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_toApplicative_1201_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v_toApplicative_1201_, 1);
lean_dec(v_unused_1265_);
v___x_1210_ = v_toApplicative_1201_;
v_isShared_1211_ = v_isSharedCheck_1264_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_toSeqRight_1208_);
lean_inc(v_toSeqLeft_1207_);
lean_inc(v_toSeq_1206_);
lean_inc(v_toFunctor_1205_);
lean_dec(v_toApplicative_1201_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1264_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1221_; 
v___f_1212_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__3));
v___f_1213_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1205_);
v___f_1214_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1214_, 0, v_toFunctor_1205_);
v___f_1215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1215_, 0, v_toFunctor_1205_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___f_1214_);
lean_ctor_set(v___x_1216_, 1, v___f_1215_);
v___f_1217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1217_, 0, v_toSeqRight_1208_);
v___f_1218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1218_, 0, v_toSeqLeft_1207_);
v___f_1219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1219_, 0, v_toSeq_1206_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 4, v___f_1217_);
lean_ctor_set(v___x_1210_, 3, v___f_1218_);
lean_ctor_set(v___x_1210_, 2, v___f_1219_);
lean_ctor_set(v___x_1210_, 1, v___f_1212_);
lean_ctor_set(v___x_1210_, 0, v___x_1216_);
v___x_1221_ = v___x_1210_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___f_1212_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v___f_1219_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v___f_1218_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v___f_1217_);
v___x_1221_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___f_1213_);
lean_ctor_set(v___x_1203_, 0, v___x_1221_);
v___x_1223_ = v___x_1203_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___f_1213_);
v___x_1223_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1224_ = l_StateRefT_x27_instMonad___redArg(v___x_1223_);
v___x_1225_ = l_ReaderT_instMonad___redArg(v___x_1224_);
v___x_1226_ = l_StateRefT_x27_instMonad___redArg(v___x_1225_);
v___x_1227_ = l_ReaderT_instMonad___redArg(v___x_1226_);
v___x_1228_ = l_ReaderT_instMonad___redArg(v___x_1227_);
v___x_1229_ = l_StateRefT_x27_instMonad___redArg(v___x_1228_);
v___x_1230_ = l_ReaderT_instMonad___redArg(v___x_1229_);
v___x_1231_ = lean_array_get_size(v_acc_1162_);
v___x_1232_ = lean_array_get_size(v_declInfos_1159_);
v___x_1233_ = lean_nat_dec_lt(v___x_1231_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec_ref(v___x_1230_);
lean_dec_ref(v_declInfos_1159_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
v___x_1234_ = lean_apply_13(v_k_1160_, v_acc_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, lean_box(0));
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_snd_1244_; lean_object* v_fst_1245_; lean_object* v_fst_1246_; lean_object* v_snd_1247_; lean_object* v___x_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = 0;
v___x_1237_ = l_Lean_instInhabitedExpr;
v___f_1238_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__0___boxed), 15, 2);
lean_closure_set(v___f_1238_, 0, v___x_1230_);
lean_closure_set(v___f_1238_, 1, v___x_1237_);
v___f_1239_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1239_, 0, v___f_1238_);
v___x_1240_ = lean_box(v___x_1236_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v___f_1239_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1235_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_array_get(v___x_1242_, v_declInfos_1159_, v___x_1231_);
lean_dec_ref_known(v___x_1242_, 2);
v_snd_1244_ = lean_ctor_get(v___x_1243_, 1);
lean_inc(v_snd_1244_);
v_fst_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_fst_1245_);
lean_dec(v___x_1243_);
v_fst_1246_ = lean_ctor_get(v_snd_1244_, 0);
lean_inc(v_fst_1246_);
v_snd_1247_ = lean_ctor_get(v_snd_1244_, 1);
lean_inc(v_snd_1247_);
lean_dec(v_snd_1244_);
v___x_1248_ = lean_box(v_kind_1161_);
lean_inc_ref(v_acc_1162_);
v___f_1249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__1___boxed), 17, 4);
lean_closure_set(v___f_1249_, 0, v_acc_1162_);
lean_closure_set(v___f_1249_, 1, v_declInfos_1159_);
lean_closure_set(v___f_1249_, 2, v_k_1160_);
lean_closure_set(v___f_1249_, 3, v___x_1248_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
v___x_1250_ = lean_apply_13(v_snd_1247_, v_acc_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, lean_box(0));
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = lean_unbox(v_fst_1246_);
lean_dec(v_fst_1246_);
v___x_1253_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg(v_fst_1245_, v___x_1252_, v_a_1251_, v___f_1249_, v_kind_1161_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v___f_1249_);
lean_dec(v_fst_1246_);
lean_dec(v_fst_1245_);
v_a_1254_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1250_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___lam__1(lean_object* v_acc_1274_, lean_object* v_declInfos_1275_, lean_object* v_k_1276_, uint8_t v_kind_1277_, lean_object* v_x_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_array_push(v_acc_1274_, v_x_1278_);
v___x_1292_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12(v_declInfos_1275_, v_k_1276_, v_kind_1277_, v___x_1291_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12___boxed(lean_object* v_declInfos_1293_, lean_object* v_k_1294_, lean_object* v_kind_1295_, lean_object* v_acc_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v_kind_boxed_1309_; lean_object* v_res_1310_; 
v_kind_boxed_1309_ = lean_unbox(v_kind_1295_);
v_res_1310_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12(v_declInfos_1293_, v_k_1294_, v_kind_boxed_1309_, v_acc_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
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
lean_dec_ref(v___y_1297_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11(lean_object* v_declInfos_1313_, lean_object* v_k_1314_, uint8_t v_kind_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11___closed__0));
v___x_1329_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12(v_declInfos_1313_, v_k_1314_, v_kind_1315_, v___x_1328_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11___boxed(lean_object* v_declInfos_1330_, lean_object* v_k_1331_, lean_object* v_kind_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
uint8_t v_kind_boxed_1345_; lean_object* v_res_1346_; 
v_kind_boxed_1345_ = lean_unbox(v_kind_1332_);
v_res_1346_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11(v_declInfos_1330_, v_k_1331_, v_kind_boxed_1345_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8(lean_object* v_declInfos_1347_, lean_object* v_k_1348_, uint8_t v_kind_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
size_t v_sz_1362_; size_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_sz_1362_ = lean_array_size(v_declInfos_1347_);
v___x_1363_ = ((size_t)0ULL);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__10(v_sz_1362_, v___x_1363_, v_declInfos_1347_);
v___x_1365_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11(v___x_1364_, v_k_1348_, v_kind_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8___boxed(lean_object* v_declInfos_1366_, lean_object* v_k_1367_, lean_object* v_kind_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_kind_boxed_1381_; lean_object* v_res_1382_; 
v_kind_boxed_1381_ = lean_unbox(v_kind_1368_);
v_res_1382_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8(v_declInfos_1366_, v_k_1367_, v_kind_boxed_1381_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6(lean_object* v_declInfos_1383_, lean_object* v_k_1384_, uint8_t v_kind_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
size_t v_sz_1398_; size_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_sz_1398_ = lean_array_size(v_declInfos_1383_);
v___x_1399_ = ((size_t)0ULL);
v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__7(v_sz_1398_, v___x_1399_, v_declInfos_1383_);
v___x_1401_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8(v___x_1400_, v_k_1384_, v_kind_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6___boxed(lean_object* v_declInfos_1402_, lean_object* v_k_1403_, lean_object* v_kind_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v_kind_boxed_1417_; lean_object* v_res_1418_; 
v_kind_boxed_1417_ = lean_unbox(v_kind_1404_);
v_res_1418_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6(v_declInfos_1402_, v_k_1403_, v_kind_boxed_1417_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__5(size_t v_sz_1419_, size_t v_i_1420_, lean_object* v_bs_1421_){
_start:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_usize_dec_lt(v_i_1420_, v_sz_1419_);
if (v___x_1422_ == 0)
{
return v_bs_1421_;
}
else
{
lean_object* v_v_1423_; lean_object* v_type_x27_1424_; lean_object* v___x_1425_; lean_object* v_bs_x27_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; 
v_v_1423_ = lean_array_uget_borrowed(v_bs_1421_, v_i_1420_);
v_type_x27_1424_ = lean_ctor_get(v_v_1423_, 1);
lean_inc_ref(v_type_x27_1424_);
v___x_1425_ = lean_unsigned_to_nat(0u);
v_bs_x27_1426_ = lean_array_uset(v_bs_1421_, v_i_1420_, v___x_1425_);
v___x_1427_ = lean_box(0);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v_type_x27_1424_);
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_add(v_i_1420_, v___x_1429_);
v___x_1431_ = lean_array_uset(v_bs_x27_1426_, v_i_1420_, v___x_1428_);
v_i_1420_ = v___x_1430_;
v_bs_1421_ = v___x_1431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__5___boxed(lean_object* v_sz_1433_, lean_object* v_i_1434_, lean_object* v_bs_1435_){
_start:
{
size_t v_sz_boxed_1436_; size_t v_i_boxed_1437_; lean_object* v_res_1438_; 
v_sz_boxed_1436_ = lean_unbox_usize(v_sz_1433_);
lean_dec(v_sz_1433_);
v_i_boxed_1437_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__5(v_sz_boxed_1436_, v_i_boxed_1437_, v_bs_1435_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__2(lean_object* v_rewrite_1439_, size_t v_sz_1440_, size_t v_i_1441_, lean_object* v_bs_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
uint8_t v___x_1455_; 
v___x_1455_ = lean_usize_dec_lt(v_i_1441_, v_sz_1440_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec_ref(v_rewrite_1439_);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_bs_1442_);
return v___x_1456_;
}
else
{
lean_object* v_v_1457_; lean_object* v___x_1458_; lean_object* v_bs_x27_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_v_1457_ = lean_array_uget(v_bs_1442_, v_i_1441_);
v___x_1458_ = lean_unsigned_to_nat(0u);
v_bs_x27_1459_ = lean_array_uset(v_bs_1442_, v_i_1441_, v___x_1458_);
v___x_1460_ = l_Lean_Expr_fvarId_x21(v_v_1457_);
lean_dec(v_v_1457_);
v___x_1461_ = l_Lean_FVarId_getType___redArg(v___x_1460_, v___y_1450_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_Meta_Sym_shareCommon(v_a_1462_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
lean_inc_ref(v_rewrite_1439_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
lean_inc(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
v___x_1465_ = lean_apply_13(v_rewrite_1439_, v_a_1464_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, lean_box(0));
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; size_t v___x_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = lean_usize_add(v_i_1441_, v___x_1467_);
v___x_1469_ = lean_array_uset(v_bs_x27_1459_, v_i_1441_, v_a_1466_);
v_i_1441_ = v___x_1468_;
v_bs_1442_ = v___x_1469_;
goto _start;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v_bs_x27_1459_);
lean_dec_ref(v_rewrite_1439_);
v_a_1471_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1465_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1465_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_bs_x27_1459_);
lean_dec_ref(v_rewrite_1439_);
v_a_1479_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1463_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1463_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_bs_x27_1459_);
lean_dec_ref(v_rewrite_1439_);
v_a_1487_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1461_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1461_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__2___boxed(lean_object* v_rewrite_1495_, lean_object* v_sz_1496_, lean_object* v_i_1497_, lean_object* v_bs_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
size_t v_sz_boxed_1511_; size_t v_i_boxed_1512_; lean_object* v_res_1513_; 
v_sz_boxed_1511_ = lean_unbox_usize(v_sz_1496_);
lean_dec(v_sz_1496_);
v_i_boxed_1512_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__2(v_rewrite_1495_, v_sz_boxed_1511_, v_i_boxed_1512_, v_bs_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__2));
v___x_1518_ = lean_unsigned_to_nat(6u);
v___x_1519_ = lean_unsigned_to_nat(103u);
v___x_1520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__1));
v___x_1521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__0));
v___x_1522_ = l_mkPanicMessageWithDecl(v___x_1521_, v___x_1520_, v___x_1519_, v___x_1518_, v___x_1517_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1(lean_object* v___x_1523_, lean_object* v_n_1524_, lean_object* v_rewrite_1525_, lean_object* v_name_1526_, lean_object* v_source_1527_, lean_object* v_boundSorts_1528_, lean_object* v_value_1529_, lean_object* v_xs_1530_, lean_object* v_body_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = lean_array_get_size(v_xs_1530_);
v___x_1545_ = lean_nat_dec_eq(v___x_1544_, v___x_1523_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v_body_1531_);
lean_dec_ref(v_xs_1530_);
lean_dec_ref(v_value_1529_);
lean_dec_ref(v_boundSorts_1528_);
lean_dec(v_source_1527_);
lean_dec(v_name_1526_);
lean_dec_ref(v_rewrite_1525_);
lean_dec(v_n_1524_);
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___closed__3);
v___x_1547_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__0(v___x_1546_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v_args_1551_; lean_object* v_lower_1553_; lean_object* v_upper_1554_; uint8_t v___x_1608_; 
v___x_1548_ = lean_unsigned_to_nat(0u);
lean_inc(v_n_1524_);
lean_inc_ref(v_xs_1530_);
v___x_1549_ = l_Array_toSubarray___redArg(v_xs_1530_, v___x_1548_, v_n_1524_);
v___x_1550_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11___closed__0));
v_args_1551_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__1___redArg(v___x_1549_, v___x_1550_);
v___x_1608_ = lean_nat_dec_le(v_n_1524_, v___x_1548_);
if (v___x_1608_ == 0)
{
v_lower_1553_ = v_n_1524_;
v_upper_1554_ = v___x_1544_;
goto v___jp_1552_;
}
else
{
lean_dec(v_n_1524_);
v_lower_1553_ = v___x_1548_;
v_upper_1554_ = v___x_1544_;
goto v___jp_1552_;
}
v___jp_1552_:
{
lean_object* v___x_1555_; lean_object* v_guards_1556_; lean_object* v___x_1557_; 
v___x_1555_ = l_Array_toSubarray___redArg(v_xs_1530_, v_lower_1553_, v_upper_1554_);
v_guards_1556_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__1___redArg(v___x_1555_, v___x_1550_);
v___x_1557_ = l_Lean_Meta_Sym_shareCommon(v_body_1531_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
lean_inc_ref(v_rewrite_1525_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc(v___y_1536_);
lean_inc_ref(v___y_1535_);
lean_inc(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
v___x_1559_ = lean_apply_13(v_rewrite_1525_, v_a_1558_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1591_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1591_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1591_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_type_1564_; lean_object* v_type_x27_1565_; lean_object* v_proof_x3f_1566_; uint8_t v___x_1567_; 
v_type_1564_ = lean_ctor_get(v_a_1560_, 0);
lean_inc_ref(v_type_1564_);
v_type_x27_1565_ = lean_ctor_get(v_a_1560_, 1);
lean_inc_ref(v_type_x27_1565_);
v_proof_x3f_1566_ = lean_ctor_get(v_a_1560_, 2);
lean_inc(v_proof_x3f_1566_);
lean_dec(v_a_1560_);
v___x_1567_ = l_Lean_Expr_isTrue(v_type_x27_1565_);
if (v___x_1567_ == 0)
{
size_t v_sz_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
lean_del_object(v___x_1562_);
v_sz_1568_ = lean_array_size(v_guards_1556_);
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__2(v_rewrite_1525_, v_sz_1568_, v___x_1569_, v_guards_1556_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___f_1574_; size_t v_sz_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_n(v_a_1571_, 2);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = lean_box(v___x_1567_);
v___x_1573_ = lean_box(v___x_1545_);
v___f_1574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___boxed), 26, 13);
lean_closure_set(v___f_1574_, 0, v_args_1551_);
lean_closure_set(v___f_1574_, 1, v_type_x27_1565_);
lean_closure_set(v___f_1574_, 2, v_name_1526_);
lean_closure_set(v___f_1574_, 3, v_source_1527_);
lean_closure_set(v___f_1574_, 4, v_boundSorts_1528_);
lean_closure_set(v___f_1574_, 5, v___x_1572_);
lean_closure_set(v___f_1574_, 6, v___x_1573_);
lean_closure_set(v___f_1574_, 7, v_a_1571_);
lean_closure_set(v___f_1574_, 8, v___x_1548_);
lean_closure_set(v___f_1574_, 9, v___x_1550_);
lean_closure_set(v___f_1574_, 10, v_value_1529_);
lean_closure_set(v___f_1574_, 11, v_proof_x3f_1566_);
lean_closure_set(v___f_1574_, 12, v_type_1564_);
v_sz_1575_ = lean_array_size(v_a_1571_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__5(v_sz_1575_, v___x_1569_, v_a_1571_);
v___x_1577_ = 0;
v___x_1578_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6(v___x_1576_, v___f_1574_, v___x_1577_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1578_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_proof_x3f_1566_);
lean_dec_ref(v_type_x27_1565_);
lean_dec_ref(v_type_1564_);
lean_dec_ref(v_args_1551_);
lean_dec_ref(v_value_1529_);
lean_dec_ref(v_boundSorts_1528_);
lean_dec(v_source_1527_);
lean_dec(v_name_1526_);
v_a_1579_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1570_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1570_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_dec(v_proof_x3f_1566_);
lean_dec_ref(v_type_x27_1565_);
lean_dec_ref(v_type_1564_);
lean_dec_ref(v_guards_1556_);
lean_dec_ref(v_args_1551_);
lean_dec_ref(v_value_1529_);
lean_dec_ref(v_boundSorts_1528_);
lean_dec(v_source_1527_);
lean_dec(v_name_1526_);
lean_dec_ref(v_rewrite_1525_);
v___x_1587_ = lean_box(0);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1587_);
v___x_1589_ = v___x_1562_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_guards_1556_);
lean_dec_ref(v_args_1551_);
lean_dec_ref(v_value_1529_);
lean_dec_ref(v_boundSorts_1528_);
lean_dec(v_source_1527_);
lean_dec(v_name_1526_);
lean_dec_ref(v_rewrite_1525_);
v_a_1592_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1559_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1559_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v_guards_1556_);
lean_dec_ref(v_args_1551_);
lean_dec_ref(v_value_1529_);
lean_dec_ref(v_boundSorts_1528_);
lean_dec(v_source_1527_);
lean_dec(v_name_1526_);
lean_dec_ref(v_rewrite_1525_);
v_a_1600_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1557_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1557_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___boxed(lean_object** _args){
lean_object* v___x_1609_ = _args[0];
lean_object* v_n_1610_ = _args[1];
lean_object* v_rewrite_1611_ = _args[2];
lean_object* v_name_1612_ = _args[3];
lean_object* v_source_1613_ = _args[4];
lean_object* v_boundSorts_1614_ = _args[5];
lean_object* v_value_1615_ = _args[6];
lean_object* v_xs_1616_ = _args[7];
lean_object* v_body_1617_ = _args[8];
lean_object* v___y_1618_ = _args[9];
lean_object* v___y_1619_ = _args[10];
lean_object* v___y_1620_ = _args[11];
lean_object* v___y_1621_ = _args[12];
lean_object* v___y_1622_ = _args[13];
lean_object* v___y_1623_ = _args[14];
lean_object* v___y_1624_ = _args[15];
lean_object* v___y_1625_ = _args[16];
lean_object* v___y_1626_ = _args[17];
lean_object* v___y_1627_ = _args[18];
lean_object* v___y_1628_ = _args[19];
lean_object* v___y_1629_ = _args[20];
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1(v___x_1609_, v_n_1610_, v_rewrite_1611_, v_name_1612_, v_source_1613_, v_boundSorts_1614_, v_value_1615_, v_xs_1616_, v_body_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___x_1609_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact(lean_object* v_rewrite_1631_, lean_object* v_fact_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_hyp_1645_; lean_object* v_boundSorts_1646_; lean_object* v_name_1647_; lean_object* v_type_1648_; lean_object* v_value_1649_; lean_object* v_source_1650_; lean_object* v_n_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v_hyp_1645_ = lean_ctor_get(v_fact_1632_, 0);
lean_inc_ref(v_hyp_1645_);
v_boundSorts_1646_ = lean_ctor_get(v_fact_1632_, 1);
lean_inc_ref(v_boundSorts_1646_);
lean_dec_ref(v_fact_1632_);
v_name_1647_ = lean_ctor_get(v_hyp_1645_, 0);
lean_inc(v_name_1647_);
v_type_1648_ = lean_ctor_get(v_hyp_1645_, 1);
lean_inc_ref(v_type_1648_);
v_value_1649_ = lean_ctor_get(v_hyp_1645_, 2);
lean_inc_ref(v_value_1649_);
v_source_1650_ = lean_ctor_get(v_hyp_1645_, 3);
lean_inc(v_source_1650_);
lean_dec_ref(v_hyp_1645_);
v_n_1651_ = lean_array_get_size(v_boundSorts_1646_);
v___x_1652_ = lean_unsigned_to_nat(2u);
v___x_1653_ = lean_nat_mul(v___x_1652_, v_n_1651_);
lean_inc(v___x_1653_);
v___f_1654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__1___boxed), 21, 7);
lean_closure_set(v___f_1654_, 0, v___x_1653_);
lean_closure_set(v___f_1654_, 1, v_n_1651_);
lean_closure_set(v___f_1654_, 2, v_rewrite_1631_);
lean_closure_set(v___f_1654_, 3, v_name_1647_);
lean_closure_set(v___f_1654_, 4, v_source_1650_);
lean_closure_set(v___f_1654_, 5, v_boundSorts_1646_);
lean_closure_set(v___f_1654_, 6, v_value_1649_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
v___x_1656_ = 0;
v___x_1657_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__7___redArg(v_type_1648_, v___x_1655_, v___f_1654_, v___x_1656_, v___x_1656_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___boxed(lean_object* v_rewrite_1658_, lean_object* v_fact_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact(v_rewrite_1658_, v_fact_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__1(lean_object* v_inst_1673_, lean_object* v_R_1674_, lean_object* v_a_1675_, lean_object* v_b_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__1___redArg(v_a_1675_, v_b_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3(lean_object* v_cls_1678_, lean_object* v_msg_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg(v_cls_1678_, v_msg_1679_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___boxed(lean_object* v_cls_1693_, lean_object* v_msg_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3(v_cls_1693_, v_msg_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13(lean_object* v_00_u03b1_1708_, lean_object* v_name_1709_, uint8_t v_bi_1710_, lean_object* v_type_1711_, lean_object* v_k_1712_, uint8_t v_kind_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___redArg(v_name_1709_, v_bi_1710_, v_type_1711_, v_k_1712_, v_kind_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13___boxed(lean_object** _args){
lean_object* v_00_u03b1_1727_ = _args[0];
lean_object* v_name_1728_ = _args[1];
lean_object* v_bi_1729_ = _args[2];
lean_object* v_type_1730_ = _args[3];
lean_object* v_k_1731_ = _args[4];
lean_object* v_kind_1732_ = _args[5];
lean_object* v___y_1733_ = _args[6];
lean_object* v___y_1734_ = _args[7];
lean_object* v___y_1735_ = _args[8];
lean_object* v___y_1736_ = _args[9];
lean_object* v___y_1737_ = _args[10];
lean_object* v___y_1738_ = _args[11];
lean_object* v___y_1739_ = _args[12];
lean_object* v___y_1740_ = _args[13];
lean_object* v___y_1741_ = _args[14];
lean_object* v___y_1742_ = _args[15];
lean_object* v___y_1743_ = _args[16];
lean_object* v___y_1744_ = _args[17];
_start:
{
uint8_t v_bi_boxed_1745_; uint8_t v_kind_boxed_1746_; lean_object* v_res_1747_; 
v_bi_boxed_1745_ = lean_unbox(v_bi_1729_);
v_kind_boxed_1746_ = lean_unbox(v_kind_1732_);
v_res_1747_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__6_spec__8_spec__11_spec__12_spec__13(v_00_u03b1_1727_, v_name_1728_, v_bi_boxed_1745_, v_type_1730_, v_k_1731_, v_kind_boxed_1746_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1747_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = lean_unsigned_to_nat(32u);
v___x_1749_ = lean_mk_empty_array_with_capacity(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = ((size_t)5ULL);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_unsigned_to_nat(32u);
v___x_1754_ = lean_mk_empty_array_with_capacity(v___x_1753_);
v___x_1755_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__0);
v___x_1756_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1754_);
lean_ctor_set(v___x_1756_, 2, v___x_1752_);
lean_ctor_set(v___x_1756_, 3, v___x_1752_);
lean_ctor_set_usize(v___x_1756_, 4, v___x_1751_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v_traceState_1760_; lean_object* v_traces_1761_; lean_object* v___x_1762_; lean_object* v_traceState_1763_; lean_object* v_env_1764_; lean_object* v_nextMacroScope_1765_; lean_object* v_ngen_1766_; lean_object* v_auxDeclNGen_1767_; lean_object* v_cache_1768_; lean_object* v_recordedDeps_1769_; lean_object* v_messages_1770_; lean_object* v_infoState_1771_; lean_object* v_snapshotTasks_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1791_; 
v___x_1759_ = lean_st_ref_get(v___y_1757_);
v_traceState_1760_ = lean_ctor_get(v___x_1759_, 4);
lean_inc_ref(v_traceState_1760_);
lean_dec(v___x_1759_);
v_traces_1761_ = lean_ctor_get(v_traceState_1760_, 0);
lean_inc_ref(v_traces_1761_);
lean_dec_ref(v_traceState_1760_);
v___x_1762_ = lean_st_ref_take(v___y_1757_);
v_traceState_1763_ = lean_ctor_get(v___x_1762_, 4);
v_env_1764_ = lean_ctor_get(v___x_1762_, 0);
v_nextMacroScope_1765_ = lean_ctor_get(v___x_1762_, 1);
v_ngen_1766_ = lean_ctor_get(v___x_1762_, 2);
v_auxDeclNGen_1767_ = lean_ctor_get(v___x_1762_, 3);
v_cache_1768_ = lean_ctor_get(v___x_1762_, 5);
v_recordedDeps_1769_ = lean_ctor_get(v___x_1762_, 6);
v_messages_1770_ = lean_ctor_get(v___x_1762_, 7);
v_infoState_1771_ = lean_ctor_get(v___x_1762_, 8);
v_snapshotTasks_1772_ = lean_ctor_get(v___x_1762_, 9);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1774_ = v___x_1762_;
v_isShared_1775_ = v_isSharedCheck_1791_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_snapshotTasks_1772_);
lean_inc(v_infoState_1771_);
lean_inc(v_messages_1770_);
lean_inc(v_recordedDeps_1769_);
lean_inc(v_cache_1768_);
lean_inc(v_traceState_1763_);
lean_inc(v_auxDeclNGen_1767_);
lean_inc(v_ngen_1766_);
lean_inc(v_nextMacroScope_1765_);
lean_inc(v_env_1764_);
lean_dec(v___x_1762_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1791_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
uint64_t v_tid_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1789_; 
v_tid_1776_ = lean_ctor_get_uint64(v_traceState_1763_, sizeof(void*)*1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_traceState_1763_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v_traceState_1763_, 0);
lean_dec(v_unused_1790_);
v___x_1778_ = v_traceState_1763_;
v_isShared_1779_ = v_isSharedCheck_1789_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v_traceState_1763_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1789_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___closed__1);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1780_);
v___x_1782_ = v___x_1778_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1780_);
lean_ctor_set_uint64(v_reuseFailAlloc_1788_, sizeof(void*)*1, v_tid_1776_);
v___x_1782_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 4, v___x_1782_);
v___x_1784_ = v___x_1774_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_env_1764_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_nextMacroScope_1765_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_ngen_1766_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_auxDeclNGen_1767_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1787_, 5, v_cache_1768_);
lean_ctor_set(v_reuseFailAlloc_1787_, 6, v_recordedDeps_1769_);
lean_ctor_set(v_reuseFailAlloc_1787_, 7, v_messages_1770_);
lean_ctor_set(v_reuseFailAlloc_1787_, 8, v_infoState_1771_);
lean_ctor_set(v_reuseFailAlloc_1787_, 9, v_snapshotTasks_1772_);
v___x_1784_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_st_ref_put(v___y_1757_, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_traces_1761_);
return v___x_1786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg___boxed(lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_1792_);
lean_dec(v___y_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1(lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___boxed(lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1(v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(lean_object* v_opts_1821_, lean_object* v_opt_1822_){
_start:
{
lean_object* v_name_1823_; lean_object* v_defValue_1824_; lean_object* v_map_1825_; lean_object* v___x_1826_; 
v_name_1823_ = lean_ctor_get(v_opt_1822_, 0);
v_defValue_1824_ = lean_ctor_get(v_opt_1822_, 1);
v_map_1825_ = lean_ctor_get(v_opts_1821_, 0);
v___x_1826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1825_, v_name_1823_);
if (lean_obj_tag(v___x_1826_) == 0)
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_unbox(v_defValue_1824_);
return v___x_1827_;
}
else
{
lean_object* v_val_1828_; 
v_val_1828_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_val_1828_);
lean_dec_ref_known(v___x_1826_, 1);
if (lean_obj_tag(v_val_1828_) == 1)
{
uint8_t v_v_1829_; 
v_v_1829_ = lean_ctor_get_uint8(v_val_1828_, 0);
lean_dec_ref_known(v_val_1828_, 0);
return v_v_1829_;
}
else
{
uint8_t v___x_1830_; 
lean_dec(v_val_1828_);
v___x_1830_ = lean_unbox(v_defValue_1824_);
return v___x_1830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2___boxed(lean_object* v_opts_1831_, lean_object* v_opt_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_opts_1831_, v_opt_1832_);
lean_dec_ref(v_opt_1832_);
lean_dec_ref(v_opts_1831_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__0));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0(lean_object* v_x_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___closed__1);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0___boxed(lean_object* v_x_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__0(v_x_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec_ref(v_x_1853_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0___lam__0(lean_object* v_dsimpMethods_1867_, lean_object* v_dsimpConfig_1868_, lean_object* v_simpMethods_1869_, lean_object* v_simpConfig_1870_, lean_object* v_type_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1884_ = 0;
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_box(6);
lean_inc_ref(v_type_1871_);
v___x_1887_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v_type_1871_);
lean_ctor_set(v___x_1887_, 2, v_type_1871_);
lean_ctor_set(v___x_1887_, 3, v___x_1886_);
v___x_1888_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_1884_, v_dsimpMethods_1867_, v_dsimpConfig_1868_, v___x_1887_, v___y_1873_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v_type_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v_type_1890_ = lean_ctor_get(v_a_1889_, 1);
lean_inc_ref_n(v_type_1890_, 2);
lean_dec(v_a_1889_);
v___x_1891_ = 0;
v___x_1892_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpExpr___redArg(v___x_1891_, v_simpMethods_1869_, v_simpConfig_1870_, v_type_1890_, v___y_1873_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1909_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1909_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1909_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
if (lean_obj_tag(v_a_1893_) == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
lean_dec_ref_known(v_a_1893_, 0);
v___x_1897_ = lean_box(0);
lean_inc_ref(v_type_1890_);
v___x_1898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1898_, 0, v_type_1890_);
lean_ctor_set(v___x_1898_, 1, v_type_1890_);
lean_ctor_set(v___x_1898_, 2, v___x_1897_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1898_);
v___x_1900_ = v___x_1895_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
lean_object* v_e_x27_1902_; lean_object* v_proof_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v_e_x27_1902_ = lean_ctor_get(v_a_1893_, 0);
lean_inc_ref(v_e_x27_1902_);
v_proof_1903_ = lean_ctor_get(v_a_1893_, 1);
lean_inc_ref(v_proof_1903_);
lean_dec_ref_known(v_a_1893_, 2);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_proof_1903_);
v___x_1905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1905_, 0, v_type_1890_);
lean_ctor_set(v___x_1905_, 1, v_e_x27_1902_);
lean_ctor_set(v___x_1905_, 2, v___x_1904_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1905_);
v___x_1907_ = v___x_1895_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v_type_1890_);
v_a_1910_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1892_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1892_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref(v_simpConfig_1870_);
lean_dec_ref(v_simpMethods_1869_);
v_a_1918_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1888_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1888_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0___lam__0___boxed(lean_object** _args){
lean_object* v_dsimpMethods_1926_ = _args[0];
lean_object* v_dsimpConfig_1927_ = _args[1];
lean_object* v_simpMethods_1928_ = _args[2];
lean_object* v_simpConfig_1929_ = _args[3];
lean_object* v_type_1930_ = _args[4];
lean_object* v___y_1931_ = _args[5];
lean_object* v___y_1932_ = _args[6];
lean_object* v___y_1933_ = _args[7];
lean_object* v___y_1934_ = _args[8];
lean_object* v___y_1935_ = _args[9];
lean_object* v___y_1936_ = _args[10];
lean_object* v___y_1937_ = _args[11];
lean_object* v___y_1938_ = _args[12];
lean_object* v___y_1939_ = _args[13];
lean_object* v___y_1940_ = _args[14];
lean_object* v___y_1941_ = _args[15];
lean_object* v___y_1942_ = _args[16];
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0___lam__0(v_dsimpMethods_1926_, v_dsimpConfig_1927_, v_simpMethods_1928_, v_simpConfig_1929_, v_type_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0(lean_object* v_dsimpMethods_1944_, lean_object* v_dsimpConfig_1945_, lean_object* v_simpMethods_1946_, lean_object* v_simpConfig_1947_, lean_object* v_as_1948_, size_t v_i_1949_, size_t v_stop_1950_, lean_object* v_b_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_a_1965_; uint8_t v___x_1969_; 
v___x_1969_ = lean_usize_dec_eq(v_i_1949_, v_stop_1950_);
if (v___x_1969_ == 0)
{
lean_object* v___f_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_inc_ref(v_simpConfig_1947_);
lean_inc_ref(v_simpMethods_1946_);
lean_inc_ref(v_dsimpConfig_1945_);
lean_inc_ref(v_dsimpMethods_1944_);
v___f_1970_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0___lam__0___boxed), 17, 4);
lean_closure_set(v___f_1970_, 0, v_dsimpMethods_1944_);
lean_closure_set(v___f_1970_, 1, v_dsimpConfig_1945_);
lean_closure_set(v___f_1970_, 2, v_simpMethods_1946_);
lean_closure_set(v___f_1970_, 3, v_simpConfig_1947_);
v___x_1971_ = lean_array_uget_borrowed(v_as_1948_, v_i_1949_);
lean_inc(v___x_1971_);
v___x_1972_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact(v___f_1970_, v___x_1971_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
if (lean_obj_tag(v_a_1973_) == 0)
{
v_a_1965_ = v_b_1951_;
goto v___jp_1964_;
}
else
{
lean_object* v_val_1974_; lean_object* v___x_1975_; 
v_val_1974_ = lean_ctor_get(v_a_1973_, 0);
lean_inc(v_val_1974_);
lean_dec_ref_known(v_a_1973_, 1);
v___x_1975_ = lean_array_push(v_b_1951_, v_val_1974_);
v_a_1965_ = v___x_1975_;
goto v___jp_1964_;
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v_b_1951_);
lean_dec_ref(v_simpConfig_1947_);
lean_dec_ref(v_simpMethods_1946_);
lean_dec_ref(v_dsimpConfig_1945_);
lean_dec_ref(v_dsimpMethods_1944_);
v_a_1976_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1972_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1972_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v___x_1984_; 
lean_dec_ref(v_simpConfig_1947_);
lean_dec_ref(v_simpMethods_1946_);
lean_dec_ref(v_dsimpConfig_1945_);
lean_dec_ref(v_dsimpMethods_1944_);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_b_1951_);
return v___x_1984_;
}
v___jp_1964_:
{
size_t v___x_1966_; size_t v___x_1967_; 
v___x_1966_ = ((size_t)1ULL);
v___x_1967_ = lean_usize_add(v_i_1949_, v___x_1966_);
v_i_1949_ = v___x_1967_;
v_b_1951_ = v_a_1965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_dsimpMethods_1985_ = _args[0];
lean_object* v_dsimpConfig_1986_ = _args[1];
lean_object* v_simpMethods_1987_ = _args[2];
lean_object* v_simpConfig_1988_ = _args[3];
lean_object* v_as_1989_ = _args[4];
lean_object* v_i_1990_ = _args[5];
lean_object* v_stop_1991_ = _args[6];
lean_object* v_b_1992_ = _args[7];
lean_object* v___y_1993_ = _args[8];
lean_object* v___y_1994_ = _args[9];
lean_object* v___y_1995_ = _args[10];
lean_object* v___y_1996_ = _args[11];
lean_object* v___y_1997_ = _args[12];
lean_object* v___y_1998_ = _args[13];
lean_object* v___y_1999_ = _args[14];
lean_object* v___y_2000_ = _args[15];
lean_object* v___y_2001_ = _args[16];
lean_object* v___y_2002_ = _args[17];
lean_object* v___y_2003_ = _args[18];
lean_object* v___y_2004_ = _args[19];
_start:
{
size_t v_i_boxed_2005_; size_t v_stop_boxed_2006_; lean_object* v_res_2007_; 
v_i_boxed_2005_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_stop_boxed_2006_ = lean_unbox_usize(v_stop_1991_);
lean_dec(v_stop_1991_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0(v_dsimpMethods_1985_, v_dsimpConfig_1986_, v_simpMethods_1987_, v_simpConfig_1988_, v_as_1989_, v_i_boxed_2005_, v_stop_boxed_2006_, v_b_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_as_1989_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0(lean_object* v_dsimpMethods_2010_, lean_object* v_dsimpConfig_2011_, lean_object* v_simpMethods_2012_, lean_object* v_simpConfig_2013_, lean_object* v_as_2014_, lean_object* v_start_2015_, lean_object* v_stop_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0___closed__0));
v___x_2030_ = lean_nat_dec_lt(v_start_2015_, v_stop_2016_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec_ref(v_simpConfig_2013_);
lean_dec_ref(v_simpMethods_2012_);
lean_dec_ref(v_dsimpConfig_2011_);
lean_dec_ref(v_dsimpMethods_2010_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2029_);
return v___x_2031_;
}
else
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = lean_array_get_size(v_as_2014_);
v___x_2033_ = lean_nat_dec_le(v_stop_2016_, v___x_2032_);
if (v___x_2033_ == 0)
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_nat_dec_lt(v_start_2015_, v___x_2032_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
lean_dec_ref(v_simpConfig_2013_);
lean_dec_ref(v_simpMethods_2012_);
lean_dec_ref(v_dsimpConfig_2011_);
lean_dec_ref(v_dsimpMethods_2010_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2029_);
return v___x_2035_;
}
else
{
size_t v___x_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_usize_of_nat(v_start_2015_);
v___x_2037_ = lean_usize_of_nat(v___x_2032_);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0(v_dsimpMethods_2010_, v_dsimpConfig_2011_, v_simpMethods_2012_, v_simpConfig_2013_, v_as_2014_, v___x_2036_, v___x_2037_, v___x_2029_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2038_;
}
}
else
{
size_t v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_usize_of_nat(v_start_2015_);
v___x_2040_ = lean_usize_of_nat(v_stop_2016_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0_spec__0(v_dsimpMethods_2010_, v_dsimpConfig_2011_, v_simpMethods_2012_, v_simpConfig_2013_, v_as_2014_, v___x_2039_, v___x_2040_, v___x_2029_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0___boxed(lean_object** _args){
lean_object* v_dsimpMethods_2042_ = _args[0];
lean_object* v_dsimpConfig_2043_ = _args[1];
lean_object* v_simpMethods_2044_ = _args[2];
lean_object* v_simpConfig_2045_ = _args[3];
lean_object* v_as_2046_ = _args[4];
lean_object* v_start_2047_ = _args[5];
lean_object* v_stop_2048_ = _args[6];
lean_object* v___y_2049_ = _args[7];
lean_object* v___y_2050_ = _args[8];
lean_object* v___y_2051_ = _args[9];
lean_object* v___y_2052_ = _args[10];
lean_object* v___y_2053_ = _args[11];
lean_object* v___y_2054_ = _args[12];
lean_object* v___y_2055_ = _args[13];
lean_object* v___y_2056_ = _args[14];
lean_object* v___y_2057_ = _args[15];
lean_object* v___y_2058_ = _args[16];
lean_object* v___y_2059_ = _args[17];
lean_object* v___y_2060_ = _args[18];
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0(v_dsimpMethods_2042_, v_dsimpConfig_2043_, v_simpMethods_2044_, v_simpConfig_2045_, v_as_2046_, v_start_2047_, v_stop_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v_stop_2048_);
lean_dec(v_start_2047_);
lean_dec_ref(v_as_2046_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__1(lean_object* v_quantifiedFacts_2062_, lean_object* v_dsimpMethods_2063_, lean_object* v_dsimpConfig_2064_, lean_object* v_simpMethods_2065_, lean_object* v_simpConfig_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = lean_array_get_size(v_quantifiedFacts_2062_);
v___x_2081_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__0(v_dsimpMethods_2063_, v_dsimpConfig_2064_, v_simpMethods_2065_, v_simpConfig_2066_, v_quantifiedFacts_2062_, v___x_2079_, v___x_2080_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__1___boxed(lean_object** _args){
lean_object* v_quantifiedFacts_2082_ = _args[0];
lean_object* v_dsimpMethods_2083_ = _args[1];
lean_object* v_dsimpConfig_2084_ = _args[2];
lean_object* v_simpMethods_2085_ = _args[3];
lean_object* v_simpConfig_2086_ = _args[4];
lean_object* v___y_2087_ = _args[5];
lean_object* v___y_2088_ = _args[6];
lean_object* v___y_2089_ = _args[7];
lean_object* v___y_2090_ = _args[8];
lean_object* v___y_2091_ = _args[9];
lean_object* v___y_2092_ = _args[10];
lean_object* v___y_2093_ = _args[11];
lean_object* v___y_2094_ = _args[12];
lean_object* v___y_2095_ = _args[13];
lean_object* v___y_2096_ = _args[14];
lean_object* v___y_2097_ = _args[15];
lean_object* v___y_2098_ = _args[16];
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__1(v_quantifiedFacts_2082_, v_dsimpMethods_2083_, v_dsimpConfig_2084_, v_simpMethods_2085_, v_simpConfig_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_quantifiedFacts_2082_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg(lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
v_a_2102_ = lean_ctor_get(v_x_2100_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_x_2100_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v_x_2100_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v_x_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 1);
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
v_a_2110_ = lean_ctor_get(v_x_2100_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_x_2100_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v_x_2100_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v_x_2100_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 0);
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg___boxed(lean_object* v_x_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg(v_x_2118_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7(lean_object* v_opts_2121_, lean_object* v_opt_2122_){
_start:
{
lean_object* v_name_2123_; lean_object* v_defValue_2124_; lean_object* v_map_2125_; lean_object* v___x_2126_; 
v_name_2123_ = lean_ctor_get(v_opt_2122_, 0);
v_defValue_2124_ = lean_ctor_get(v_opt_2122_, 1);
v_map_2125_ = lean_ctor_get(v_opts_2121_, 0);
v___x_2126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2125_, v_name_2123_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_inc(v_defValue_2124_);
return v_defValue_2124_;
}
else
{
lean_object* v_val_2127_; 
v_val_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___x_2126_, 1);
if (lean_obj_tag(v_val_2127_) == 3)
{
lean_object* v_v_2128_; 
v_v_2128_ = lean_ctor_get(v_val_2127_, 0);
lean_inc(v_v_2128_);
lean_dec_ref_known(v_val_2127_, 1);
return v_v_2128_;
}
else
{
lean_dec(v_val_2127_);
lean_inc(v_defValue_2124_);
return v_defValue_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7___boxed(lean_object* v_opts_2129_, lean_object* v_opt_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7(v_opts_2129_, v_opt_2130_);
lean_dec_ref(v_opt_2130_);
lean_dec_ref(v_opts_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__6(lean_object* v_e_2132_){
_start:
{
if (lean_obj_tag(v_e_2132_) == 0)
{
uint8_t v___x_2133_; 
v___x_2133_ = 2;
return v___x_2133_;
}
else
{
uint8_t v___x_2134_; 
v___x_2134_ = 0;
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__6___boxed(lean_object* v_e_2135_){
_start:
{
uint8_t v_res_2136_; lean_object* v_r_2137_; 
v_res_2136_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__6(v_e_2135_);
lean_dec_ref(v_e_2135_);
v_r_2137_ = lean_box(v_res_2136_);
return v_r_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4_spec__5(size_t v_sz_2138_, size_t v_i_2139_, lean_object* v_bs_2140_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_usize_dec_lt(v_i_2139_, v_sz_2138_);
if (v___x_2141_ == 0)
{
return v_bs_2140_;
}
else
{
lean_object* v_v_2142_; lean_object* v_msg_2143_; lean_object* v___x_2144_; lean_object* v_bs_x27_2145_; size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v_v_2142_ = lean_array_uget_borrowed(v_bs_2140_, v_i_2139_);
v_msg_2143_ = lean_ctor_get(v_v_2142_, 1);
lean_inc_ref(v_msg_2143_);
v___x_2144_ = lean_unsigned_to_nat(0u);
v_bs_x27_2145_ = lean_array_uset(v_bs_2140_, v_i_2139_, v___x_2144_);
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_i_2139_, v___x_2146_);
v___x_2148_ = lean_array_uset(v_bs_x27_2145_, v_i_2139_, v_msg_2143_);
v_i_2139_ = v___x_2147_;
v_bs_2140_ = v___x_2148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2150_, lean_object* v_i_2151_, lean_object* v_bs_2152_){
_start:
{
size_t v_sz_boxed_2153_; size_t v_i_boxed_2154_; lean_object* v_res_2155_; 
v_sz_boxed_2153_ = lean_unbox_usize(v_sz_2150_);
lean_dec(v_sz_2150_);
v_i_boxed_2154_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4_spec__5(v_sz_boxed_2153_, v_i_boxed_2154_, v_bs_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___redArg(lean_object* v_oldTraces_2156_, lean_object* v_data_2157_, lean_object* v_ref_2158_, lean_object* v_msg_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_toCold_2165_; lean_object* v_currRecDepth_2166_; lean_object* v_ref_2167_; uint16_t v_optionFlags_2168_; uint8_t v_suppressElabErrors_2169_; uint8_t v_checkDeprecated_2170_; uint8_t v_isRecordingDeps_2171_; lean_object* v_ref_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v_traceState_2175_; lean_object* v_traces_2176_; lean_object* v___x_2177_; size_t v_sz_2178_; size_t v___x_2179_; lean_object* v___x_2180_; lean_object* v_msg_2181_; lean_object* v___x_2182_; lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2221_; 
v_toCold_2165_ = lean_ctor_get(v___y_2162_, 0);
v_currRecDepth_2166_ = lean_ctor_get(v___y_2162_, 1);
v_ref_2167_ = lean_ctor_get(v___y_2162_, 2);
v_optionFlags_2168_ = lean_ctor_get_uint16(v___y_2162_, sizeof(void*)*3);
v_suppressElabErrors_2169_ = lean_ctor_get_uint8(v___y_2162_, sizeof(void*)*3 + 2);
v_checkDeprecated_2170_ = lean_ctor_get_uint8(v___y_2162_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2171_ = lean_ctor_get_uint8(v___y_2162_, sizeof(void*)*3 + 4);
v_ref_2172_ = l_Lean_replaceRef(v_ref_2158_, v_ref_2167_);
lean_inc(v_currRecDepth_2166_);
lean_inc_ref(v_toCold_2165_);
v___x_2173_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2173_, 0, v_toCold_2165_);
lean_ctor_set(v___x_2173_, 1, v_currRecDepth_2166_);
lean_ctor_set(v___x_2173_, 2, v_ref_2172_);
lean_ctor_set_uint16(v___x_2173_, sizeof(void*)*3, v_optionFlags_2168_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*3 + 2, v_suppressElabErrors_2169_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*3 + 3, v_checkDeprecated_2170_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*3 + 4, v_isRecordingDeps_2171_);
v___x_2174_ = lean_st_ref_get(v___y_2163_);
v_traceState_2175_ = lean_ctor_get(v___x_2174_, 4);
lean_inc_ref(v_traceState_2175_);
lean_dec(v___x_2174_);
v_traces_2176_ = lean_ctor_get(v_traceState_2175_, 0);
lean_inc_ref(v_traces_2176_);
lean_dec_ref(v_traceState_2175_);
v___x_2177_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2176_);
lean_dec_ref(v_traces_2176_);
v_sz_2178_ = lean_array_size(v___x_2177_);
v___x_2179_ = ((size_t)0ULL);
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4_spec__5(v_sz_2178_, v___x_2179_, v___x_2177_);
v_msg_2181_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2181_, 0, v_data_2157_);
lean_ctor_set(v_msg_2181_, 1, v_msg_2159_);
lean_ctor_set(v_msg_2181_, 2, v___x_2180_);
v___x_2182_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3_spec__3(v_msg_2181_, v___y_2160_, v___y_2161_, v___x_2173_, v___y_2163_);
lean_dec_ref_known(v___x_2173_, 3);
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2221_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2221_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v_traceState_2188_; lean_object* v_env_2189_; lean_object* v_nextMacroScope_2190_; lean_object* v_ngen_2191_; lean_object* v_auxDeclNGen_2192_; lean_object* v_cache_2193_; lean_object* v_recordedDeps_2194_; lean_object* v_messages_2195_; lean_object* v_infoState_2196_; lean_object* v_snapshotTasks_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2220_; 
v___x_2187_ = lean_st_ref_take(v___y_2163_);
v_traceState_2188_ = lean_ctor_get(v___x_2187_, 4);
v_env_2189_ = lean_ctor_get(v___x_2187_, 0);
v_nextMacroScope_2190_ = lean_ctor_get(v___x_2187_, 1);
v_ngen_2191_ = lean_ctor_get(v___x_2187_, 2);
v_auxDeclNGen_2192_ = lean_ctor_get(v___x_2187_, 3);
v_cache_2193_ = lean_ctor_get(v___x_2187_, 5);
v_recordedDeps_2194_ = lean_ctor_get(v___x_2187_, 6);
v_messages_2195_ = lean_ctor_get(v___x_2187_, 7);
v_infoState_2196_ = lean_ctor_get(v___x_2187_, 8);
v_snapshotTasks_2197_ = lean_ctor_get(v___x_2187_, 9);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2199_ = v___x_2187_;
v_isShared_2200_ = v_isSharedCheck_2220_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_snapshotTasks_2197_);
lean_inc(v_infoState_2196_);
lean_inc(v_messages_2195_);
lean_inc(v_recordedDeps_2194_);
lean_inc(v_cache_2193_);
lean_inc(v_traceState_2188_);
lean_inc(v_auxDeclNGen_2192_);
lean_inc(v_ngen_2191_);
lean_inc(v_nextMacroScope_2190_);
lean_inc(v_env_2189_);
lean_dec(v___x_2187_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2220_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
uint64_t v_tid_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2218_; 
v_tid_2201_ = lean_ctor_get_uint64(v_traceState_2188_, sizeof(void*)*1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_traceState_2188_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; 
v_unused_2219_ = lean_ctor_get(v_traceState_2188_, 0);
lean_dec(v_unused_2219_);
v___x_2203_ = v_traceState_2188_;
v_isShared_2204_ = v_isSharedCheck_2218_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v_traceState_2188_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2218_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2205_ = lean_box(0);
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_ref_2158_);
lean_ctor_set(v___x_2206_, 1, v_a_2183_);
v___x_2207_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2156_, v___x_2206_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2207_);
v___x_2209_ = v___x_2203_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2207_);
lean_ctor_set_uint64(v_reuseFailAlloc_2217_, sizeof(void*)*1, v_tid_2201_);
v___x_2209_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2211_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 4, v___x_2209_);
v___x_2211_ = v___x_2199_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_env_2189_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_nextMacroScope_2190_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_ngen_2191_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_auxDeclNGen_2192_);
lean_ctor_set(v_reuseFailAlloc_2216_, 4, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2216_, 5, v_cache_2193_);
lean_ctor_set(v_reuseFailAlloc_2216_, 6, v_recordedDeps_2194_);
lean_ctor_set(v_reuseFailAlloc_2216_, 7, v_messages_2195_);
lean_ctor_set(v_reuseFailAlloc_2216_, 8, v_infoState_2196_);
lean_ctor_set(v_reuseFailAlloc_2216_, 9, v_snapshotTasks_2197_);
v___x_2211_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_st_ref_put(v___y_2163_, v___x_2211_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2205_);
v___x_2214_ = v___x_2185_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2205_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_2222_, lean_object* v_data_2223_, lean_object* v_ref_2224_, lean_object* v_msg_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___redArg(v_oldTraces_2222_, v_data_2223_, v_ref_2224_, v_msg_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2231_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__0));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2235_; double v___x_2236_; 
v___x_2235_ = lean_unsigned_to_nat(1000u);
v___x_2236_ = lean_float_of_nat(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3(lean_object* v_cls_2237_, uint8_t v_collapsed_2238_, lean_object* v_tag_2239_, lean_object* v_opts_2240_, uint8_t v_clsEnabled_2241_, lean_object* v_oldTraces_2242_, lean_object* v_msg_2243_, lean_object* v_resStartStop_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_fst_2257_; lean_object* v_snd_2258_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v_data_2262_; lean_object* v_fst_2265_; lean_object* v_snd_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; lean_object* v___y_2270_; lean_object* v_a_2271_; uint8_t v___y_2286_; double v___y_2318_; 
v_fst_2257_ = lean_ctor_get(v_resStartStop_2244_, 0);
lean_inc(v_fst_2257_);
v_snd_2258_ = lean_ctor_get(v_resStartStop_2244_, 1);
lean_inc(v_snd_2258_);
lean_dec_ref(v_resStartStop_2244_);
v_fst_2265_ = lean_ctor_get(v_snd_2258_, 0);
lean_inc(v_fst_2265_);
v_snd_2266_ = lean_ctor_get(v_snd_2258_, 1);
lean_inc(v_snd_2266_);
lean_dec(v_snd_2258_);
v___x_2267_ = l_Lean_trace_profiler;
v___x_2268_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_opts_2240_, v___x_2267_);
if (v___x_2268_ == 0)
{
v___y_2286_ = v___x_2268_;
goto v___jp_2285_;
}
else
{
lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2324_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_opts_2240_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; double v___x_2327_; double v___x_2328_; double v___x_2329_; 
v___x_2325_ = l_Lean_trace_profiler_threshold;
v___x_2326_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7(v_opts_2240_, v___x_2325_);
v___x_2327_ = lean_float_of_nat(v___x_2326_);
v___x_2328_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2);
v___x_2329_ = lean_float_div(v___x_2327_, v___x_2328_);
v___y_2318_ = v___x_2329_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; double v___x_2332_; 
v___x_2330_ = l_Lean_trace_profiler_threshold;
v___x_2331_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7(v_opts_2240_, v___x_2330_);
v___x_2332_ = lean_float_of_nat(v___x_2331_);
v___y_2318_ = v___x_2332_;
goto v___jp_2317_;
}
}
v___jp_2259_:
{
lean_object* v___x_2263_; 
lean_inc(v___y_2261_);
v___x_2263_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___redArg(v_oldTraces_2242_, v_data_2262_, v___y_2261_, v___y_2260_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v___x_2264_; 
lean_dec_ref_known(v___x_2263_, 1);
v___x_2264_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg(v_fst_2257_);
return v___x_2264_;
}
else
{
lean_dec(v_fst_2257_);
return v___x_2263_;
}
}
v___jp_2269_:
{
uint8_t v_result_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; double v___x_2275_; lean_object* v_data_2276_; 
v_result_2272_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__6(v_fst_2257_);
v___x_2273_ = lean_box(v_result_2272_);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
v___x_2275_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_2239_);
lean_inc_ref(v___x_2274_);
lean_inc(v_cls_2237_);
v_data_2276_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2276_, 0, v_cls_2237_);
lean_ctor_set(v_data_2276_, 1, v___x_2274_);
lean_ctor_set(v_data_2276_, 2, v_tag_2239_);
lean_ctor_set_float(v_data_2276_, sizeof(void*)*3, v___x_2275_);
lean_ctor_set_float(v_data_2276_, sizeof(void*)*3 + 8, v___x_2275_);
lean_ctor_set_uint8(v_data_2276_, sizeof(void*)*3 + 16, v_collapsed_2238_);
if (v___x_2268_ == 0)
{
lean_dec_ref_known(v___x_2274_, 1);
lean_dec(v_snd_2266_);
lean_dec(v_fst_2265_);
lean_dec_ref(v_tag_2239_);
lean_dec(v_cls_2237_);
v___y_2260_ = v_a_2271_;
v___y_2261_ = v___y_2270_;
v_data_2262_ = v_data_2276_;
goto v___jp_2259_;
}
else
{
lean_object* v_data_2277_; double v___x_2278_; double v___x_2279_; 
lean_dec_ref_known(v_data_2276_, 3);
v_data_2277_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2277_, 0, v_cls_2237_);
lean_ctor_set(v_data_2277_, 1, v___x_2274_);
lean_ctor_set(v_data_2277_, 2, v_tag_2239_);
v___x_2278_ = lean_unbox_float(v_fst_2265_);
lean_dec(v_fst_2265_);
lean_ctor_set_float(v_data_2277_, sizeof(void*)*3, v___x_2278_);
v___x_2279_ = lean_unbox_float(v_snd_2266_);
lean_dec(v_snd_2266_);
lean_ctor_set_float(v_data_2277_, sizeof(void*)*3 + 8, v___x_2279_);
lean_ctor_set_uint8(v_data_2277_, sizeof(void*)*3 + 16, v_collapsed_2238_);
v___y_2260_ = v_a_2271_;
v___y_2261_ = v___y_2270_;
v_data_2262_ = v_data_2277_;
goto v___jp_2259_;
}
}
v___jp_2280_:
{
lean_object* v_ref_2281_; lean_object* v___x_2282_; 
v_ref_2281_ = lean_ctor_get(v___y_2254_, 2);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v___y_2248_);
lean_inc(v___y_2247_);
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2245_);
lean_inc(v_fst_2257_);
v___x_2282_ = lean_apply_13(v_msg_2243_, v_fst_2257_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, lean_box(0));
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___y_2270_ = v_ref_2281_;
v_a_2271_ = v_a_2283_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2284_; 
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1);
v___y_2270_ = v_ref_2281_;
v_a_2271_ = v___x_2284_;
goto v___jp_2269_;
}
}
v___jp_2285_:
{
if (v_clsEnabled_2241_ == 0)
{
if (v___y_2286_ == 0)
{
lean_object* v___x_2287_; lean_object* v_traceState_2288_; lean_object* v_env_2289_; lean_object* v_nextMacroScope_2290_; lean_object* v_ngen_2291_; lean_object* v_auxDeclNGen_2292_; lean_object* v_cache_2293_; lean_object* v_recordedDeps_2294_; lean_object* v_messages_2295_; lean_object* v_infoState_2296_; lean_object* v_snapshotTasks_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_snd_2266_);
lean_dec(v_fst_2265_);
lean_dec_ref(v_msg_2243_);
lean_dec_ref(v_tag_2239_);
lean_dec(v_cls_2237_);
v___x_2287_ = lean_st_ref_take(v___y_2255_);
v_traceState_2288_ = lean_ctor_get(v___x_2287_, 4);
v_env_2289_ = lean_ctor_get(v___x_2287_, 0);
v_nextMacroScope_2290_ = lean_ctor_get(v___x_2287_, 1);
v_ngen_2291_ = lean_ctor_get(v___x_2287_, 2);
v_auxDeclNGen_2292_ = lean_ctor_get(v___x_2287_, 3);
v_cache_2293_ = lean_ctor_get(v___x_2287_, 5);
v_recordedDeps_2294_ = lean_ctor_get(v___x_2287_, 6);
v_messages_2295_ = lean_ctor_get(v___x_2287_, 7);
v_infoState_2296_ = lean_ctor_get(v___x_2287_, 8);
v_snapshotTasks_2297_ = lean_ctor_get(v___x_2287_, 9);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2299_ = v___x_2287_;
v_isShared_2300_ = v_isSharedCheck_2316_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_snapshotTasks_2297_);
lean_inc(v_infoState_2296_);
lean_inc(v_messages_2295_);
lean_inc(v_recordedDeps_2294_);
lean_inc(v_cache_2293_);
lean_inc(v_traceState_2288_);
lean_inc(v_auxDeclNGen_2292_);
lean_inc(v_ngen_2291_);
lean_inc(v_nextMacroScope_2290_);
lean_inc(v_env_2289_);
lean_dec(v___x_2287_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2316_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
uint64_t v_tid_2301_; lean_object* v_traces_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2315_; 
v_tid_2301_ = lean_ctor_get_uint64(v_traceState_2288_, sizeof(void*)*1);
v_traces_2302_ = lean_ctor_get(v_traceState_2288_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_traceState_2288_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2304_ = v_traceState_2288_;
v_isShared_2305_ = v_isSharedCheck_2315_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_traces_2302_);
lean_dec(v_traceState_2288_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2315_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2242_, v_traces_2302_);
lean_dec_ref(v_traces_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2306_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2306_);
lean_ctor_set_uint64(v_reuseFailAlloc_2314_, sizeof(void*)*1, v_tid_2301_);
v___x_2308_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 4, v___x_2308_);
v___x_2310_ = v___x_2299_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_env_2289_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_nextMacroScope_2290_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v_ngen_2291_);
lean_ctor_set(v_reuseFailAlloc_2313_, 3, v_auxDeclNGen_2292_);
lean_ctor_set(v_reuseFailAlloc_2313_, 4, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2313_, 5, v_cache_2293_);
lean_ctor_set(v_reuseFailAlloc_2313_, 6, v_recordedDeps_2294_);
lean_ctor_set(v_reuseFailAlloc_2313_, 7, v_messages_2295_);
lean_ctor_set(v_reuseFailAlloc_2313_, 8, v_infoState_2296_);
lean_ctor_set(v_reuseFailAlloc_2313_, 9, v_snapshotTasks_2297_);
v___x_2310_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_st_ref_put(v___y_2255_, v___x_2310_);
v___x_2312_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg(v_fst_2257_);
return v___x_2312_;
}
}
}
}
}
else
{
goto v___jp_2280_;
}
}
else
{
goto v___jp_2280_;
}
}
v___jp_2317_:
{
double v___x_2319_; double v___x_2320_; double v___x_2321_; uint8_t v___x_2322_; 
v___x_2319_ = lean_unbox_float(v_snd_2266_);
v___x_2320_ = lean_unbox_float(v_fst_2265_);
v___x_2321_ = lean_float_sub(v___x_2319_, v___x_2320_);
v___x_2322_ = lean_float_decLt(v___y_2318_, v___x_2321_);
v___y_2286_ = v___x_2322_;
goto v___jp_2285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2333_ = _args[0];
lean_object* v_collapsed_2334_ = _args[1];
lean_object* v_tag_2335_ = _args[2];
lean_object* v_opts_2336_ = _args[3];
lean_object* v_clsEnabled_2337_ = _args[4];
lean_object* v_oldTraces_2338_ = _args[5];
lean_object* v_msg_2339_ = _args[6];
lean_object* v_resStartStop_2340_ = _args[7];
lean_object* v___y_2341_ = _args[8];
lean_object* v___y_2342_ = _args[9];
lean_object* v___y_2343_ = _args[10];
lean_object* v___y_2344_ = _args[11];
lean_object* v___y_2345_ = _args[12];
lean_object* v___y_2346_ = _args[13];
lean_object* v___y_2347_ = _args[14];
lean_object* v___y_2348_ = _args[15];
lean_object* v___y_2349_ = _args[16];
lean_object* v___y_2350_ = _args[17];
lean_object* v___y_2351_ = _args[18];
lean_object* v___y_2352_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_2353_; uint8_t v_clsEnabled_boxed_2354_; lean_object* v_res_2355_; 
v_collapsed_boxed_2353_ = lean_unbox(v_collapsed_2334_);
v_clsEnabled_boxed_2354_ = lean_unbox(v_clsEnabled_2337_);
v_res_2355_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3(v_cls_2333_, v_collapsed_boxed_2353_, v_tag_2335_, v_opts_2336_, v_clsEnabled_boxed_2354_, v_oldTraces_2338_, v_msg_2339_, v_resStartStop_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_opts_2336_);
return v_res_2355_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1(void){
_start:
{
lean_object* v___x_2357_; double v___x_2358_; 
v___x_2357_ = lean_unsigned_to_nat(1000000000u);
v___x_2358_ = lean_float_of_nat(v___x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers(lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v___f_2373_; lean_object* v___x_2374_; lean_object* v_eprBvProblem_2375_; lean_object* v_sortInfo_2376_; lean_object* v_sortMap_2377_; lean_object* v_predInfo_2378_; lean_object* v_groundFacts_2379_; lean_object* v_quantifiedFacts_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2531_; 
v___f_2373_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__0));
v___x_2374_ = lean_st_ref_get(v_a_2362_);
v_eprBvProblem_2375_ = lean_ctor_get(v___x_2374_, 4);
lean_inc_ref(v_eprBvProblem_2375_);
lean_dec(v___x_2374_);
v_sortInfo_2376_ = lean_ctor_get(v_eprBvProblem_2375_, 0);
v_sortMap_2377_ = lean_ctor_get(v_eprBvProblem_2375_, 1);
v_predInfo_2378_ = lean_ctor_get(v_eprBvProblem_2375_, 2);
v_groundFacts_2379_ = lean_ctor_get(v_eprBvProblem_2375_, 3);
v_quantifiedFacts_2380_ = lean_ctor_get(v_eprBvProblem_2375_, 4);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_eprBvProblem_2375_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2382_ = v_eprBvProblem_2375_;
v_isShared_2383_ = v_isSharedCheck_2531_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_quantifiedFacts_2380_);
lean_inc(v_groundFacts_2379_);
lean_inc(v_predInfo_2378_);
lean_inc(v_sortMap_2377_);
lean_inc(v_sortInfo_2376_);
lean_dec(v_eprBvProblem_2375_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2531_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_facts_2385_; lean_object* v___y_2386_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2407_ = lean_array_get_size(v_quantifiedFacts_2380_);
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = lean_nat_dec_eq(v___x_2407_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v_toCold_2410_; lean_object* v_options_2411_; lean_object* v_inheritedTraceOptions_2412_; uint8_t v_hasTrace_2413_; lean_object* v___f_2414_; 
v_toCold_2410_ = lean_ctor_get(v_a_2370_, 0);
v_options_2411_ = lean_ctor_get(v_toCold_2410_, 2);
v_inheritedTraceOptions_2412_ = lean_ctor_get(v_toCold_2410_, 11);
v_hasTrace_2413_ = lean_ctor_get_uint8(v_options_2411_, sizeof(void*)*1);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___lam__1___boxed), 17, 1);
lean_closure_set(v___f_2414_, 0, v_quantifiedFacts_2380_);
if (v_hasTrace_2413_ == 0)
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(v___f_2414_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v_facts_2385_ = v_a_2416_;
v___y_2386_ = v_a_2362_;
goto v___jp_2384_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_del_object(v___x_2382_);
lean_dec_ref(v_groundFacts_2379_);
lean_dec_ref(v_predInfo_2378_);
lean_dec_ref(v_sortMap_2377_);
lean_dec_ref(v_sortInfo_2376_);
v_a_2417_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2415_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2415_);
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
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v_a_2432_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v_a_2447_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__4));
v___x_2426_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_2427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__7);
v___x_2428_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2412_, v_options_2411_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = l_Lean_trace_profiler;
v___x_2518_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_2411_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(v___f_2414_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v_facts_2385_ = v_a_2520_;
v___y_2386_ = v_a_2362_;
goto v___jp_2384_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_del_object(v___x_2382_);
lean_dec_ref(v_groundFacts_2379_);
lean_dec_ref(v_predInfo_2378_);
lean_dec_ref(v_sortMap_2377_);
lean_dec_ref(v_sortInfo_2376_);
v_a_2521_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2519_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2519_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
else
{
lean_del_object(v___x_2382_);
goto v___jp_2456_;
}
}
else
{
lean_del_object(v___x_2382_);
goto v___jp_2456_;
}
v___jp_2429_:
{
lean_object* v___x_2433_; double v___x_2434_; double v___x_2435_; double v___x_2436_; double v___x_2437_; double v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2433_ = lean_io_mono_nanos_now();
v___x_2434_ = lean_float_of_nat(v___y_2431_);
v___x_2435_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_2436_ = lean_float_div(v___x_2434_, v___x_2435_);
v___x_2437_ = lean_float_of_nat(v___x_2433_);
v___x_2438_ = lean_float_div(v___x_2437_, v___x_2435_);
v___x_2439_ = lean_box_float(v___x_2436_);
v___x_2440_ = lean_box_float(v___x_2438_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_a_2432_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3(v___x_2425_, v_hasTrace_2413_, v___x_2426_, v_options_2411_, v___x_2428_, v___y_2430_, v___f_2373_, v___x_2442_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2443_;
}
v___jp_2444_:
{
lean_object* v___x_2448_; double v___x_2449_; double v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2448_ = lean_io_get_num_heartbeats();
v___x_2449_ = lean_float_of_nat(v___y_2445_);
v___x_2450_ = lean_float_of_nat(v___x_2448_);
v___x_2451_ = lean_box_float(v___x_2449_);
v___x_2452_ = lean_box_float(v___x_2450_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_a_2447_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3(v___x_2425_, v_hasTrace_2413_, v___x_2426_, v_options_2411_, v___x_2428_, v___y_2446_, v___f_2373_, v___x_2454_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2455_;
}
v___jp_2456_:
{
lean_object* v___x_2457_; lean_object* v_a_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2457_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v_a_2371_);
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2460_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_2411_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_io_mono_nanos_now();
v___x_2462_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(v___f_2414_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; lean_object* v_caches_2465_; lean_object* v_typeAnalysis_2466_; lean_object* v_target_2467_; lean_object* v_hypotheses_2468_; uint8_t v_didChange_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2479_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = lean_st_ref_take(v_a_2362_);
v_caches_2465_ = lean_ctor_get(v___x_2464_, 0);
v_typeAnalysis_2466_ = lean_ctor_get(v___x_2464_, 1);
v_target_2467_ = lean_ctor_get(v___x_2464_, 2);
v_hypotheses_2468_ = lean_ctor_get(v___x_2464_, 3);
v_didChange_2469_ = lean_ctor_get_uint8(v___x_2464_, sizeof(void*)*5);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2464_, 4);
lean_dec(v_unused_2480_);
v___x_2471_ = v___x_2464_;
v_isShared_2472_ = v_isSharedCheck_2479_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_hypotheses_2468_);
lean_inc(v_target_2467_);
lean_inc(v_typeAnalysis_2466_);
lean_inc(v_caches_2465_);
lean_dec(v___x_2464_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2479_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2473_, 0, v_sortInfo_2376_);
lean_ctor_set(v___x_2473_, 1, v_sortMap_2377_);
lean_ctor_set(v___x_2473_, 2, v_predInfo_2378_);
lean_ctor_set(v___x_2473_, 3, v_groundFacts_2379_);
lean_ctor_set(v___x_2473_, 4, v_a_2463_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 4, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_caches_2465_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_typeAnalysis_2466_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_target_2467_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_hypotheses_2468_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v___x_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2478_, sizeof(void*)*5, v_didChange_2469_);
v___x_2475_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_st_ref_put(v_a_2362_, v___x_2475_);
v___x_2477_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__2));
v___y_2430_ = v_a_2458_;
v___y_2431_ = v___x_2461_;
v_a_2432_ = v___x_2477_;
goto v___jp_2429_;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v_groundFacts_2379_);
lean_dec_ref(v_predInfo_2378_);
lean_dec_ref(v_sortMap_2377_);
lean_dec_ref(v_sortInfo_2376_);
v_a_2481_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2462_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2462_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 0);
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
v___y_2430_ = v_a_2458_;
v___y_2431_ = v___x_2461_;
v_a_2432_ = v___x_2486_;
goto v___jp_2429_;
}
}
}
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_io_get_num_heartbeats();
v___x_2490_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(v___f_2414_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2492_; lean_object* v_caches_2493_; lean_object* v_typeAnalysis_2494_; lean_object* v_target_2495_; lean_object* v_hypotheses_2496_; uint8_t v_didChange_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2507_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2490_, 1);
v___x_2492_ = lean_st_ref_take(v_a_2362_);
v_caches_2493_ = lean_ctor_get(v___x_2492_, 0);
v_typeAnalysis_2494_ = lean_ctor_get(v___x_2492_, 1);
v_target_2495_ = lean_ctor_get(v___x_2492_, 2);
v_hypotheses_2496_ = lean_ctor_get(v___x_2492_, 3);
v_didChange_2497_ = lean_ctor_get_uint8(v___x_2492_, sizeof(void*)*5);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v___x_2492_, 4);
lean_dec(v_unused_2508_);
v___x_2499_ = v___x_2492_;
v_isShared_2500_ = v_isSharedCheck_2507_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_hypotheses_2496_);
lean_inc(v_target_2495_);
lean_inc(v_typeAnalysis_2494_);
lean_inc(v_caches_2493_);
lean_dec(v___x_2492_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2507_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2501_, 0, v_sortInfo_2376_);
lean_ctor_set(v___x_2501_, 1, v_sortMap_2377_);
lean_ctor_set(v___x_2501_, 2, v_predInfo_2378_);
lean_ctor_set(v___x_2501_, 3, v_groundFacts_2379_);
lean_ctor_set(v___x_2501_, 4, v_a_2491_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 4, v___x_2501_);
v___x_2503_ = v___x_2499_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_caches_2493_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_typeAnalysis_2494_);
lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_target_2495_);
lean_ctor_set(v_reuseFailAlloc_2506_, 3, v_hypotheses_2496_);
lean_ctor_set(v_reuseFailAlloc_2506_, 4, v___x_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, sizeof(void*)*5, v_didChange_2497_);
v___x_2503_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_st_ref_put(v_a_2362_, v___x_2503_);
v___x_2505_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__2));
v___y_2445_ = v___x_2489_;
v___y_2446_ = v_a_2458_;
v_a_2447_ = v___x_2505_;
goto v___jp_2444_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v_groundFacts_2379_);
lean_dec_ref(v_predInfo_2378_);
lean_dec_ref(v_sortMap_2377_);
lean_dec_ref(v_sortInfo_2376_);
v_a_2509_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2490_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2490_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 0);
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
v___y_2445_ = v___x_2489_;
v___y_2446_ = v_a_2458_;
v_a_2447_ = v___x_2514_;
goto v___jp_2444_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_del_object(v___x_2382_);
lean_dec_ref(v_quantifiedFacts_2380_);
lean_dec_ref(v_groundFacts_2379_);
lean_dec_ref(v_predInfo_2378_);
lean_dec_ref(v_sortMap_2377_);
lean_dec_ref(v_sortInfo_2376_);
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
return v___x_2530_;
}
v___jp_2384_:
{
lean_object* v___x_2387_; lean_object* v_caches_2388_; lean_object* v_typeAnalysis_2389_; lean_object* v_target_2390_; lean_object* v_hypotheses_2391_; uint8_t v_didChange_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2405_; 
v___x_2387_ = lean_st_ref_take(v___y_2386_);
v_caches_2388_ = lean_ctor_get(v___x_2387_, 0);
v_typeAnalysis_2389_ = lean_ctor_get(v___x_2387_, 1);
v_target_2390_ = lean_ctor_get(v___x_2387_, 2);
v_hypotheses_2391_ = lean_ctor_get(v___x_2387_, 3);
v_didChange_2392_ = lean_ctor_get_uint8(v___x_2387_, sizeof(void*)*5);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v___x_2387_, 4);
lean_dec(v_unused_2406_);
v___x_2394_ = v___x_2387_;
v_isShared_2395_ = v_isSharedCheck_2405_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_hypotheses_2391_);
lean_inc(v_target_2390_);
lean_inc(v_typeAnalysis_2389_);
lean_inc(v_caches_2388_);
lean_dec(v___x_2387_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2405_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2396_ = lean_box(0);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v_facts_2385_);
v___x_2398_ = v___x_2382_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_sortInfo_2376_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_sortMap_2377_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_predInfo_2378_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_groundFacts_2379_);
lean_ctor_set(v_reuseFailAlloc_2404_, 4, v_facts_2385_);
v___x_2398_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 4, v___x_2398_);
v___x_2400_ = v___x_2394_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_caches_2388_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_typeAnalysis_2389_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_target_2390_);
lean_ctor_set(v_reuseFailAlloc_2403_, 3, v_hypotheses_2391_);
lean_ctor_set(v_reuseFailAlloc_2403_, 4, v___x_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2403_, sizeof(void*)*5, v_didChange_2392_);
v___x_2400_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_st_ref_put(v___y_2386_, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2396_);
return v___x_2402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___boxed(lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers(v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5(lean_object* v_00_u03b1_2545_, lean_object* v_x_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg(v_x_2546_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2560_, lean_object* v_x_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5(v_00_u03b1_2560_, v_x_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4(lean_object* v_oldTraces_2575_, lean_object* v_data_2576_, lean_object* v_ref_2577_, lean_object* v_msg_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___redArg(v_oldTraces_2575_, v_data_2576_, v_ref_2577_, v_msg_2578_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___boxed(lean_object* v_oldTraces_2592_, lean_object* v_data_2593_, lean_object* v_ref_2594_, lean_object* v_msg_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4(v_oldTraces_2592_, v_data_2593_, v_ref_2594_, v_msg_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2608_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__0));
v___x_2611_ = l_Lean_stringToMessageData(v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0(lean_object* v_name_2612_, lean_object* v_x_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2626_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1);
v___x_2627_ = l_Lean_MessageData_ofName(v_name_2612_);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed(lean_object* v_name_2630_, lean_object* v_x_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0(v_name_2630_, v_x_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec_ref(v_x_2631_);
return v_res_2644_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0_spec__0(lean_object* v_e_2645_){
_start:
{
if (lean_obj_tag(v_e_2645_) == 0)
{
uint8_t v___x_2646_; 
v___x_2646_ = 2;
return v___x_2646_;
}
else
{
lean_object* v_a_2647_; uint8_t v___x_2648_; 
v_a_2647_ = lean_ctor_get(v_e_2645_, 0);
v___x_2648_ = lean_unbox(v_a_2647_);
if (v___x_2648_ == 0)
{
uint8_t v___x_2649_; 
v___x_2649_ = 1;
return v___x_2649_;
}
else
{
uint8_t v___x_2650_; 
v___x_2650_ = 0;
return v___x_2650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0_spec__0___boxed(lean_object* v_e_2651_){
_start:
{
uint8_t v_res_2652_; lean_object* v_r_2653_; 
v_res_2652_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0_spec__0(v_e_2651_);
lean_dec_ref(v_e_2651_);
v_r_2653_ = lean_box(v_res_2652_);
return v_r_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(lean_object* v_cls_2654_, uint8_t v_collapsed_2655_, lean_object* v_tag_2656_, lean_object* v_opts_2657_, uint8_t v_clsEnabled_2658_, lean_object* v_oldTraces_2659_, lean_object* v_msg_2660_, lean_object* v_resStartStop_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_fst_2674_; lean_object* v_snd_2675_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v_data_2679_; lean_object* v_fst_2690_; lean_object* v_snd_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; lean_object* v___y_2695_; lean_object* v_a_2696_; uint8_t v___y_2711_; double v___y_2743_; 
v_fst_2674_ = lean_ctor_get(v_resStartStop_2661_, 0);
lean_inc(v_fst_2674_);
v_snd_2675_ = lean_ctor_get(v_resStartStop_2661_, 1);
lean_inc(v_snd_2675_);
lean_dec_ref(v_resStartStop_2661_);
v_fst_2690_ = lean_ctor_get(v_snd_2675_, 0);
lean_inc(v_fst_2690_);
v_snd_2691_ = lean_ctor_get(v_snd_2675_, 1);
lean_inc(v_snd_2691_);
lean_dec(v_snd_2675_);
v___x_2692_ = l_Lean_trace_profiler;
v___x_2693_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_opts_2657_, v___x_2692_);
if (v___x_2693_ == 0)
{
v___y_2711_ = v___x_2693_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2748_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2749_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_opts_2657_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; double v___x_2752_; double v___x_2753_; double v___x_2754_; 
v___x_2750_ = l_Lean_trace_profiler_threshold;
v___x_2751_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7(v_opts_2657_, v___x_2750_);
v___x_2752_ = lean_float_of_nat(v___x_2751_);
v___x_2753_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__2);
v___x_2754_ = lean_float_div(v___x_2752_, v___x_2753_);
v___y_2743_ = v___x_2754_;
goto v___jp_2742_;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; double v___x_2757_; 
v___x_2755_ = l_Lean_trace_profiler_threshold;
v___x_2756_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__7(v_opts_2657_, v___x_2755_);
v___x_2757_ = lean_float_of_nat(v___x_2756_);
v___y_2743_ = v___x_2757_;
goto v___jp_2742_;
}
}
v___jp_2676_:
{
lean_object* v___x_2680_; 
lean_inc(v___y_2677_);
v___x_2680_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__4___redArg(v_oldTraces_2659_, v_data_2679_, v___y_2677_, v___y_2678_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2681_; 
lean_dec_ref_known(v___x_2680_, 1);
v___x_2681_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg(v_fst_2674_);
return v___x_2681_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_fst_2674_);
v_a_2682_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2680_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2680_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
v___jp_2694_:
{
uint8_t v_result_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; double v___x_2700_; lean_object* v_data_2701_; 
v_result_2697_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0_spec__0(v_fst_2674_);
v___x_2698_ = lean_box(v_result_2697_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
v___x_2700_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_2656_);
lean_inc_ref(v___x_2699_);
lean_inc(v_cls_2654_);
v_data_2701_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2701_, 0, v_cls_2654_);
lean_ctor_set(v_data_2701_, 1, v___x_2699_);
lean_ctor_set(v_data_2701_, 2, v_tag_2656_);
lean_ctor_set_float(v_data_2701_, sizeof(void*)*3, v___x_2700_);
lean_ctor_set_float(v_data_2701_, sizeof(void*)*3 + 8, v___x_2700_);
lean_ctor_set_uint8(v_data_2701_, sizeof(void*)*3 + 16, v_collapsed_2655_);
if (v___x_2693_ == 0)
{
lean_dec_ref_known(v___x_2699_, 1);
lean_dec(v_snd_2691_);
lean_dec(v_fst_2690_);
lean_dec_ref(v_tag_2656_);
lean_dec(v_cls_2654_);
v___y_2677_ = v___y_2695_;
v___y_2678_ = v_a_2696_;
v_data_2679_ = v_data_2701_;
goto v___jp_2676_;
}
else
{
lean_object* v_data_2702_; double v___x_2703_; double v___x_2704_; 
lean_dec_ref_known(v_data_2701_, 3);
v_data_2702_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2702_, 0, v_cls_2654_);
lean_ctor_set(v_data_2702_, 1, v___x_2699_);
lean_ctor_set(v_data_2702_, 2, v_tag_2656_);
v___x_2703_ = lean_unbox_float(v_fst_2690_);
lean_dec(v_fst_2690_);
lean_ctor_set_float(v_data_2702_, sizeof(void*)*3, v___x_2703_);
v___x_2704_ = lean_unbox_float(v_snd_2691_);
lean_dec(v_snd_2691_);
lean_ctor_set_float(v_data_2702_, sizeof(void*)*3 + 8, v___x_2704_);
lean_ctor_set_uint8(v_data_2702_, sizeof(void*)*3 + 16, v_collapsed_2655_);
v___y_2677_ = v___y_2695_;
v___y_2678_ = v_a_2696_;
v_data_2679_ = v_data_2702_;
goto v___jp_2676_;
}
}
v___jp_2705_:
{
lean_object* v_ref_2706_; lean_object* v___x_2707_; 
v_ref_2706_ = lean_ctor_get(v___y_2671_, 2);
lean_inc(v___y_2672_);
lean_inc_ref(v___y_2671_);
lean_inc(v___y_2670_);
lean_inc_ref(v___y_2669_);
lean_inc(v___y_2668_);
lean_inc_ref(v___y_2667_);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc(v___y_2663_);
lean_inc_ref(v___y_2662_);
lean_inc(v_fst_2674_);
v___x_2707_ = lean_apply_13(v_msg_2660_, v_fst_2674_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, lean_box(0));
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v___y_2695_ = v_ref_2706_;
v_a_2696_ = v_a_2708_;
goto v___jp_2694_;
}
else
{
lean_object* v___x_2709_; 
lean_dec_ref_known(v___x_2707_, 1);
v___x_2709_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3___closed__1);
v___y_2695_ = v_ref_2706_;
v_a_2696_ = v___x_2709_;
goto v___jp_2694_;
}
}
v___jp_2710_:
{
if (v_clsEnabled_2658_ == 0)
{
if (v___y_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v_traceState_2713_; lean_object* v_env_2714_; lean_object* v_nextMacroScope_2715_; lean_object* v_ngen_2716_; lean_object* v_auxDeclNGen_2717_; lean_object* v_cache_2718_; lean_object* v_recordedDeps_2719_; lean_object* v_messages_2720_; lean_object* v_infoState_2721_; lean_object* v_snapshotTasks_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_snd_2691_);
lean_dec(v_fst_2690_);
lean_dec_ref(v_msg_2660_);
lean_dec_ref(v_tag_2656_);
lean_dec(v_cls_2654_);
v___x_2712_ = lean_st_ref_take(v___y_2672_);
v_traceState_2713_ = lean_ctor_get(v___x_2712_, 4);
v_env_2714_ = lean_ctor_get(v___x_2712_, 0);
v_nextMacroScope_2715_ = lean_ctor_get(v___x_2712_, 1);
v_ngen_2716_ = lean_ctor_get(v___x_2712_, 2);
v_auxDeclNGen_2717_ = lean_ctor_get(v___x_2712_, 3);
v_cache_2718_ = lean_ctor_get(v___x_2712_, 5);
v_recordedDeps_2719_ = lean_ctor_get(v___x_2712_, 6);
v_messages_2720_ = lean_ctor_get(v___x_2712_, 7);
v_infoState_2721_ = lean_ctor_get(v___x_2712_, 8);
v_snapshotTasks_2722_ = lean_ctor_get(v___x_2712_, 9);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2724_ = v___x_2712_;
v_isShared_2725_ = v_isSharedCheck_2741_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_snapshotTasks_2722_);
lean_inc(v_infoState_2721_);
lean_inc(v_messages_2720_);
lean_inc(v_recordedDeps_2719_);
lean_inc(v_cache_2718_);
lean_inc(v_traceState_2713_);
lean_inc(v_auxDeclNGen_2717_);
lean_inc(v_ngen_2716_);
lean_inc(v_nextMacroScope_2715_);
lean_inc(v_env_2714_);
lean_dec(v___x_2712_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2741_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
uint64_t v_tid_2726_; lean_object* v_traces_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2740_; 
v_tid_2726_ = lean_ctor_get_uint64(v_traceState_2713_, sizeof(void*)*1);
v_traces_2727_ = lean_ctor_get(v_traceState_2713_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_traceState_2713_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2729_ = v_traceState_2713_;
v_isShared_2730_ = v_isSharedCheck_2740_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_traces_2727_);
lean_dec(v_traceState_2713_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2740_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2659_, v_traces_2727_);
lean_dec_ref(v_traces_2727_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2731_);
v___x_2733_ = v___x_2729_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2731_);
lean_ctor_set_uint64(v_reuseFailAlloc_2739_, sizeof(void*)*1, v_tid_2726_);
v___x_2733_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2735_; 
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 4, v___x_2733_);
v___x_2735_ = v___x_2724_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_env_2714_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_nextMacroScope_2715_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_ngen_2716_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v_auxDeclNGen_2717_);
lean_ctor_set(v_reuseFailAlloc_2738_, 4, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2738_, 5, v_cache_2718_);
lean_ctor_set(v_reuseFailAlloc_2738_, 6, v_recordedDeps_2719_);
lean_ctor_set(v_reuseFailAlloc_2738_, 7, v_messages_2720_);
lean_ctor_set(v_reuseFailAlloc_2738_, 8, v_infoState_2721_);
lean_ctor_set(v_reuseFailAlloc_2738_, 9, v_snapshotTasks_2722_);
v___x_2735_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_st_ref_put(v___y_2672_, v___x_2735_);
v___x_2737_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__3_spec__5___redArg(v_fst_2674_);
return v___x_2737_;
}
}
}
}
}
else
{
goto v___jp_2705_;
}
}
else
{
goto v___jp_2705_;
}
}
v___jp_2742_:
{
double v___x_2744_; double v___x_2745_; double v___x_2746_; uint8_t v___x_2747_; 
v___x_2744_ = lean_unbox_float(v_snd_2691_);
v___x_2745_ = lean_unbox_float(v_fst_2690_);
v___x_2746_ = lean_float_sub(v___x_2744_, v___x_2745_);
v___x_2747_ = lean_float_decLt(v___y_2743_, v___x_2746_);
v___y_2711_ = v___x_2747_;
goto v___jp_2710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___boxed(lean_object** _args){
lean_object* v_cls_2758_ = _args[0];
lean_object* v_collapsed_2759_ = _args[1];
lean_object* v_tag_2760_ = _args[2];
lean_object* v_opts_2761_ = _args[3];
lean_object* v_clsEnabled_2762_ = _args[4];
lean_object* v_oldTraces_2763_ = _args[5];
lean_object* v_msg_2764_ = _args[6];
lean_object* v_resStartStop_2765_ = _args[7];
lean_object* v___y_2766_ = _args[8];
lean_object* v___y_2767_ = _args[9];
lean_object* v___y_2768_ = _args[10];
lean_object* v___y_2769_ = _args[11];
lean_object* v___y_2770_ = _args[12];
lean_object* v___y_2771_ = _args[13];
lean_object* v___y_2772_ = _args[14];
lean_object* v___y_2773_ = _args[15];
lean_object* v___y_2774_ = _args[16];
lean_object* v___y_2775_ = _args[17];
lean_object* v___y_2776_ = _args[18];
lean_object* v___y_2777_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_2778_; uint8_t v_clsEnabled_boxed_2779_; lean_object* v_res_2780_; 
v_collapsed_boxed_2778_ = lean_unbox(v_collapsed_2759_);
v_clsEnabled_boxed_2779_ = lean_unbox(v_clsEnabled_2762_);
v_res_2780_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v_cls_2758_, v_collapsed_boxed_2778_, v_tag_2760_, v_opts_2761_, v_clsEnabled_boxed_2779_, v_oldTraces_2763_, v_msg_2764_, v_resStartStop_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec_ref(v_opts_2761_);
return v_res_2780_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_2786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact___lam__0___closed__6));
v___x_2787_ = l_Lean_Name_append(v___x_2786_, v___x_2785_);
return v___x_2787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__2));
v___x_2790_ = l_Lean_stringToMessageData(v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline(lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
uint8_t v___y_2804_; uint8_t v___y_2805_; lean_object* v___y_2806_; uint8_t v___y_2822_; lean_object* v___y_2823_; uint8_t v___y_2824_; uint8_t v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; uint8_t v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_a_2843_; uint8_t v___y_2853_; lean_object* v___y_2854_; uint8_t v___y_2855_; uint8_t v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; uint8_t v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v_a_2874_; uint8_t v___y_2887_; lean_object* v___y_2888_; uint8_t v___y_2889_; uint8_t v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; uint8_t v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; uint8_t v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; uint8_t v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; uint8_t v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; uint8_t v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v_a_3044_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; uint8_t v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; uint8_t v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v_a_3075_; lean_object* v___y_3088_; lean_object* v___y_3089_; uint8_t v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; uint8_t v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; uint8_t v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; uint8_t v___y_3149_; lean_object* v___y_3150_; uint8_t v_fixedInt_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; uint8_t v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v_a_3228_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; uint8_t v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; uint8_t v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v_a_3259_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; uint8_t v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; uint8_t v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; uint8_t v___y_3333_; lean_object* v___y_3334_; uint8_t v_fixedInt_3335_; uint8_t v_enums_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; uint8_t v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; uint8_t v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; uint8_t v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v_a_3414_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; uint8_t v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; uint8_t v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; uint8_t v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v_a_3445_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; uint8_t v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; uint8_t v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; uint8_t v___y_3519_; lean_object* v___y_3520_; uint8_t v_structures_3521_; uint8_t v_fixedInt_3522_; uint8_t v_enums_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; uint8_t v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; uint8_t v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v_a_3602_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; uint8_t v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; uint8_t v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; uint8_t v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v_a_3636_; lean_object* v___y_3646_; lean_object* v___y_3647_; uint8_t v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; uint8_t v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; uint8_t v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; uint8_t v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; uint8_t v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v_a_3773_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; uint8_t v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; uint8_t v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v_a_3803_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; uint8_t v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; uint8_t v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3906_; lean_object* v___y_3907_; uint8_t v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3931_; lean_object* v___y_3932_; uint8_t v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; uint8_t v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; uint8_t v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v_a_3952_; lean_object* v___y_3962_; lean_object* v___y_3963_; uint8_t v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; uint8_t v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; uint8_t v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v_a_3983_; lean_object* v___y_3996_; lean_object* v___y_3997_; uint8_t v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; uint8_t v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v_toCold_4101_; lean_object* v_options_4102_; uint8_t v_hasTrace_4103_; 
v_toCold_4101_ = lean_ctor_get(v_a_2800_, 0);
v_options_4102_ = lean_ctor_get(v_toCold_4101_, 2);
v_hasTrace_4103_ = lean_ctor_get_uint8(v_options_4102_, sizeof(void*)*1);
if (v_hasTrace_4103_ == 0)
{
v___y_4087_ = v_a_2791_;
v___y_4088_ = v_a_2792_;
v___y_4089_ = v_a_2793_;
v___y_4090_ = v_a_2794_;
v___y_4091_ = v_a_2795_;
v___y_4092_ = v_a_2796_;
v___y_4093_ = v_a_2797_;
v___y_4094_ = v_a_2798_;
v___y_4095_ = v_a_2799_;
v___y_4096_ = v_a_2800_;
v___y_4097_ = v_a_2801_;
goto v___jp_4086_;
}
else
{
lean_object* v_inheritedTraceOptions_4104_; lean_object* v_cls_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
v_inheritedTraceOptions_4104_ = lean_ctor_get(v_toCold_4101_, 11);
v_cls_4105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_4106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_4107_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4104_, v_options_4102_, v___x_4106_);
if (v___x_4107_ == 0)
{
v___y_4087_ = v_a_2791_;
v___y_4088_ = v_a_2792_;
v___y_4089_ = v_a_2793_;
v___y_4090_ = v_a_2794_;
v___y_4091_ = v_a_2795_;
v___y_4092_ = v_a_2796_;
v___y_4093_ = v_a_2797_;
v___y_4094_ = v_a_2798_;
v___y_4095_ = v_a_2799_;
v___y_4096_ = v_a_2800_;
v___y_4097_ = v_a_2801_;
goto v___jp_4086_;
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3);
v___x_4109_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg(v_cls_4105_, v___x_4108_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_dec_ref_known(v___x_4109_, 1);
v___y_4087_ = v_a_2791_;
v___y_4088_ = v_a_2792_;
v___y_4089_ = v_a_2793_;
v___y_4090_ = v_a_2794_;
v___y_4091_ = v_a_2795_;
v___y_4092_ = v_a_2796_;
v___y_4093_ = v_a_2797_;
v___y_4094_ = v_a_2798_;
v___y_4095_ = v_a_2799_;
v___y_4096_ = v_a_2800_;
v___y_4097_ = v_a_2801_;
goto v___jp_4086_;
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4109_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4109_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
v___jp_2803_:
{
if (lean_obj_tag(v___y_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2820_; 
v_a_2807_ = lean_ctor_get(v___y_2806_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___y_2806_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2809_ = v___y_2806_;
v_isShared_2810_ = v_isSharedCheck_2820_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___y_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2820_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
uint8_t v___x_2811_; 
v___x_2811_ = lean_unbox(v_a_2807_);
lean_dec(v_a_2807_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2812_ = lean_box(v___y_2805_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2812_);
v___x_2814_ = v___x_2809_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2816_ = lean_box(v___y_2804_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2816_);
v___x_2818_ = v___x_2809_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
return v___y_2806_;
}
}
v___jp_2821_:
{
lean_object* v___x_2844_; double v___x_2845_; double v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2844_ = lean_io_get_num_heartbeats();
v___x_2845_ = lean_float_of_nat(v___y_2838_);
v___x_2846_ = lean_float_of_nat(v___x_2844_);
v___x_2847_ = lean_box_float(v___x_2845_);
v___x_2848_ = lean_box_float(v___x_2846_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_a_2843_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2841_);
v___x_2851_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_2841_, v___y_2824_, v___y_2836_, v___y_2837_, v___y_2825_, v___y_2835_, v___y_2834_, v___x_2850_, v___y_2839_, v___y_2830_, v___y_2831_, v___y_2840_, v___y_2823_, v___y_2829_, v___y_2828_, v___y_2826_, v___y_2842_, v___y_2833_, v___y_2827_);
v___y_2804_ = v___y_2832_;
v___y_2805_ = v___y_2822_;
v___y_2806_ = v___x_2851_;
goto v___jp_2803_;
}
v___jp_2852_:
{
lean_object* v___x_2875_; double v___x_2876_; double v___x_2877_; double v___x_2878_; double v___x_2879_; double v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2875_ = lean_io_mono_nanos_now();
v___x_2876_ = lean_float_of_nat(v___y_2872_);
v___x_2877_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_2878_ = lean_float_div(v___x_2876_, v___x_2877_);
v___x_2879_ = lean_float_of_nat(v___x_2875_);
v___x_2880_ = lean_float_div(v___x_2879_, v___x_2877_);
v___x_2881_ = lean_box_float(v___x_2878_);
v___x_2882_ = lean_box_float(v___x_2880_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_a_2874_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
lean_inc_ref(v___y_2867_);
lean_inc(v___y_2871_);
v___x_2885_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_2871_, v___y_2855_, v___y_2867_, v___y_2868_, v___y_2856_, v___y_2866_, v___y_2865_, v___x_2884_, v___y_2869_, v___y_2861_, v___y_2862_, v___y_2870_, v___y_2854_, v___y_2860_, v___y_2859_, v___y_2857_, v___y_2873_, v___y_2864_, v___y_2858_);
v___y_2804_ = v___y_2863_;
v___y_2805_ = v___y_2853_;
v___y_2806_ = v___x_2885_;
goto v___jp_2803_;
}
v___jp_2886_:
{
lean_object* v___x_2907_; lean_object* v_a_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2907_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_2892_);
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2910_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v___y_2901_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_io_mono_nanos_now();
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2906_);
lean_inc_ref(v___y_2891_);
lean_inc(v___y_2893_);
lean_inc_ref(v___y_2894_);
lean_inc(v___y_2888_);
lean_inc_ref(v___y_2902_);
lean_inc(v___y_2896_);
lean_inc(v___y_2895_);
lean_inc_ref(v___y_2903_);
v___x_2912_ = lean_apply_12(v___y_2905_, v___y_2903_, v___y_2895_, v___y_2896_, v___y_2902_, v___y_2888_, v___y_2894_, v___y_2893_, v___y_2891_, v___y_2906_, v___y_2899_, v___y_2892_, lean_box(0));
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set_tag(v___x_2915_, 1);
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
v___y_2853_ = v___y_2887_;
v___y_2854_ = v___y_2888_;
v___y_2855_ = v___y_2889_;
v___y_2856_ = v___y_2890_;
v___y_2857_ = v___y_2891_;
v___y_2858_ = v___y_2892_;
v___y_2859_ = v___y_2893_;
v___y_2860_ = v___y_2894_;
v___y_2861_ = v___y_2895_;
v___y_2862_ = v___y_2896_;
v___y_2863_ = v___y_2897_;
v___y_2864_ = v___y_2899_;
v___y_2865_ = v___y_2898_;
v___y_2866_ = v_a_2908_;
v___y_2867_ = v___y_2900_;
v___y_2868_ = v___y_2901_;
v___y_2869_ = v___y_2903_;
v___y_2870_ = v___y_2902_;
v___y_2871_ = v___y_2904_;
v___y_2872_ = v___x_2911_;
v___y_2873_ = v___y_2906_;
v_a_2874_ = v___x_2918_;
goto v___jp_2852_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_a_2921_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2912_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2912_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set_tag(v___x_2923_, 0);
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
v___y_2853_ = v___y_2887_;
v___y_2854_ = v___y_2888_;
v___y_2855_ = v___y_2889_;
v___y_2856_ = v___y_2890_;
v___y_2857_ = v___y_2891_;
v___y_2858_ = v___y_2892_;
v___y_2859_ = v___y_2893_;
v___y_2860_ = v___y_2894_;
v___y_2861_ = v___y_2895_;
v___y_2862_ = v___y_2896_;
v___y_2863_ = v___y_2897_;
v___y_2864_ = v___y_2899_;
v___y_2865_ = v___y_2898_;
v___y_2866_ = v_a_2908_;
v___y_2867_ = v___y_2900_;
v___y_2868_ = v___y_2901_;
v___y_2869_ = v___y_2903_;
v___y_2870_ = v___y_2902_;
v___y_2871_ = v___y_2904_;
v___y_2872_ = v___x_2911_;
v___y_2873_ = v___y_2906_;
v_a_2874_ = v___x_2926_;
goto v___jp_2852_;
}
}
}
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2906_);
lean_inc_ref(v___y_2891_);
lean_inc(v___y_2893_);
lean_inc_ref(v___y_2894_);
lean_inc(v___y_2888_);
lean_inc_ref(v___y_2902_);
lean_inc(v___y_2896_);
lean_inc(v___y_2895_);
lean_inc_ref(v___y_2903_);
v___x_2930_ = lean_apply_12(v___y_2905_, v___y_2903_, v___y_2895_, v___y_2896_, v___y_2902_, v___y_2888_, v___y_2894_, v___y_2893_, v___y_2891_, v___y_2906_, v___y_2899_, v___y_2892_, lean_box(0));
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 1);
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
v___y_2822_ = v___y_2887_;
v___y_2823_ = v___y_2888_;
v___y_2824_ = v___y_2889_;
v___y_2825_ = v___y_2890_;
v___y_2826_ = v___y_2891_;
v___y_2827_ = v___y_2892_;
v___y_2828_ = v___y_2893_;
v___y_2829_ = v___y_2894_;
v___y_2830_ = v___y_2895_;
v___y_2831_ = v___y_2896_;
v___y_2832_ = v___y_2897_;
v___y_2833_ = v___y_2899_;
v___y_2834_ = v___y_2898_;
v___y_2835_ = v_a_2908_;
v___y_2836_ = v___y_2900_;
v___y_2837_ = v___y_2901_;
v___y_2838_ = v___x_2929_;
v___y_2839_ = v___y_2903_;
v___y_2840_ = v___y_2902_;
v___y_2841_ = v___y_2904_;
v___y_2842_ = v___y_2906_;
v_a_2843_ = v___x_2936_;
goto v___jp_2821_;
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
v_a_2939_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2930_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2930_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 0);
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
v___y_2822_ = v___y_2887_;
v___y_2823_ = v___y_2888_;
v___y_2824_ = v___y_2889_;
v___y_2825_ = v___y_2890_;
v___y_2826_ = v___y_2891_;
v___y_2827_ = v___y_2892_;
v___y_2828_ = v___y_2893_;
v___y_2829_ = v___y_2894_;
v___y_2830_ = v___y_2895_;
v___y_2831_ = v___y_2896_;
v___y_2832_ = v___y_2897_;
v___y_2833_ = v___y_2899_;
v___y_2834_ = v___y_2898_;
v___y_2835_ = v_a_2908_;
v___y_2836_ = v___y_2900_;
v___y_2837_ = v___y_2901_;
v___y_2838_ = v___x_2929_;
v___y_2839_ = v___y_2903_;
v___y_2840_ = v___y_2902_;
v___y_2841_ = v___y_2904_;
v___y_2842_ = v___y_2906_;
v_a_2843_ = v___x_2944_;
goto v___jp_2821_;
}
}
}
}
}
v___jp_2947_:
{
lean_object* v___x_2961_; lean_object* v_a_2962_; lean_object* v___x_2963_; 
v___x_2961_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_2950_);
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_2962_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v_a_2962_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; uint8_t v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v___x_2965_ = lean_unbox(v_a_2964_);
if (v___x_2965_ == 0)
{
uint8_t v_shortCircuit_2966_; 
v_shortCircuit_2966_ = lean_ctor_get_uint8(v___y_2949_, sizeof(void*)*3 + 9);
if (v_shortCircuit_2966_ == 0)
{
return v___x_2963_;
}
else
{
lean_object* v___x_2967_; lean_object* v_toCold_2968_; lean_object* v_options_2969_; uint8_t v_hasTrace_2970_; 
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2967_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_toCold_2968_ = lean_ctor_get(v___y_2959_, 0);
v_options_2969_ = lean_ctor_get(v_toCold_2968_, 2);
v_hasTrace_2970_ = lean_ctor_get_uint8(v_options_2969_, sizeof(void*)*1);
if (v_hasTrace_2970_ == 0)
{
lean_object* v_run_x27_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_run_x27_2971_ = lean_ctor_get(v___x_2967_, 1);
lean_inc_ref(v_run_x27_2971_);
lean_inc(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc(v___y_2958_);
lean_inc_ref(v___y_2957_);
lean_inc(v___y_2956_);
lean_inc_ref(v___y_2955_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2950_);
v___x_2972_ = lean_apply_12(v_run_x27_2971_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, lean_box(0));
v___x_2973_ = lean_unbox(v_a_2964_);
lean_dec(v_a_2964_);
v___y_2804_ = v___y_2948_;
v___y_2805_ = v___x_2973_;
v___y_2806_ = v___x_2972_;
goto v___jp_2803_;
}
else
{
lean_object* v_name_2974_; lean_object* v_run_x27_2975_; lean_object* v_inheritedTraceOptions_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_name_2974_ = lean_ctor_get(v___x_2967_, 0);
v_run_x27_2975_ = lean_ctor_get(v___x_2967_, 1);
v_inheritedTraceOptions_2976_ = lean_ctor_get(v_toCold_2968_, 11);
lean_inc(v_name_2974_);
v___f_2977_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2977_, 0, v_name_2974_);
v___x_2978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_2979_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_2980_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_2981_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2976_, v_options_2969_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = l_Lean_trace_profiler;
v___x_2983_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_2969_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; uint8_t v___x_2985_; 
lean_dec_ref(v___f_2977_);
lean_inc_ref(v_run_x27_2975_);
lean_inc(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc(v___y_2958_);
lean_inc_ref(v___y_2957_);
lean_inc(v___y_2956_);
lean_inc_ref(v___y_2955_);
lean_inc(v___y_2954_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2952_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2950_);
v___x_2984_ = lean_apply_12(v_run_x27_2975_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, lean_box(0));
v___x_2985_ = lean_unbox(v_a_2964_);
lean_dec(v_a_2964_);
v___y_2804_ = v___y_2948_;
v___y_2805_ = v___x_2985_;
v___y_2806_ = v___x_2984_;
goto v___jp_2803_;
}
else
{
uint8_t v___x_2986_; 
v___x_2986_ = lean_unbox(v_a_2964_);
lean_dec(v_a_2964_);
lean_inc_ref(v_run_x27_2975_);
v___y_2887_ = v___x_2986_;
v___y_2888_ = v___y_2954_;
v___y_2889_ = v_hasTrace_2970_;
v___y_2890_ = v___x_2981_;
v___y_2891_ = v___y_2957_;
v___y_2892_ = v___y_2960_;
v___y_2893_ = v___y_2956_;
v___y_2894_ = v___y_2955_;
v___y_2895_ = v___y_2951_;
v___y_2896_ = v___y_2952_;
v___y_2897_ = v___y_2948_;
v___y_2898_ = v___f_2977_;
v___y_2899_ = v___y_2959_;
v___y_2900_ = v___x_2979_;
v___y_2901_ = v_options_2969_;
v___y_2902_ = v___y_2953_;
v___y_2903_ = v___y_2950_;
v___y_2904_ = v___x_2978_;
v___y_2905_ = v_run_x27_2975_;
v___y_2906_ = v___y_2958_;
goto v___jp_2886_;
}
}
else
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_unbox(v_a_2964_);
lean_dec(v_a_2964_);
lean_inc_ref(v_run_x27_2975_);
v___y_2887_ = v___x_2987_;
v___y_2888_ = v___y_2954_;
v___y_2889_ = v_hasTrace_2970_;
v___y_2890_ = v___x_2981_;
v___y_2891_ = v___y_2957_;
v___y_2892_ = v___y_2960_;
v___y_2893_ = v___y_2956_;
v___y_2894_ = v___y_2955_;
v___y_2895_ = v___y_2951_;
v___y_2896_ = v___y_2952_;
v___y_2897_ = v___y_2948_;
v___y_2898_ = v___f_2977_;
v___y_2899_ = v___y_2959_;
v___y_2900_ = v___x_2979_;
v___y_2901_ = v_options_2969_;
v___y_2902_ = v___y_2953_;
v___y_2903_ = v___y_2950_;
v___y_2904_ = v___x_2978_;
v___y_2905_ = v_run_x27_2975_;
v___y_2906_ = v___y_2958_;
goto v___jp_2886_;
}
}
}
}
else
{
lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2995_; 
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; 
v_unused_2996_ = lean_ctor_get(v___x_2963_, 0);
lean_dec(v_unused_2996_);
v___x_2989_ = v___x_2963_;
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
else
{
lean_dec(v___x_2963_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2991_ = lean_box(v___y_2948_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2991_);
v___x_2993_ = v___x_2989_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
return v___x_2963_;
}
}
v___jp_2997_:
{
if (lean_obj_tag(v___y_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3021_; 
v_a_3012_ = lean_ctor_get(v___y_3011_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___y_3011_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3014_ = v___y_3011_;
v_isShared_3015_ = v_isSharedCheck_3021_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___y_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3021_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_unbox(v_a_3012_);
lean_dec(v_a_3012_);
if (v___x_3016_ == 0)
{
lean_del_object(v___x_3014_);
v___y_2948_ = v___y_3004_;
v___y_2949_ = v___y_3002_;
v___y_2950_ = v___y_3009_;
v___y_2951_ = v___y_3000_;
v___y_2952_ = v___y_3007_;
v___y_2953_ = v___y_3005_;
v___y_2954_ = v___y_2999_;
v___y_2955_ = v___y_3001_;
v___y_2956_ = v___y_2998_;
v___y_2957_ = v___y_3003_;
v___y_2958_ = v___y_3010_;
v___y_2959_ = v___y_3008_;
v___y_2960_ = v___y_3006_;
goto v___jp_2947_;
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3017_ = lean_box(v___y_3004_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3017_);
v___x_3019_ = v___x_3014_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
return v___y_3011_;
}
}
v___jp_3022_:
{
lean_object* v___x_3045_; double v___x_3046_; double v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3045_ = lean_io_get_num_heartbeats();
v___x_3046_ = lean_float_of_nat(v___y_3035_);
v___x_3047_ = lean_float_of_nat(v___x_3045_);
v___x_3048_ = lean_box_float(v___x_3046_);
v___x_3049_ = lean_box_float(v___x_3047_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3048_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v_a_3044_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
lean_inc_ref(v___y_3034_);
lean_inc(v___y_3036_);
v___x_3052_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3036_, v___y_3026_, v___y_3034_, v___y_3031_, v___y_3040_, v___y_3025_, v___y_3038_, v___x_3051_, v___y_3043_, v___y_3029_, v___y_3041_, v___y_3033_, v___y_3024_, v___y_3028_, v___y_3023_, v___y_3030_, v___y_3042_, v___y_3039_, v___y_3037_);
v___y_2998_ = v___y_3023_;
v___y_2999_ = v___y_3024_;
v___y_3000_ = v___y_3029_;
v___y_3001_ = v___y_3028_;
v___y_3002_ = v___y_3027_;
v___y_3003_ = v___y_3030_;
v___y_3004_ = v___y_3032_;
v___y_3005_ = v___y_3033_;
v___y_3006_ = v___y_3037_;
v___y_3007_ = v___y_3041_;
v___y_3008_ = v___y_3039_;
v___y_3009_ = v___y_3043_;
v___y_3010_ = v___y_3042_;
v___y_3011_ = v___x_3052_;
goto v___jp_2997_;
}
v___jp_3053_:
{
lean_object* v___x_3076_; double v___x_3077_; double v___x_3078_; double v___x_3079_; double v___x_3080_; double v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3076_ = lean_io_mono_nanos_now();
v___x_3077_ = lean_float_of_nat(v___y_3069_);
v___x_3078_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_3079_ = lean_float_div(v___x_3077_, v___x_3078_);
v___x_3080_ = lean_float_of_nat(v___x_3076_);
v___x_3081_ = lean_float_div(v___x_3080_, v___x_3078_);
v___x_3082_ = lean_box_float(v___x_3079_);
v___x_3083_ = lean_box_float(v___x_3081_);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_a_3075_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
lean_inc_ref(v___y_3065_);
lean_inc(v___y_3066_);
v___x_3086_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3066_, v___y_3057_, v___y_3065_, v___y_3062_, v___y_3071_, v___y_3056_, v___y_3068_, v___x_3085_, v___y_3074_, v___y_3060_, v___y_3072_, v___y_3064_, v___y_3055_, v___y_3059_, v___y_3054_, v___y_3061_, v___y_3073_, v___y_3070_, v___y_3067_);
v___y_2998_ = v___y_3054_;
v___y_2999_ = v___y_3055_;
v___y_3000_ = v___y_3060_;
v___y_3001_ = v___y_3059_;
v___y_3002_ = v___y_3058_;
v___y_3003_ = v___y_3061_;
v___y_3004_ = v___y_3063_;
v___y_3005_ = v___y_3064_;
v___y_3006_ = v___y_3067_;
v___y_3007_ = v___y_3072_;
v___y_3008_ = v___y_3070_;
v___y_3009_ = v___y_3074_;
v___y_3010_ = v___y_3073_;
v___y_3011_ = v___x_3086_;
goto v___jp_2997_;
}
v___jp_3087_:
{
lean_object* v___x_3108_; lean_object* v_a_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3108_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_3101_);
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref(v___x_3108_);
v___x_3110_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3111_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v___y_3096_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_io_mono_nanos_now();
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3105_);
lean_inc(v___y_3107_);
lean_inc_ref(v___y_3094_);
lean_inc(v___y_3088_);
lean_inc_ref(v___y_3092_);
lean_inc(v___y_3089_);
lean_inc_ref(v___y_3098_);
lean_inc(v___y_3103_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3106_);
v___x_3113_ = lean_apply_12(v___y_3095_, v___y_3106_, v___y_3093_, v___y_3103_, v___y_3098_, v___y_3089_, v___y_3092_, v___y_3088_, v___y_3094_, v___y_3107_, v___y_3105_, v___y_3101_, lean_box(0));
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
lean_ctor_set_tag(v___x_3116_, 1);
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
v___y_3056_ = v_a_3109_;
v___y_3057_ = v___y_3090_;
v___y_3058_ = v___y_3091_;
v___y_3059_ = v___y_3092_;
v___y_3060_ = v___y_3093_;
v___y_3061_ = v___y_3094_;
v___y_3062_ = v___y_3096_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v___y_3098_;
v___y_3065_ = v___y_3099_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___y_3101_;
v___y_3068_ = v___y_3102_;
v___y_3069_ = v___x_3112_;
v___y_3070_ = v___y_3105_;
v___y_3071_ = v___y_3104_;
v___y_3072_ = v___y_3103_;
v___y_3073_ = v___y_3107_;
v___y_3074_ = v___y_3106_;
v_a_3075_ = v___x_3119_;
goto v___jp_3053_;
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
v_a_3122_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3113_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3113_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
lean_ctor_set_tag(v___x_3124_, 0);
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
v___y_3056_ = v_a_3109_;
v___y_3057_ = v___y_3090_;
v___y_3058_ = v___y_3091_;
v___y_3059_ = v___y_3092_;
v___y_3060_ = v___y_3093_;
v___y_3061_ = v___y_3094_;
v___y_3062_ = v___y_3096_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v___y_3098_;
v___y_3065_ = v___y_3099_;
v___y_3066_ = v___y_3100_;
v___y_3067_ = v___y_3101_;
v___y_3068_ = v___y_3102_;
v___y_3069_ = v___x_3112_;
v___y_3070_ = v___y_3105_;
v___y_3071_ = v___y_3104_;
v___y_3072_ = v___y_3103_;
v___y_3073_ = v___y_3107_;
v___y_3074_ = v___y_3106_;
v_a_3075_ = v___x_3127_;
goto v___jp_3053_;
}
}
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3105_);
lean_inc(v___y_3107_);
lean_inc_ref(v___y_3094_);
lean_inc(v___y_3088_);
lean_inc_ref(v___y_3092_);
lean_inc(v___y_3089_);
lean_inc_ref(v___y_3098_);
lean_inc(v___y_3103_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3106_);
v___x_3131_ = lean_apply_12(v___y_3095_, v___y_3106_, v___y_3093_, v___y_3103_, v___y_3098_, v___y_3089_, v___y_3092_, v___y_3088_, v___y_3094_, v___y_3107_, v___y_3105_, v___y_3101_, lean_box(0));
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set_tag(v___x_3134_, 1);
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
v___y_3023_ = v___y_3088_;
v___y_3024_ = v___y_3089_;
v___y_3025_ = v_a_3109_;
v___y_3026_ = v___y_3090_;
v___y_3027_ = v___y_3091_;
v___y_3028_ = v___y_3092_;
v___y_3029_ = v___y_3093_;
v___y_3030_ = v___y_3094_;
v___y_3031_ = v___y_3096_;
v___y_3032_ = v___y_3097_;
v___y_3033_ = v___y_3098_;
v___y_3034_ = v___y_3099_;
v___y_3035_ = v___x_3130_;
v___y_3036_ = v___y_3100_;
v___y_3037_ = v___y_3101_;
v___y_3038_ = v___y_3102_;
v___y_3039_ = v___y_3105_;
v___y_3040_ = v___y_3104_;
v___y_3041_ = v___y_3103_;
v___y_3042_ = v___y_3107_;
v___y_3043_ = v___y_3106_;
v_a_3044_ = v___x_3137_;
goto v___jp_3022_;
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_a_3140_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3131_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3131_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 0);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
v___y_3023_ = v___y_3088_;
v___y_3024_ = v___y_3089_;
v___y_3025_ = v_a_3109_;
v___y_3026_ = v___y_3090_;
v___y_3027_ = v___y_3091_;
v___y_3028_ = v___y_3092_;
v___y_3029_ = v___y_3093_;
v___y_3030_ = v___y_3094_;
v___y_3031_ = v___y_3096_;
v___y_3032_ = v___y_3097_;
v___y_3033_ = v___y_3098_;
v___y_3034_ = v___y_3099_;
v___y_3035_ = v___x_3130_;
v___y_3036_ = v___y_3100_;
v___y_3037_ = v___y_3101_;
v___y_3038_ = v___y_3102_;
v___y_3039_ = v___y_3105_;
v___y_3040_ = v___y_3104_;
v___y_3041_ = v___y_3103_;
v___y_3042_ = v___y_3107_;
v___y_3043_ = v___y_3106_;
v_a_3044_ = v___x_3145_;
goto v___jp_3022_;
}
}
}
}
}
v___jp_3148_:
{
if (v_fixedInt_3151_ == 0)
{
v___y_2948_ = v___y_3149_;
v___y_2949_ = v___y_3150_;
v___y_2950_ = v___y_3152_;
v___y_2951_ = v___y_3153_;
v___y_2952_ = v___y_3154_;
v___y_2953_ = v___y_3155_;
v___y_2954_ = v___y_3156_;
v___y_2955_ = v___y_3157_;
v___y_2956_ = v___y_3158_;
v___y_2957_ = v___y_3159_;
v___y_2958_ = v___y_3160_;
v___y_2959_ = v___y_3161_;
v___y_2960_ = v___y_3162_;
goto v___jp_2947_;
}
else
{
lean_object* v___x_3163_; lean_object* v_toCold_3164_; lean_object* v_options_3165_; uint8_t v_hasTrace_3166_; 
v___x_3163_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_toCold_3164_ = lean_ctor_get(v___y_3161_, 0);
v_options_3165_ = lean_ctor_get(v_toCold_3164_, 2);
v_hasTrace_3166_ = lean_ctor_get_uint8(v_options_3165_, sizeof(void*)*1);
if (v_hasTrace_3166_ == 0)
{
lean_object* v_run_x27_3167_; lean_object* v___x_3168_; 
v_run_x27_3167_ = lean_ctor_get(v___x_3163_, 1);
lean_inc_ref(v_run_x27_3167_);
lean_inc(v___y_3162_);
lean_inc_ref(v___y_3161_);
lean_inc(v___y_3160_);
lean_inc_ref(v___y_3159_);
lean_inc(v___y_3158_);
lean_inc_ref(v___y_3157_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
v___x_3168_ = lean_apply_12(v_run_x27_3167_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, lean_box(0));
v___y_2998_ = v___y_3158_;
v___y_2999_ = v___y_3156_;
v___y_3000_ = v___y_3153_;
v___y_3001_ = v___y_3157_;
v___y_3002_ = v___y_3150_;
v___y_3003_ = v___y_3159_;
v___y_3004_ = v___y_3149_;
v___y_3005_ = v___y_3155_;
v___y_3006_ = v___y_3162_;
v___y_3007_ = v___y_3154_;
v___y_3008_ = v___y_3161_;
v___y_3009_ = v___y_3152_;
v___y_3010_ = v___y_3160_;
v___y_3011_ = v___x_3168_;
goto v___jp_2997_;
}
else
{
lean_object* v_name_3169_; lean_object* v_run_x27_3170_; lean_object* v_inheritedTraceOptions_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_name_3169_ = lean_ctor_get(v___x_3163_, 0);
v_run_x27_3170_ = lean_ctor_get(v___x_3163_, 1);
v_inheritedTraceOptions_3171_ = lean_ctor_get(v_toCold_3164_, 11);
lean_inc(v_name_3169_);
v___f_3172_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_3172_, 0, v_name_3169_);
v___x_3173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_3174_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_3175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_3176_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3171_, v_options_3165_, v___x_3175_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = l_Lean_trace_profiler;
v___x_3178_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_3165_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; 
lean_dec_ref(v___f_3172_);
lean_inc_ref(v_run_x27_3170_);
lean_inc(v___y_3162_);
lean_inc_ref(v___y_3161_);
lean_inc(v___y_3160_);
lean_inc_ref(v___y_3159_);
lean_inc(v___y_3158_);
lean_inc_ref(v___y_3157_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
v___x_3179_ = lean_apply_12(v_run_x27_3170_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, lean_box(0));
v___y_2998_ = v___y_3158_;
v___y_2999_ = v___y_3156_;
v___y_3000_ = v___y_3153_;
v___y_3001_ = v___y_3157_;
v___y_3002_ = v___y_3150_;
v___y_3003_ = v___y_3159_;
v___y_3004_ = v___y_3149_;
v___y_3005_ = v___y_3155_;
v___y_3006_ = v___y_3162_;
v___y_3007_ = v___y_3154_;
v___y_3008_ = v___y_3161_;
v___y_3009_ = v___y_3152_;
v___y_3010_ = v___y_3160_;
v___y_3011_ = v___x_3179_;
goto v___jp_2997_;
}
else
{
lean_inc_ref(v_run_x27_3170_);
v___y_3088_ = v___y_3158_;
v___y_3089_ = v___y_3156_;
v___y_3090_ = v_hasTrace_3166_;
v___y_3091_ = v___y_3150_;
v___y_3092_ = v___y_3157_;
v___y_3093_ = v___y_3153_;
v___y_3094_ = v___y_3159_;
v___y_3095_ = v_run_x27_3170_;
v___y_3096_ = v_options_3165_;
v___y_3097_ = v___y_3149_;
v___y_3098_ = v___y_3155_;
v___y_3099_ = v___x_3174_;
v___y_3100_ = v___x_3173_;
v___y_3101_ = v___y_3162_;
v___y_3102_ = v___f_3172_;
v___y_3103_ = v___y_3154_;
v___y_3104_ = v___x_3176_;
v___y_3105_ = v___y_3161_;
v___y_3106_ = v___y_3152_;
v___y_3107_ = v___y_3160_;
goto v___jp_3087_;
}
}
else
{
lean_inc_ref(v_run_x27_3170_);
v___y_3088_ = v___y_3158_;
v___y_3089_ = v___y_3156_;
v___y_3090_ = v_hasTrace_3166_;
v___y_3091_ = v___y_3150_;
v___y_3092_ = v___y_3157_;
v___y_3093_ = v___y_3153_;
v___y_3094_ = v___y_3159_;
v___y_3095_ = v_run_x27_3170_;
v___y_3096_ = v_options_3165_;
v___y_3097_ = v___y_3149_;
v___y_3098_ = v___y_3155_;
v___y_3099_ = v___x_3174_;
v___y_3100_ = v___x_3173_;
v___y_3101_ = v___y_3162_;
v___y_3102_ = v___f_3172_;
v___y_3103_ = v___y_3154_;
v___y_3104_ = v___x_3176_;
v___y_3105_ = v___y_3161_;
v___y_3106_ = v___y_3152_;
v___y_3107_ = v___y_3160_;
goto v___jp_3087_;
}
}
}
}
v___jp_3180_:
{
if (lean_obj_tag(v___y_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3205_; 
v_a_3195_ = lean_ctor_get(v___y_3194_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___y_3194_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3197_ = v___y_3194_;
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___y_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
uint8_t v___x_3199_; 
v___x_3199_ = lean_unbox(v_a_3195_);
lean_dec(v_a_3195_);
if (v___x_3199_ == 0)
{
uint8_t v_fixedInt_3200_; 
lean_del_object(v___x_3197_);
v_fixedInt_3200_ = lean_ctor_get_uint8(v___y_3186_, sizeof(void*)*3 + 6);
v___y_3149_ = v___y_3188_;
v___y_3150_ = v___y_3186_;
v_fixedInt_3151_ = v_fixedInt_3200_;
v___y_3152_ = v___y_3190_;
v___y_3153_ = v___y_3189_;
v___y_3154_ = v___y_3182_;
v___y_3155_ = v___y_3184_;
v___y_3156_ = v___y_3193_;
v___y_3157_ = v___y_3191_;
v___y_3158_ = v___y_3183_;
v___y_3159_ = v___y_3185_;
v___y_3160_ = v___y_3187_;
v___y_3161_ = v___y_3181_;
v___y_3162_ = v___y_3192_;
goto v___jp_3148_;
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3201_ = lean_box(v___y_3188_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3201_);
v___x_3203_ = v___x_3197_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
return v___y_3194_;
}
}
v___jp_3206_:
{
lean_object* v___x_3229_; double v___x_3230_; double v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3229_ = lean_io_get_num_heartbeats();
v___x_3230_ = lean_float_of_nat(v___y_3225_);
v___x_3231_ = lean_float_of_nat(v___x_3229_);
v___x_3232_ = lean_box_float(v___x_3230_);
v___x_3233_ = lean_box_float(v___x_3231_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_a_3228_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
lean_inc_ref(v___y_3227_);
lean_inc(v___y_3208_);
v___x_3236_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3208_, v___y_3220_, v___y_3227_, v___y_3216_, v___y_3210_, v___y_3223_, v___y_3219_, v___x_3235_, v___y_3221_, v___y_3218_, v___y_3209_, v___y_3213_, v___y_3226_, v___y_3222_, v___y_3211_, v___y_3212_, v___y_3215_, v___y_3207_, v___y_3224_);
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3209_;
v___y_3183_ = v___y_3211_;
v___y_3184_ = v___y_3213_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___y_3214_;
v___y_3187_ = v___y_3215_;
v___y_3188_ = v___y_3217_;
v___y_3189_ = v___y_3218_;
v___y_3190_ = v___y_3221_;
v___y_3191_ = v___y_3222_;
v___y_3192_ = v___y_3224_;
v___y_3193_ = v___y_3226_;
v___y_3194_ = v___x_3236_;
goto v___jp_3180_;
}
v___jp_3237_:
{
lean_object* v___x_3260_; double v___x_3261_; double v___x_3262_; double v___x_3263_; double v___x_3264_; double v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3260_ = lean_io_mono_nanos_now();
v___x_3261_ = lean_float_of_nat(v___y_3249_);
v___x_3262_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_3263_ = lean_float_div(v___x_3261_, v___x_3262_);
v___x_3264_ = lean_float_of_nat(v___x_3260_);
v___x_3265_ = lean_float_div(v___x_3264_, v___x_3262_);
v___x_3266_ = lean_box_float(v___x_3263_);
v___x_3267_ = lean_box_float(v___x_3265_);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3266_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v_a_3259_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
lean_inc_ref(v___y_3258_);
lean_inc(v___y_3239_);
v___x_3270_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3239_, v___y_3252_, v___y_3258_, v___y_3247_, v___y_3241_, v___y_3255_, v___y_3251_, v___x_3269_, v___y_3253_, v___y_3250_, v___y_3240_, v___y_3244_, v___y_3257_, v___y_3254_, v___y_3242_, v___y_3243_, v___y_3246_, v___y_3238_, v___y_3256_);
v___y_3181_ = v___y_3238_;
v___y_3182_ = v___y_3240_;
v___y_3183_ = v___y_3242_;
v___y_3184_ = v___y_3244_;
v___y_3185_ = v___y_3243_;
v___y_3186_ = v___y_3245_;
v___y_3187_ = v___y_3246_;
v___y_3188_ = v___y_3248_;
v___y_3189_ = v___y_3250_;
v___y_3190_ = v___y_3253_;
v___y_3191_ = v___y_3254_;
v___y_3192_ = v___y_3256_;
v___y_3193_ = v___y_3257_;
v___y_3194_ = v___x_3270_;
goto v___jp_3180_;
}
v___jp_3271_:
{
lean_object* v___x_3292_; lean_object* v_a_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v___x_3292_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_3289_);
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3293_);
lean_dec_ref(v___x_3292_);
v___x_3294_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3295_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v___y_3281_, v___x_3294_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = lean_io_mono_nanos_now();
lean_inc(v___y_3289_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3280_);
lean_inc_ref(v___y_3277_);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3288_);
lean_inc(v___y_3290_);
lean_inc_ref(v___y_3278_);
lean_inc(v___y_3274_);
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3285_);
v___x_3297_ = lean_apply_12(v___y_3287_, v___y_3285_, v___y_3283_, v___y_3274_, v___y_3278_, v___y_3290_, v___y_3288_, v___y_3276_, v___y_3277_, v___y_3280_, v___y_3272_, v___y_3289_, lean_box(0));
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3297_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3297_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 1);
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
v___y_3238_ = v___y_3272_;
v___y_3239_ = v___y_3273_;
v___y_3240_ = v___y_3274_;
v___y_3241_ = v___y_3275_;
v___y_3242_ = v___y_3276_;
v___y_3243_ = v___y_3277_;
v___y_3244_ = v___y_3278_;
v___y_3245_ = v___y_3279_;
v___y_3246_ = v___y_3280_;
v___y_3247_ = v___y_3281_;
v___y_3248_ = v___y_3282_;
v___y_3249_ = v___x_3296_;
v___y_3250_ = v___y_3283_;
v___y_3251_ = v___y_3284_;
v___y_3252_ = v___y_3286_;
v___y_3253_ = v___y_3285_;
v___y_3254_ = v___y_3288_;
v___y_3255_ = v_a_3293_;
v___y_3256_ = v___y_3289_;
v___y_3257_ = v___y_3290_;
v___y_3258_ = v___y_3291_;
v_a_3259_ = v___x_3303_;
goto v___jp_3237_;
}
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
v_a_3306_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3297_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3297_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set_tag(v___x_3308_, 0);
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
v___y_3238_ = v___y_3272_;
v___y_3239_ = v___y_3273_;
v___y_3240_ = v___y_3274_;
v___y_3241_ = v___y_3275_;
v___y_3242_ = v___y_3276_;
v___y_3243_ = v___y_3277_;
v___y_3244_ = v___y_3278_;
v___y_3245_ = v___y_3279_;
v___y_3246_ = v___y_3280_;
v___y_3247_ = v___y_3281_;
v___y_3248_ = v___y_3282_;
v___y_3249_ = v___x_3296_;
v___y_3250_ = v___y_3283_;
v___y_3251_ = v___y_3284_;
v___y_3252_ = v___y_3286_;
v___y_3253_ = v___y_3285_;
v___y_3254_ = v___y_3288_;
v___y_3255_ = v_a_3293_;
v___y_3256_ = v___y_3289_;
v___y_3257_ = v___y_3290_;
v___y_3258_ = v___y_3291_;
v_a_3259_ = v___x_3311_;
goto v___jp_3237_;
}
}
}
}
else
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3289_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3280_);
lean_inc_ref(v___y_3277_);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3288_);
lean_inc(v___y_3290_);
lean_inc_ref(v___y_3278_);
lean_inc(v___y_3274_);
lean_inc(v___y_3283_);
lean_inc_ref(v___y_3285_);
v___x_3315_ = lean_apply_12(v___y_3287_, v___y_3285_, v___y_3283_, v___y_3274_, v___y_3278_, v___y_3290_, v___y_3288_, v___y_3276_, v___y_3277_, v___y_3280_, v___y_3272_, v___y_3289_, lean_box(0));
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
lean_ctor_set_tag(v___x_3318_, 1);
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
v___y_3207_ = v___y_3272_;
v___y_3208_ = v___y_3273_;
v___y_3209_ = v___y_3274_;
v___y_3210_ = v___y_3275_;
v___y_3211_ = v___y_3276_;
v___y_3212_ = v___y_3277_;
v___y_3213_ = v___y_3278_;
v___y_3214_ = v___y_3279_;
v___y_3215_ = v___y_3280_;
v___y_3216_ = v___y_3281_;
v___y_3217_ = v___y_3282_;
v___y_3218_ = v___y_3283_;
v___y_3219_ = v___y_3284_;
v___y_3220_ = v___y_3286_;
v___y_3221_ = v___y_3285_;
v___y_3222_ = v___y_3288_;
v___y_3223_ = v_a_3293_;
v___y_3224_ = v___y_3289_;
v___y_3225_ = v___x_3314_;
v___y_3226_ = v___y_3290_;
v___y_3227_ = v___y_3291_;
v_a_3228_ = v___x_3321_;
goto v___jp_3206_;
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
v_a_3324_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3315_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3315_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
lean_ctor_set_tag(v___x_3326_, 0);
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
v___y_3207_ = v___y_3272_;
v___y_3208_ = v___y_3273_;
v___y_3209_ = v___y_3274_;
v___y_3210_ = v___y_3275_;
v___y_3211_ = v___y_3276_;
v___y_3212_ = v___y_3277_;
v___y_3213_ = v___y_3278_;
v___y_3214_ = v___y_3279_;
v___y_3215_ = v___y_3280_;
v___y_3216_ = v___y_3281_;
v___y_3217_ = v___y_3282_;
v___y_3218_ = v___y_3283_;
v___y_3219_ = v___y_3284_;
v___y_3220_ = v___y_3286_;
v___y_3221_ = v___y_3285_;
v___y_3222_ = v___y_3288_;
v___y_3223_ = v_a_3293_;
v___y_3224_ = v___y_3289_;
v___y_3225_ = v___x_3314_;
v___y_3226_ = v___y_3290_;
v___y_3227_ = v___y_3291_;
v_a_3228_ = v___x_3329_;
goto v___jp_3206_;
}
}
}
}
}
v___jp_3332_:
{
if (v_enums_3336_ == 0)
{
v___y_3149_ = v___y_3333_;
v___y_3150_ = v___y_3334_;
v_fixedInt_3151_ = v_fixedInt_3335_;
v___y_3152_ = v___y_3337_;
v___y_3153_ = v___y_3338_;
v___y_3154_ = v___y_3339_;
v___y_3155_ = v___y_3340_;
v___y_3156_ = v___y_3341_;
v___y_3157_ = v___y_3342_;
v___y_3158_ = v___y_3343_;
v___y_3159_ = v___y_3344_;
v___y_3160_ = v___y_3345_;
v___y_3161_ = v___y_3346_;
v___y_3162_ = v___y_3347_;
goto v___jp_3148_;
}
else
{
lean_object* v___x_3348_; lean_object* v_toCold_3349_; lean_object* v_options_3350_; uint8_t v_hasTrace_3351_; 
v___x_3348_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_toCold_3349_ = lean_ctor_get(v___y_3346_, 0);
v_options_3350_ = lean_ctor_get(v_toCold_3349_, 2);
v_hasTrace_3351_ = lean_ctor_get_uint8(v_options_3350_, sizeof(void*)*1);
if (v_hasTrace_3351_ == 0)
{
lean_object* v_run_x27_3352_; lean_object* v___x_3353_; 
v_run_x27_3352_ = lean_ctor_get(v___x_3348_, 1);
lean_inc_ref(v_run_x27_3352_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
lean_inc(v___y_3345_);
lean_inc_ref(v___y_3344_);
lean_inc(v___y_3343_);
lean_inc_ref(v___y_3342_);
lean_inc(v___y_3341_);
lean_inc_ref(v___y_3340_);
lean_inc(v___y_3339_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
v___x_3353_ = lean_apply_12(v_run_x27_3352_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, lean_box(0));
v___y_3181_ = v___y_3346_;
v___y_3182_ = v___y_3339_;
v___y_3183_ = v___y_3343_;
v___y_3184_ = v___y_3340_;
v___y_3185_ = v___y_3344_;
v___y_3186_ = v___y_3334_;
v___y_3187_ = v___y_3345_;
v___y_3188_ = v___y_3333_;
v___y_3189_ = v___y_3338_;
v___y_3190_ = v___y_3337_;
v___y_3191_ = v___y_3342_;
v___y_3192_ = v___y_3347_;
v___y_3193_ = v___y_3341_;
v___y_3194_ = v___x_3353_;
goto v___jp_3180_;
}
else
{
lean_object* v_name_3354_; lean_object* v_run_x27_3355_; lean_object* v_inheritedTraceOptions_3356_; lean_object* v___f_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v_name_3354_ = lean_ctor_get(v___x_3348_, 0);
v_run_x27_3355_ = lean_ctor_get(v___x_3348_, 1);
v_inheritedTraceOptions_3356_ = lean_ctor_get(v_toCold_3349_, 11);
lean_inc(v_name_3354_);
v___f_3357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_3357_, 0, v_name_3354_);
v___x_3358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_3359_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_3360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_3361_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3356_, v_options_3350_, v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; uint8_t v___x_3363_; 
v___x_3362_ = l_Lean_trace_profiler;
v___x_3363_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_3350_, v___x_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec_ref(v___f_3357_);
lean_inc_ref(v_run_x27_3355_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
lean_inc(v___y_3345_);
lean_inc_ref(v___y_3344_);
lean_inc(v___y_3343_);
lean_inc_ref(v___y_3342_);
lean_inc(v___y_3341_);
lean_inc_ref(v___y_3340_);
lean_inc(v___y_3339_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
v___x_3364_ = lean_apply_12(v_run_x27_3355_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, lean_box(0));
v___y_3181_ = v___y_3346_;
v___y_3182_ = v___y_3339_;
v___y_3183_ = v___y_3343_;
v___y_3184_ = v___y_3340_;
v___y_3185_ = v___y_3344_;
v___y_3186_ = v___y_3334_;
v___y_3187_ = v___y_3345_;
v___y_3188_ = v___y_3333_;
v___y_3189_ = v___y_3338_;
v___y_3190_ = v___y_3337_;
v___y_3191_ = v___y_3342_;
v___y_3192_ = v___y_3347_;
v___y_3193_ = v___y_3341_;
v___y_3194_ = v___x_3364_;
goto v___jp_3180_;
}
else
{
lean_inc_ref(v_run_x27_3355_);
v___y_3272_ = v___y_3346_;
v___y_3273_ = v___x_3358_;
v___y_3274_ = v___y_3339_;
v___y_3275_ = v___x_3361_;
v___y_3276_ = v___y_3343_;
v___y_3277_ = v___y_3344_;
v___y_3278_ = v___y_3340_;
v___y_3279_ = v___y_3334_;
v___y_3280_ = v___y_3345_;
v___y_3281_ = v_options_3350_;
v___y_3282_ = v___y_3333_;
v___y_3283_ = v___y_3338_;
v___y_3284_ = v___f_3357_;
v___y_3285_ = v___y_3337_;
v___y_3286_ = v_hasTrace_3351_;
v___y_3287_ = v_run_x27_3355_;
v___y_3288_ = v___y_3342_;
v___y_3289_ = v___y_3347_;
v___y_3290_ = v___y_3341_;
v___y_3291_ = v___x_3359_;
goto v___jp_3271_;
}
}
else
{
lean_inc_ref(v_run_x27_3355_);
v___y_3272_ = v___y_3346_;
v___y_3273_ = v___x_3358_;
v___y_3274_ = v___y_3339_;
v___y_3275_ = v___x_3361_;
v___y_3276_ = v___y_3343_;
v___y_3277_ = v___y_3344_;
v___y_3278_ = v___y_3340_;
v___y_3279_ = v___y_3334_;
v___y_3280_ = v___y_3345_;
v___y_3281_ = v_options_3350_;
v___y_3282_ = v___y_3333_;
v___y_3283_ = v___y_3338_;
v___y_3284_ = v___f_3357_;
v___y_3285_ = v___y_3337_;
v___y_3286_ = v_hasTrace_3351_;
v___y_3287_ = v_run_x27_3355_;
v___y_3288_ = v___y_3342_;
v___y_3289_ = v___y_3347_;
v___y_3290_ = v___y_3341_;
v___y_3291_ = v___x_3359_;
goto v___jp_3271_;
}
}
}
}
v___jp_3365_:
{
if (lean_obj_tag(v___y_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3391_; 
v_a_3380_ = lean_ctor_get(v___y_3379_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___y_3379_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3382_ = v___y_3379_;
v_isShared_3383_ = v_isSharedCheck_3391_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___y_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3391_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
uint8_t v___x_3384_; 
v___x_3384_ = lean_unbox(v_a_3380_);
lean_dec(v_a_3380_);
if (v___x_3384_ == 0)
{
uint8_t v_fixedInt_3385_; uint8_t v_enums_3386_; 
lean_del_object(v___x_3382_);
v_fixedInt_3385_ = lean_ctor_get_uint8(v___y_3370_, sizeof(void*)*3 + 6);
v_enums_3386_ = lean_ctor_get_uint8(v___y_3370_, sizeof(void*)*3 + 7);
v___y_3333_ = v___y_3373_;
v___y_3334_ = v___y_3370_;
v_fixedInt_3335_ = v_fixedInt_3385_;
v_enums_3336_ = v_enums_3386_;
v___y_3337_ = v___y_3371_;
v___y_3338_ = v___y_3377_;
v___y_3339_ = v___y_3369_;
v___y_3340_ = v___y_3378_;
v___y_3341_ = v___y_3368_;
v___y_3342_ = v___y_3374_;
v___y_3343_ = v___y_3376_;
v___y_3344_ = v___y_3375_;
v___y_3345_ = v___y_3366_;
v___y_3346_ = v___y_3372_;
v___y_3347_ = v___y_3367_;
goto v___jp_3332_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = lean_box(v___y_3373_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3387_);
v___x_3389_ = v___x_3382_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
else
{
return v___y_3379_;
}
}
v___jp_3392_:
{
lean_object* v___x_3415_; double v___x_3416_; double v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3415_ = lean_io_get_num_heartbeats();
v___x_3416_ = lean_float_of_nat(v___y_3409_);
v___x_3417_ = lean_float_of_nat(v___x_3415_);
v___x_3418_ = lean_box_float(v___x_3416_);
v___x_3419_ = lean_box_float(v___x_3417_);
v___x_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v_a_3414_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
lean_inc_ref(v___y_3410_);
lean_inc(v___y_3402_);
v___x_3422_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3402_, v___y_3398_, v___y_3410_, v___y_3407_, v___y_3411_, v___y_3405_, v___y_3395_, v___x_3421_, v___y_3401_, v___y_3412_, v___y_3399_, v___y_3413_, v___y_3396_, v___y_3404_, v___y_3408_, v___y_3406_, v___y_3393_, v___y_3400_, v___y_3394_);
v___y_3366_ = v___y_3393_;
v___y_3367_ = v___y_3394_;
v___y_3368_ = v___y_3396_;
v___y_3369_ = v___y_3399_;
v___y_3370_ = v___y_3397_;
v___y_3371_ = v___y_3401_;
v___y_3372_ = v___y_3400_;
v___y_3373_ = v___y_3403_;
v___y_3374_ = v___y_3404_;
v___y_3375_ = v___y_3406_;
v___y_3376_ = v___y_3408_;
v___y_3377_ = v___y_3412_;
v___y_3378_ = v___y_3413_;
v___y_3379_ = v___x_3422_;
goto v___jp_3365_;
}
v___jp_3423_:
{
lean_object* v___x_3446_; double v___x_3447_; double v___x_3448_; double v___x_3449_; double v___x_3450_; double v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3446_ = lean_io_mono_nanos_now();
v___x_3447_ = lean_float_of_nat(v___y_3432_);
v___x_3448_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_3449_ = lean_float_div(v___x_3447_, v___x_3448_);
v___x_3450_ = lean_float_of_nat(v___x_3446_);
v___x_3451_ = lean_float_div(v___x_3450_, v___x_3448_);
v___x_3452_ = lean_box_float(v___x_3449_);
v___x_3453_ = lean_box_float(v___x_3451_);
v___x_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3455_, 0, v_a_3445_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
lean_inc_ref(v___y_3441_);
lean_inc(v___y_3434_);
v___x_3456_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3434_, v___y_3429_, v___y_3441_, v___y_3439_, v___y_3442_, v___y_3437_, v___y_3426_, v___x_3455_, v___y_3433_, v___y_3443_, v___y_3430_, v___y_3444_, v___y_3427_, v___y_3436_, v___y_3440_, v___y_3438_, v___y_3424_, v___y_3431_, v___y_3425_);
v___y_3366_ = v___y_3424_;
v___y_3367_ = v___y_3425_;
v___y_3368_ = v___y_3427_;
v___y_3369_ = v___y_3430_;
v___y_3370_ = v___y_3428_;
v___y_3371_ = v___y_3433_;
v___y_3372_ = v___y_3431_;
v___y_3373_ = v___y_3435_;
v___y_3374_ = v___y_3436_;
v___y_3375_ = v___y_3438_;
v___y_3376_ = v___y_3440_;
v___y_3377_ = v___y_3443_;
v___y_3378_ = v___y_3444_;
v___y_3379_ = v___x_3456_;
goto v___jp_3365_;
}
v___jp_3457_:
{
lean_object* v___x_3478_; lean_object* v_a_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_3459_);
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref(v___x_3478_);
v___x_3480_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3481_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v___y_3471_, v___x_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = lean_io_mono_nanos_now();
lean_inc(v___y_3459_);
lean_inc_ref(v___y_3465_);
lean_inc(v___y_3458_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3473_);
lean_inc_ref(v___y_3469_);
lean_inc(v___y_3461_);
lean_inc_ref(v___y_3474_);
lean_inc(v___y_3464_);
lean_inc(v___y_3475_);
lean_inc_ref(v___y_3466_);
v___x_3483_ = lean_apply_12(v___y_3472_, v___y_3466_, v___y_3475_, v___y_3464_, v___y_3474_, v___y_3461_, v___y_3469_, v___y_3473_, v___y_3470_, v___y_3458_, v___y_3465_, v___y_3459_, lean_box(0));
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3483_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set_tag(v___x_3486_, 1);
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
v___y_3424_ = v___y_3458_;
v___y_3425_ = v___y_3459_;
v___y_3426_ = v___y_3460_;
v___y_3427_ = v___y_3461_;
v___y_3428_ = v___y_3462_;
v___y_3429_ = v___y_3463_;
v___y_3430_ = v___y_3464_;
v___y_3431_ = v___y_3465_;
v___y_3432_ = v___x_3482_;
v___y_3433_ = v___y_3466_;
v___y_3434_ = v___y_3467_;
v___y_3435_ = v___y_3468_;
v___y_3436_ = v___y_3469_;
v___y_3437_ = v_a_3479_;
v___y_3438_ = v___y_3470_;
v___y_3439_ = v___y_3471_;
v___y_3440_ = v___y_3473_;
v___y_3441_ = v___y_3477_;
v___y_3442_ = v___y_3476_;
v___y_3443_ = v___y_3475_;
v___y_3444_ = v___y_3474_;
v_a_3445_ = v___x_3489_;
goto v___jp_3423_;
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
v_a_3492_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3483_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3483_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set_tag(v___x_3494_, 0);
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
v___y_3424_ = v___y_3458_;
v___y_3425_ = v___y_3459_;
v___y_3426_ = v___y_3460_;
v___y_3427_ = v___y_3461_;
v___y_3428_ = v___y_3462_;
v___y_3429_ = v___y_3463_;
v___y_3430_ = v___y_3464_;
v___y_3431_ = v___y_3465_;
v___y_3432_ = v___x_3482_;
v___y_3433_ = v___y_3466_;
v___y_3434_ = v___y_3467_;
v___y_3435_ = v___y_3468_;
v___y_3436_ = v___y_3469_;
v___y_3437_ = v_a_3479_;
v___y_3438_ = v___y_3470_;
v___y_3439_ = v___y_3471_;
v___y_3440_ = v___y_3473_;
v___y_3441_ = v___y_3477_;
v___y_3442_ = v___y_3476_;
v___y_3443_ = v___y_3475_;
v___y_3444_ = v___y_3474_;
v_a_3445_ = v___x_3497_;
goto v___jp_3423_;
}
}
}
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3459_);
lean_inc_ref(v___y_3465_);
lean_inc(v___y_3458_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3473_);
lean_inc_ref(v___y_3469_);
lean_inc(v___y_3461_);
lean_inc_ref(v___y_3474_);
lean_inc(v___y_3464_);
lean_inc(v___y_3475_);
lean_inc_ref(v___y_3466_);
v___x_3501_ = lean_apply_12(v___y_3472_, v___y_3466_, v___y_3475_, v___y_3464_, v___y_3474_, v___y_3461_, v___y_3469_, v___y_3473_, v___y_3470_, v___y_3458_, v___y_3465_, v___y_3459_, lean_box(0));
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set_tag(v___x_3504_, 1);
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
v___y_3393_ = v___y_3458_;
v___y_3394_ = v___y_3459_;
v___y_3395_ = v___y_3460_;
v___y_3396_ = v___y_3461_;
v___y_3397_ = v___y_3462_;
v___y_3398_ = v___y_3463_;
v___y_3399_ = v___y_3464_;
v___y_3400_ = v___y_3465_;
v___y_3401_ = v___y_3466_;
v___y_3402_ = v___y_3467_;
v___y_3403_ = v___y_3468_;
v___y_3404_ = v___y_3469_;
v___y_3405_ = v_a_3479_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3473_;
v___y_3409_ = v___x_3500_;
v___y_3410_ = v___y_3477_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3475_;
v___y_3413_ = v___y_3474_;
v_a_3414_ = v___x_3507_;
goto v___jp_3392_;
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
v_a_3510_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3501_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3501_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set_tag(v___x_3512_, 0);
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
v___y_3393_ = v___y_3458_;
v___y_3394_ = v___y_3459_;
v___y_3395_ = v___y_3460_;
v___y_3396_ = v___y_3461_;
v___y_3397_ = v___y_3462_;
v___y_3398_ = v___y_3463_;
v___y_3399_ = v___y_3464_;
v___y_3400_ = v___y_3465_;
v___y_3401_ = v___y_3466_;
v___y_3402_ = v___y_3467_;
v___y_3403_ = v___y_3468_;
v___y_3404_ = v___y_3469_;
v___y_3405_ = v_a_3479_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3473_;
v___y_3409_ = v___x_3500_;
v___y_3410_ = v___y_3477_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3475_;
v___y_3413_ = v___y_3474_;
v_a_3414_ = v___x_3515_;
goto v___jp_3392_;
}
}
}
}
}
v___jp_3518_:
{
if (v_structures_3521_ == 0)
{
v___y_3333_ = v___y_3519_;
v___y_3334_ = v___y_3520_;
v_fixedInt_3335_ = v_fixedInt_3522_;
v_enums_3336_ = v_enums_3523_;
v___y_3337_ = v___y_3524_;
v___y_3338_ = v___y_3525_;
v___y_3339_ = v___y_3526_;
v___y_3340_ = v___y_3527_;
v___y_3341_ = v___y_3528_;
v___y_3342_ = v___y_3529_;
v___y_3343_ = v___y_3530_;
v___y_3344_ = v___y_3531_;
v___y_3345_ = v___y_3532_;
v___y_3346_ = v___y_3533_;
v___y_3347_ = v___y_3534_;
goto v___jp_3332_;
}
else
{
lean_object* v___x_3535_; lean_object* v_toCold_3536_; lean_object* v_options_3537_; uint8_t v_hasTrace_3538_; 
v___x_3535_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_toCold_3536_ = lean_ctor_get(v___y_3533_, 0);
v_options_3537_ = lean_ctor_get(v_toCold_3536_, 2);
v_hasTrace_3538_ = lean_ctor_get_uint8(v_options_3537_, sizeof(void*)*1);
if (v_hasTrace_3538_ == 0)
{
lean_object* v_run_x27_3539_; lean_object* v___x_3540_; 
v_run_x27_3539_ = lean_ctor_get(v___x_3535_, 1);
lean_inc_ref(v_run_x27_3539_);
lean_inc(v___y_3534_);
lean_inc_ref(v___y_3533_);
lean_inc(v___y_3532_);
lean_inc_ref(v___y_3531_);
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3529_);
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
lean_inc(v___y_3526_);
lean_inc(v___y_3525_);
lean_inc_ref(v___y_3524_);
v___x_3540_ = lean_apply_12(v_run_x27_3539_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, lean_box(0));
v___y_3366_ = v___y_3532_;
v___y_3367_ = v___y_3534_;
v___y_3368_ = v___y_3528_;
v___y_3369_ = v___y_3526_;
v___y_3370_ = v___y_3520_;
v___y_3371_ = v___y_3524_;
v___y_3372_ = v___y_3533_;
v___y_3373_ = v___y_3519_;
v___y_3374_ = v___y_3529_;
v___y_3375_ = v___y_3531_;
v___y_3376_ = v___y_3530_;
v___y_3377_ = v___y_3525_;
v___y_3378_ = v___y_3527_;
v___y_3379_ = v___x_3540_;
goto v___jp_3365_;
}
else
{
lean_object* v_name_3541_; lean_object* v_run_x27_3542_; lean_object* v_inheritedTraceOptions_3543_; lean_object* v___f_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v_name_3541_ = lean_ctor_get(v___x_3535_, 0);
v_run_x27_3542_ = lean_ctor_get(v___x_3535_, 1);
v_inheritedTraceOptions_3543_ = lean_ctor_get(v_toCold_3536_, 11);
lean_inc(v_name_3541_);
v___f_3544_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_3544_, 0, v_name_3541_);
v___x_3545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_3546_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_3547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_3548_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3543_, v_options_3537_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3549_ = l_Lean_trace_profiler;
v___x_3550_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_3537_, v___x_3549_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref(v___f_3544_);
lean_inc_ref(v_run_x27_3542_);
lean_inc(v___y_3534_);
lean_inc_ref(v___y_3533_);
lean_inc(v___y_3532_);
lean_inc_ref(v___y_3531_);
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3529_);
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
lean_inc(v___y_3526_);
lean_inc(v___y_3525_);
lean_inc_ref(v___y_3524_);
v___x_3551_ = lean_apply_12(v_run_x27_3542_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, lean_box(0));
v___y_3366_ = v___y_3532_;
v___y_3367_ = v___y_3534_;
v___y_3368_ = v___y_3528_;
v___y_3369_ = v___y_3526_;
v___y_3370_ = v___y_3520_;
v___y_3371_ = v___y_3524_;
v___y_3372_ = v___y_3533_;
v___y_3373_ = v___y_3519_;
v___y_3374_ = v___y_3529_;
v___y_3375_ = v___y_3531_;
v___y_3376_ = v___y_3530_;
v___y_3377_ = v___y_3525_;
v___y_3378_ = v___y_3527_;
v___y_3379_ = v___x_3551_;
goto v___jp_3365_;
}
else
{
lean_inc_ref(v_run_x27_3542_);
v___y_3458_ = v___y_3532_;
v___y_3459_ = v___y_3534_;
v___y_3460_ = v___f_3544_;
v___y_3461_ = v___y_3528_;
v___y_3462_ = v___y_3520_;
v___y_3463_ = v_hasTrace_3538_;
v___y_3464_ = v___y_3526_;
v___y_3465_ = v___y_3533_;
v___y_3466_ = v___y_3524_;
v___y_3467_ = v___x_3545_;
v___y_3468_ = v___y_3519_;
v___y_3469_ = v___y_3529_;
v___y_3470_ = v___y_3531_;
v___y_3471_ = v_options_3537_;
v___y_3472_ = v_run_x27_3542_;
v___y_3473_ = v___y_3530_;
v___y_3474_ = v___y_3527_;
v___y_3475_ = v___y_3525_;
v___y_3476_ = v___x_3548_;
v___y_3477_ = v___x_3546_;
goto v___jp_3457_;
}
}
else
{
lean_inc_ref(v_run_x27_3542_);
v___y_3458_ = v___y_3532_;
v___y_3459_ = v___y_3534_;
v___y_3460_ = v___f_3544_;
v___y_3461_ = v___y_3528_;
v___y_3462_ = v___y_3520_;
v___y_3463_ = v_hasTrace_3538_;
v___y_3464_ = v___y_3526_;
v___y_3465_ = v___y_3533_;
v___y_3466_ = v___y_3524_;
v___y_3467_ = v___x_3545_;
v___y_3468_ = v___y_3519_;
v___y_3469_ = v___y_3529_;
v___y_3470_ = v___y_3531_;
v___y_3471_ = v_options_3537_;
v___y_3472_ = v_run_x27_3542_;
v___y_3473_ = v___y_3530_;
v___y_3474_ = v___y_3527_;
v___y_3475_ = v___y_3525_;
v___y_3476_ = v___x_3548_;
v___y_3477_ = v___x_3546_;
goto v___jp_3457_;
}
}
}
}
v___jp_3552_:
{
if (lean_obj_tag(v___y_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3579_; 
v_a_3567_ = lean_ctor_get(v___y_3566_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___y_3566_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3569_ = v___y_3566_;
v_isShared_3570_ = v_isSharedCheck_3579_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___y_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3579_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
uint8_t v___x_3571_; 
v___x_3571_ = lean_unbox(v_a_3567_);
lean_dec(v_a_3567_);
if (v___x_3571_ == 0)
{
uint8_t v_structures_3572_; uint8_t v_fixedInt_3573_; uint8_t v_enums_3574_; 
lean_del_object(v___x_3569_);
v_structures_3572_ = lean_ctor_get_uint8(v___y_3557_, sizeof(void*)*3 + 5);
v_fixedInt_3573_ = lean_ctor_get_uint8(v___y_3557_, sizeof(void*)*3 + 6);
v_enums_3574_ = lean_ctor_get_uint8(v___y_3557_, sizeof(void*)*3 + 7);
v___y_3519_ = v___y_3561_;
v___y_3520_ = v___y_3557_;
v_structures_3521_ = v_structures_3572_;
v_fixedInt_3522_ = v_fixedInt_3573_;
v_enums_3523_ = v_enums_3574_;
v___y_3524_ = v___y_3553_;
v___y_3525_ = v___y_3555_;
v___y_3526_ = v___y_3564_;
v___y_3527_ = v___y_3563_;
v___y_3528_ = v___y_3558_;
v___y_3529_ = v___y_3565_;
v___y_3530_ = v___y_3556_;
v___y_3531_ = v___y_3554_;
v___y_3532_ = v___y_3560_;
v___y_3533_ = v___y_3559_;
v___y_3534_ = v___y_3562_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3575_ = lean_box(v___y_3561_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3575_);
v___x_3577_ = v___x_3569_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
return v___y_3566_;
}
}
v___jp_3580_:
{
lean_object* v___x_3603_; double v___x_3604_; double v___x_3605_; double v___x_3606_; double v___x_3607_; double v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3603_ = lean_io_mono_nanos_now();
v___x_3604_ = lean_float_of_nat(v___y_3590_);
v___x_3605_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_3606_ = lean_float_div(v___x_3604_, v___x_3605_);
v___x_3607_ = lean_float_of_nat(v___x_3603_);
v___x_3608_ = lean_float_div(v___x_3607_, v___x_3605_);
v___x_3609_ = lean_box_float(v___x_3606_);
v___x_3610_ = lean_box_float(v___x_3608_);
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v_a_3602_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
lean_inc_ref(v___y_3588_);
lean_inc(v___y_3591_);
v___x_3613_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3591_, v___y_3584_, v___y_3588_, v___y_3599_, v___y_3597_, v___y_3581_, v___y_3595_, v___x_3612_, v___y_3582_, v___y_3585_, v___y_3600_, v___y_3598_, v___y_3589_, v___y_3601_, v___y_3587_, v___y_3583_, v___y_3594_, v___y_3592_, v___y_3596_);
v___y_3553_ = v___y_3582_;
v___y_3554_ = v___y_3583_;
v___y_3555_ = v___y_3585_;
v___y_3556_ = v___y_3587_;
v___y_3557_ = v___y_3586_;
v___y_3558_ = v___y_3589_;
v___y_3559_ = v___y_3592_;
v___y_3560_ = v___y_3594_;
v___y_3561_ = v___y_3593_;
v___y_3562_ = v___y_3596_;
v___y_3563_ = v___y_3598_;
v___y_3564_ = v___y_3600_;
v___y_3565_ = v___y_3601_;
v___y_3566_ = v___x_3613_;
goto v___jp_3552_;
}
v___jp_3614_:
{
lean_object* v___x_3637_; double v___x_3638_; double v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3637_ = lean_io_get_num_heartbeats();
v___x_3638_ = lean_float_of_nat(v___y_3619_);
v___x_3639_ = lean_float_of_nat(v___x_3637_);
v___x_3640_ = lean_box_float(v___x_3638_);
v___x_3641_ = lean_box_float(v___x_3639_);
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3643_, 0, v_a_3636_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
lean_inc_ref(v___y_3623_);
lean_inc(v___y_3625_);
v___x_3644_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3625_, v___y_3618_, v___y_3623_, v___y_3633_, v___y_3631_, v___y_3615_, v___y_3629_, v___x_3643_, v___y_3616_, v___y_3620_, v___y_3634_, v___y_3632_, v___y_3624_, v___y_3635_, v___y_3622_, v___y_3617_, v___y_3628_, v___y_3626_, v___y_3630_);
v___y_3553_ = v___y_3616_;
v___y_3554_ = v___y_3617_;
v___y_3555_ = v___y_3620_;
v___y_3556_ = v___y_3622_;
v___y_3557_ = v___y_3621_;
v___y_3558_ = v___y_3624_;
v___y_3559_ = v___y_3626_;
v___y_3560_ = v___y_3628_;
v___y_3561_ = v___y_3627_;
v___y_3562_ = v___y_3630_;
v___y_3563_ = v___y_3632_;
v___y_3564_ = v___y_3634_;
v___y_3565_ = v___y_3635_;
v___y_3566_ = v___x_3644_;
goto v___jp_3552_;
}
v___jp_3645_:
{
lean_object* v___x_3666_; lean_object* v_a_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3666_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_3660_);
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref(v___x_3666_);
v___x_3668_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3669_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v___y_3664_, v___x_3668_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = lean_io_mono_nanos_now();
lean_inc(v___y_3660_);
lean_inc_ref(v___y_3656_);
lean_inc(v___y_3657_);
lean_inc_ref(v___y_3647_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3665_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3661_);
lean_inc(v___y_3663_);
lean_inc(v___y_3649_);
lean_inc_ref(v___y_3646_);
v___x_3671_ = lean_apply_12(v___y_3650_, v___y_3646_, v___y_3649_, v___y_3663_, v___y_3661_, v___y_3654_, v___y_3665_, v___y_3652_, v___y_3647_, v___y_3657_, v___y_3656_, v___y_3660_, lean_box(0));
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set_tag(v___x_3674_, 1);
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
v___y_3581_ = v_a_3667_;
v___y_3582_ = v___y_3646_;
v___y_3583_ = v___y_3647_;
v___y_3584_ = v___y_3648_;
v___y_3585_ = v___y_3649_;
v___y_3586_ = v___y_3651_;
v___y_3587_ = v___y_3652_;
v___y_3588_ = v___y_3653_;
v___y_3589_ = v___y_3654_;
v___y_3590_ = v___x_3670_;
v___y_3591_ = v___y_3655_;
v___y_3592_ = v___y_3656_;
v___y_3593_ = v___y_3658_;
v___y_3594_ = v___y_3657_;
v___y_3595_ = v___y_3659_;
v___y_3596_ = v___y_3660_;
v___y_3597_ = v___y_3662_;
v___y_3598_ = v___y_3661_;
v___y_3599_ = v___y_3664_;
v___y_3600_ = v___y_3663_;
v___y_3601_ = v___y_3665_;
v_a_3602_ = v___x_3677_;
goto v___jp_3580_;
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3671_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3671_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 0);
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
v___y_3581_ = v_a_3667_;
v___y_3582_ = v___y_3646_;
v___y_3583_ = v___y_3647_;
v___y_3584_ = v___y_3648_;
v___y_3585_ = v___y_3649_;
v___y_3586_ = v___y_3651_;
v___y_3587_ = v___y_3652_;
v___y_3588_ = v___y_3653_;
v___y_3589_ = v___y_3654_;
v___y_3590_ = v___x_3670_;
v___y_3591_ = v___y_3655_;
v___y_3592_ = v___y_3656_;
v___y_3593_ = v___y_3658_;
v___y_3594_ = v___y_3657_;
v___y_3595_ = v___y_3659_;
v___y_3596_ = v___y_3660_;
v___y_3597_ = v___y_3662_;
v___y_3598_ = v___y_3661_;
v___y_3599_ = v___y_3664_;
v___y_3600_ = v___y_3663_;
v___y_3601_ = v___y_3665_;
v_a_3602_ = v___x_3685_;
goto v___jp_3580_;
}
}
}
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3660_);
lean_inc_ref(v___y_3656_);
lean_inc(v___y_3657_);
lean_inc_ref(v___y_3647_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3665_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3661_);
lean_inc(v___y_3663_);
lean_inc(v___y_3649_);
lean_inc_ref(v___y_3646_);
v___x_3689_ = lean_apply_12(v___y_3650_, v___y_3646_, v___y_3649_, v___y_3663_, v___y_3661_, v___y_3654_, v___y_3665_, v___y_3652_, v___y_3647_, v___y_3657_, v___y_3656_, v___y_3660_, lean_box(0));
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 1);
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
v___y_3615_ = v_a_3667_;
v___y_3616_ = v___y_3646_;
v___y_3617_ = v___y_3647_;
v___y_3618_ = v___y_3648_;
v___y_3619_ = v___x_3688_;
v___y_3620_ = v___y_3649_;
v___y_3621_ = v___y_3651_;
v___y_3622_ = v___y_3652_;
v___y_3623_ = v___y_3653_;
v___y_3624_ = v___y_3654_;
v___y_3625_ = v___y_3655_;
v___y_3626_ = v___y_3656_;
v___y_3627_ = v___y_3658_;
v___y_3628_ = v___y_3657_;
v___y_3629_ = v___y_3659_;
v___y_3630_ = v___y_3660_;
v___y_3631_ = v___y_3662_;
v___y_3632_ = v___y_3661_;
v___y_3633_ = v___y_3664_;
v___y_3634_ = v___y_3663_;
v___y_3635_ = v___y_3665_;
v_a_3636_ = v___x_3695_;
goto v___jp_3614_;
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
v_a_3698_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3689_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3689_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
lean_ctor_set_tag(v___x_3700_, 0);
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
v___y_3615_ = v_a_3667_;
v___y_3616_ = v___y_3646_;
v___y_3617_ = v___y_3647_;
v___y_3618_ = v___y_3648_;
v___y_3619_ = v___x_3688_;
v___y_3620_ = v___y_3649_;
v___y_3621_ = v___y_3651_;
v___y_3622_ = v___y_3652_;
v___y_3623_ = v___y_3653_;
v___y_3624_ = v___y_3654_;
v___y_3625_ = v___y_3655_;
v___y_3626_ = v___y_3656_;
v___y_3627_ = v___y_3658_;
v___y_3628_ = v___y_3657_;
v___y_3629_ = v___y_3659_;
v___y_3630_ = v___y_3660_;
v___y_3631_ = v___y_3662_;
v___y_3632_ = v___y_3661_;
v___y_3633_ = v___y_3664_;
v___y_3634_ = v___y_3663_;
v___y_3635_ = v___y_3665_;
v_a_3636_ = v___x_3703_;
goto v___jp_3614_;
}
}
}
}
}
v___jp_3706_:
{
if (lean_obj_tag(v___y_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3751_; 
v_a_3720_ = lean_ctor_get(v___y_3719_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___y_3719_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3722_ = v___y_3719_;
v_isShared_3723_ = v_isSharedCheck_3751_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___y_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3751_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
uint8_t v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = 1;
v___x_3725_ = lean_unbox(v_a_3720_);
lean_dec(v_a_3720_);
if (v___x_3725_ == 0)
{
uint8_t v_epr_3726_; 
lean_del_object(v___x_3722_);
v_epr_3726_ = lean_ctor_get_uint8(v___y_3713_, sizeof(void*)*3 + 12);
if (v_epr_3726_ == 0)
{
uint8_t v_structures_3727_; uint8_t v_fixedInt_3728_; uint8_t v_enums_3729_; 
v_structures_3727_ = lean_ctor_get_uint8(v___y_3713_, sizeof(void*)*3 + 5);
v_fixedInt_3728_ = lean_ctor_get_uint8(v___y_3713_, sizeof(void*)*3 + 6);
v_enums_3729_ = lean_ctor_get_uint8(v___y_3713_, sizeof(void*)*3 + 7);
v___y_3519_ = v___x_3724_;
v___y_3520_ = v___y_3713_;
v_structures_3521_ = v_structures_3727_;
v_fixedInt_3522_ = v_fixedInt_3728_;
v_enums_3523_ = v_enums_3729_;
v___y_3524_ = v___y_3708_;
v___y_3525_ = v___y_3710_;
v___y_3526_ = v___y_3716_;
v___y_3527_ = v___y_3715_;
v___y_3528_ = v___y_3714_;
v___y_3529_ = v___y_3718_;
v___y_3530_ = v___y_3712_;
v___y_3531_ = v___y_3709_;
v___y_3532_ = v___y_3707_;
v___y_3533_ = v___y_3717_;
v___y_3534_ = v___y_3711_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3730_; lean_object* v_toCold_3731_; lean_object* v_options_3732_; uint8_t v_hasTrace_3733_; 
v___x_3730_ = l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass;
v_toCold_3731_ = lean_ctor_get(v___y_3717_, 0);
v_options_3732_ = lean_ctor_get(v_toCold_3731_, 2);
v_hasTrace_3733_ = lean_ctor_get_uint8(v_options_3732_, sizeof(void*)*1);
if (v_hasTrace_3733_ == 0)
{
lean_object* v_run_x27_3734_; lean_object* v___x_3735_; 
v_run_x27_3734_ = lean_ctor_get(v___x_3730_, 1);
lean_inc_ref(v_run_x27_3734_);
lean_inc(v___y_3711_);
lean_inc_ref(v___y_3717_);
lean_inc(v___y_3707_);
lean_inc_ref(v___y_3709_);
lean_inc(v___y_3712_);
lean_inc_ref(v___y_3718_);
lean_inc(v___y_3714_);
lean_inc_ref(v___y_3715_);
lean_inc(v___y_3716_);
lean_inc(v___y_3710_);
lean_inc_ref(v___y_3708_);
v___x_3735_ = lean_apply_12(v_run_x27_3734_, v___y_3708_, v___y_3710_, v___y_3716_, v___y_3715_, v___y_3714_, v___y_3718_, v___y_3712_, v___y_3709_, v___y_3707_, v___y_3717_, v___y_3711_, lean_box(0));
v___y_3553_ = v___y_3708_;
v___y_3554_ = v___y_3709_;
v___y_3555_ = v___y_3710_;
v___y_3556_ = v___y_3712_;
v___y_3557_ = v___y_3713_;
v___y_3558_ = v___y_3714_;
v___y_3559_ = v___y_3717_;
v___y_3560_ = v___y_3707_;
v___y_3561_ = v___x_3724_;
v___y_3562_ = v___y_3711_;
v___y_3563_ = v___y_3715_;
v___y_3564_ = v___y_3716_;
v___y_3565_ = v___y_3718_;
v___y_3566_ = v___x_3735_;
goto v___jp_3552_;
}
else
{
lean_object* v_name_3736_; lean_object* v_run_x27_3737_; lean_object* v_inheritedTraceOptions_3738_; lean_object* v___f_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v_name_3736_ = lean_ctor_get(v___x_3730_, 0);
v_run_x27_3737_ = lean_ctor_get(v___x_3730_, 1);
v_inheritedTraceOptions_3738_ = lean_ctor_get(v_toCold_3731_, 11);
lean_inc(v_name_3736_);
v___f_3739_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_3739_, 0, v_name_3736_);
v___x_3740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_3741_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_3742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_3743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3738_, v_options_3732_, v___x_3742_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3744_ = l_Lean_trace_profiler;
v___x_3745_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_3732_, v___x_3744_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; 
lean_dec_ref(v___f_3739_);
lean_inc_ref(v_run_x27_3737_);
lean_inc(v___y_3711_);
lean_inc_ref(v___y_3717_);
lean_inc(v___y_3707_);
lean_inc_ref(v___y_3709_);
lean_inc(v___y_3712_);
lean_inc_ref(v___y_3718_);
lean_inc(v___y_3714_);
lean_inc_ref(v___y_3715_);
lean_inc(v___y_3716_);
lean_inc(v___y_3710_);
lean_inc_ref(v___y_3708_);
v___x_3746_ = lean_apply_12(v_run_x27_3737_, v___y_3708_, v___y_3710_, v___y_3716_, v___y_3715_, v___y_3714_, v___y_3718_, v___y_3712_, v___y_3709_, v___y_3707_, v___y_3717_, v___y_3711_, lean_box(0));
v___y_3553_ = v___y_3708_;
v___y_3554_ = v___y_3709_;
v___y_3555_ = v___y_3710_;
v___y_3556_ = v___y_3712_;
v___y_3557_ = v___y_3713_;
v___y_3558_ = v___y_3714_;
v___y_3559_ = v___y_3717_;
v___y_3560_ = v___y_3707_;
v___y_3561_ = v___x_3724_;
v___y_3562_ = v___y_3711_;
v___y_3563_ = v___y_3715_;
v___y_3564_ = v___y_3716_;
v___y_3565_ = v___y_3718_;
v___y_3566_ = v___x_3746_;
goto v___jp_3552_;
}
else
{
lean_inc_ref(v_run_x27_3737_);
v___y_3646_ = v___y_3708_;
v___y_3647_ = v___y_3709_;
v___y_3648_ = v_hasTrace_3733_;
v___y_3649_ = v___y_3710_;
v___y_3650_ = v_run_x27_3737_;
v___y_3651_ = v___y_3713_;
v___y_3652_ = v___y_3712_;
v___y_3653_ = v___x_3741_;
v___y_3654_ = v___y_3714_;
v___y_3655_ = v___x_3740_;
v___y_3656_ = v___y_3717_;
v___y_3657_ = v___y_3707_;
v___y_3658_ = v___x_3724_;
v___y_3659_ = v___f_3739_;
v___y_3660_ = v___y_3711_;
v___y_3661_ = v___y_3715_;
v___y_3662_ = v___x_3743_;
v___y_3663_ = v___y_3716_;
v___y_3664_ = v_options_3732_;
v___y_3665_ = v___y_3718_;
goto v___jp_3645_;
}
}
else
{
lean_inc_ref(v_run_x27_3737_);
v___y_3646_ = v___y_3708_;
v___y_3647_ = v___y_3709_;
v___y_3648_ = v_hasTrace_3733_;
v___y_3649_ = v___y_3710_;
v___y_3650_ = v_run_x27_3737_;
v___y_3651_ = v___y_3713_;
v___y_3652_ = v___y_3712_;
v___y_3653_ = v___x_3741_;
v___y_3654_ = v___y_3714_;
v___y_3655_ = v___x_3740_;
v___y_3656_ = v___y_3717_;
v___y_3657_ = v___y_3707_;
v___y_3658_ = v___x_3724_;
v___y_3659_ = v___f_3739_;
v___y_3660_ = v___y_3711_;
v___y_3661_ = v___y_3715_;
v___y_3662_ = v___x_3743_;
v___y_3663_ = v___y_3716_;
v___y_3664_ = v_options_3732_;
v___y_3665_ = v___y_3718_;
goto v___jp_3645_;
}
}
}
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3747_ = lean_box(v___x_3724_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3747_);
v___x_3749_ = v___x_3722_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
return v___y_3719_;
}
}
v___jp_3752_:
{
lean_object* v___x_3774_; double v___x_3775_; double v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3774_ = lean_io_get_num_heartbeats();
v___x_3775_ = lean_float_of_nat(v___y_3765_);
v___x_3776_ = lean_float_of_nat(v___x_3774_);
v___x_3777_ = lean_box_float(v___x_3775_);
v___x_3778_ = lean_box_float(v___x_3776_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v_a_3773_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
lean_inc_ref(v___y_3756_);
lean_inc(v___y_3766_);
v___x_3781_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3766_, v___y_3768_, v___y_3756_, v___y_3760_, v___y_3762_, v___y_3767_, v___y_3755_, v___x_3780_, v___y_3753_, v___y_3757_, v___y_3771_, v___y_3770_, v___y_3761_, v___y_3772_, v___y_3759_, v___y_3754_, v___y_3764_, v___y_3763_, v___y_3769_);
v___y_3707_ = v___y_3764_;
v___y_3708_ = v___y_3753_;
v___y_3709_ = v___y_3754_;
v___y_3710_ = v___y_3757_;
v___y_3711_ = v___y_3769_;
v___y_3712_ = v___y_3759_;
v___y_3713_ = v___y_3758_;
v___y_3714_ = v___y_3761_;
v___y_3715_ = v___y_3770_;
v___y_3716_ = v___y_3771_;
v___y_3717_ = v___y_3763_;
v___y_3718_ = v___y_3772_;
v___y_3719_ = v___x_3781_;
goto v___jp_3706_;
}
v___jp_3782_:
{
lean_object* v___x_3804_; double v___x_3805_; double v___x_3806_; double v___x_3807_; double v___x_3808_; double v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3804_ = lean_io_mono_nanos_now();
v___x_3805_ = lean_float_of_nat(v___y_3794_);
v___x_3806_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_3807_ = lean_float_div(v___x_3805_, v___x_3806_);
v___x_3808_ = lean_float_of_nat(v___x_3804_);
v___x_3809_ = lean_float_div(v___x_3808_, v___x_3806_);
v___x_3810_ = lean_box_float(v___x_3807_);
v___x_3811_ = lean_box_float(v___x_3809_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v_a_3803_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
lean_inc_ref(v___y_3786_);
lean_inc(v___y_3796_);
v___x_3814_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3796_, v___y_3798_, v___y_3786_, v___y_3790_, v___y_3792_, v___y_3797_, v___y_3785_, v___x_3813_, v___y_3783_, v___y_3787_, v___y_3801_, v___y_3800_, v___y_3791_, v___y_3802_, v___y_3789_, v___y_3784_, v___y_3795_, v___y_3793_, v___y_3799_);
v___y_3707_ = v___y_3795_;
v___y_3708_ = v___y_3783_;
v___y_3709_ = v___y_3784_;
v___y_3710_ = v___y_3787_;
v___y_3711_ = v___y_3799_;
v___y_3712_ = v___y_3789_;
v___y_3713_ = v___y_3788_;
v___y_3714_ = v___y_3791_;
v___y_3715_ = v___y_3800_;
v___y_3716_ = v___y_3801_;
v___y_3717_ = v___y_3793_;
v___y_3718_ = v___y_3802_;
v___y_3719_ = v___x_3814_;
goto v___jp_3706_;
}
v___jp_3815_:
{
lean_object* v___x_3835_; lean_object* v_a_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3835_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_3831_);
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3835_);
v___x_3837_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3838_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v___y_3823_, v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = lean_io_mono_nanos_now();
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3826_);
lean_inc(v___y_3828_);
lean_inc_ref(v___y_3817_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3834_);
lean_inc(v___y_3824_);
lean_inc_ref(v___y_3832_);
lean_inc(v___y_3833_);
lean_inc(v___y_3820_);
lean_inc_ref(v___y_3816_);
v___x_3840_ = lean_apply_12(v___y_3827_, v___y_3816_, v___y_3820_, v___y_3833_, v___y_3832_, v___y_3824_, v___y_3834_, v___y_3822_, v___y_3817_, v___y_3828_, v___y_3826_, v___y_3831_, lean_box(0));
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 1);
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
v___y_3783_ = v___y_3816_;
v___y_3784_ = v___y_3817_;
v___y_3785_ = v___y_3818_;
v___y_3786_ = v___y_3819_;
v___y_3787_ = v___y_3820_;
v___y_3788_ = v___y_3821_;
v___y_3789_ = v___y_3822_;
v___y_3790_ = v___y_3823_;
v___y_3791_ = v___y_3824_;
v___y_3792_ = v___y_3825_;
v___y_3793_ = v___y_3826_;
v___y_3794_ = v___x_3839_;
v___y_3795_ = v___y_3828_;
v___y_3796_ = v___y_3829_;
v___y_3797_ = v_a_3836_;
v___y_3798_ = v___y_3830_;
v___y_3799_ = v___y_3831_;
v___y_3800_ = v___y_3832_;
v___y_3801_ = v___y_3833_;
v___y_3802_ = v___y_3834_;
v_a_3803_ = v___x_3846_;
goto v___jp_3782_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_a_3849_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3840_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3840_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set_tag(v___x_3851_, 0);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
v___y_3783_ = v___y_3816_;
v___y_3784_ = v___y_3817_;
v___y_3785_ = v___y_3818_;
v___y_3786_ = v___y_3819_;
v___y_3787_ = v___y_3820_;
v___y_3788_ = v___y_3821_;
v___y_3789_ = v___y_3822_;
v___y_3790_ = v___y_3823_;
v___y_3791_ = v___y_3824_;
v___y_3792_ = v___y_3825_;
v___y_3793_ = v___y_3826_;
v___y_3794_ = v___x_3839_;
v___y_3795_ = v___y_3828_;
v___y_3796_ = v___y_3829_;
v___y_3797_ = v_a_3836_;
v___y_3798_ = v___y_3830_;
v___y_3799_ = v___y_3831_;
v___y_3800_ = v___y_3832_;
v___y_3801_ = v___y_3833_;
v___y_3802_ = v___y_3834_;
v_a_3803_ = v___x_3854_;
goto v___jp_3782_;
}
}
}
}
else
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3826_);
lean_inc(v___y_3828_);
lean_inc_ref(v___y_3817_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3834_);
lean_inc(v___y_3824_);
lean_inc_ref(v___y_3832_);
lean_inc(v___y_3833_);
lean_inc(v___y_3820_);
lean_inc_ref(v___y_3816_);
v___x_3858_ = lean_apply_12(v___y_3827_, v___y_3816_, v___y_3820_, v___y_3833_, v___y_3832_, v___y_3824_, v___y_3834_, v___y_3822_, v___y_3817_, v___y_3828_, v___y_3826_, v___y_3831_, lean_box(0));
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3858_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3858_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set_tag(v___x_3861_, 1);
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
v___y_3753_ = v___y_3816_;
v___y_3754_ = v___y_3817_;
v___y_3755_ = v___y_3818_;
v___y_3756_ = v___y_3819_;
v___y_3757_ = v___y_3820_;
v___y_3758_ = v___y_3821_;
v___y_3759_ = v___y_3822_;
v___y_3760_ = v___y_3823_;
v___y_3761_ = v___y_3824_;
v___y_3762_ = v___y_3825_;
v___y_3763_ = v___y_3826_;
v___y_3764_ = v___y_3828_;
v___y_3765_ = v___x_3857_;
v___y_3766_ = v___y_3829_;
v___y_3767_ = v_a_3836_;
v___y_3768_ = v___y_3830_;
v___y_3769_ = v___y_3831_;
v___y_3770_ = v___y_3832_;
v___y_3771_ = v___y_3833_;
v___y_3772_ = v___y_3834_;
v_a_3773_ = v___x_3864_;
goto v___jp_3752_;
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
v_a_3867_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3858_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3858_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
lean_ctor_set_tag(v___x_3869_, 0);
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
v___y_3753_ = v___y_3816_;
v___y_3754_ = v___y_3817_;
v___y_3755_ = v___y_3818_;
v___y_3756_ = v___y_3819_;
v___y_3757_ = v___y_3820_;
v___y_3758_ = v___y_3821_;
v___y_3759_ = v___y_3822_;
v___y_3760_ = v___y_3823_;
v___y_3761_ = v___y_3824_;
v___y_3762_ = v___y_3825_;
v___y_3763_ = v___y_3826_;
v___y_3764_ = v___y_3828_;
v___y_3765_ = v___x_3857_;
v___y_3766_ = v___y_3829_;
v___y_3767_ = v_a_3836_;
v___y_3768_ = v___y_3830_;
v___y_3769_ = v___y_3831_;
v___y_3770_ = v___y_3832_;
v___y_3771_ = v___y_3833_;
v___y_3772_ = v___y_3834_;
v_a_3773_ = v___x_3872_;
goto v___jp_3752_;
}
}
}
}
}
v___jp_3875_:
{
lean_object* v___x_3888_; lean_object* v_toCold_3889_; lean_object* v_options_3890_; uint8_t v_hasTrace_3891_; 
v___x_3888_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v_toCold_3889_ = lean_ctor_get(v___y_3886_, 0);
v_options_3890_ = lean_ctor_get(v_toCold_3889_, 2);
v_hasTrace_3891_ = lean_ctor_get_uint8(v_options_3890_, sizeof(void*)*1);
if (v_hasTrace_3891_ == 0)
{
lean_object* v_run_x27_3892_; lean_object* v___x_3893_; 
v_run_x27_3892_ = lean_ctor_get(v___x_3888_, 1);
lean_inc_ref(v_run_x27_3892_);
lean_inc(v___y_3887_);
lean_inc_ref(v___y_3886_);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3880_);
lean_inc(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
v___x_3893_ = lean_apply_12(v_run_x27_3892_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, lean_box(0));
v___y_3707_ = v___y_3885_;
v___y_3708_ = v___y_3877_;
v___y_3709_ = v___y_3884_;
v___y_3710_ = v___y_3878_;
v___y_3711_ = v___y_3887_;
v___y_3712_ = v___y_3883_;
v___y_3713_ = v___y_3876_;
v___y_3714_ = v___y_3881_;
v___y_3715_ = v___y_3880_;
v___y_3716_ = v___y_3879_;
v___y_3717_ = v___y_3886_;
v___y_3718_ = v___y_3882_;
v___y_3719_ = v___x_3893_;
goto v___jp_3706_;
}
else
{
lean_object* v_name_3894_; lean_object* v_run_x27_3895_; lean_object* v_inheritedTraceOptions_3896_; lean_object* v___f_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v_name_3894_ = lean_ctor_get(v___x_3888_, 0);
v_run_x27_3895_ = lean_ctor_get(v___x_3888_, 1);
v_inheritedTraceOptions_3896_ = lean_ctor_get(v_toCold_3889_, 11);
lean_inc(v_name_3894_);
v___f_3897_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_3897_, 0, v_name_3894_);
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_3899_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_3900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_3901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3896_, v_options_3890_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = l_Lean_trace_profiler;
v___x_3903_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_3890_, v___x_3902_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; 
lean_dec_ref(v___f_3897_);
lean_inc_ref(v_run_x27_3895_);
lean_inc(v___y_3887_);
lean_inc_ref(v___y_3886_);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3880_);
lean_inc(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
v___x_3904_ = lean_apply_12(v_run_x27_3895_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, lean_box(0));
v___y_3707_ = v___y_3885_;
v___y_3708_ = v___y_3877_;
v___y_3709_ = v___y_3884_;
v___y_3710_ = v___y_3878_;
v___y_3711_ = v___y_3887_;
v___y_3712_ = v___y_3883_;
v___y_3713_ = v___y_3876_;
v___y_3714_ = v___y_3881_;
v___y_3715_ = v___y_3880_;
v___y_3716_ = v___y_3879_;
v___y_3717_ = v___y_3886_;
v___y_3718_ = v___y_3882_;
v___y_3719_ = v___x_3904_;
goto v___jp_3706_;
}
else
{
lean_inc_ref(v_run_x27_3895_);
v___y_3816_ = v___y_3877_;
v___y_3817_ = v___y_3884_;
v___y_3818_ = v___f_3897_;
v___y_3819_ = v___x_3899_;
v___y_3820_ = v___y_3878_;
v___y_3821_ = v___y_3876_;
v___y_3822_ = v___y_3883_;
v___y_3823_ = v_options_3890_;
v___y_3824_ = v___y_3881_;
v___y_3825_ = v___x_3901_;
v___y_3826_ = v___y_3886_;
v___y_3827_ = v_run_x27_3895_;
v___y_3828_ = v___y_3885_;
v___y_3829_ = v___x_3898_;
v___y_3830_ = v_hasTrace_3891_;
v___y_3831_ = v___y_3887_;
v___y_3832_ = v___y_3880_;
v___y_3833_ = v___y_3879_;
v___y_3834_ = v___y_3882_;
goto v___jp_3815_;
}
}
else
{
lean_inc_ref(v_run_x27_3895_);
v___y_3816_ = v___y_3877_;
v___y_3817_ = v___y_3884_;
v___y_3818_ = v___f_3897_;
v___y_3819_ = v___x_3899_;
v___y_3820_ = v___y_3878_;
v___y_3821_ = v___y_3876_;
v___y_3822_ = v___y_3883_;
v___y_3823_ = v_options_3890_;
v___y_3824_ = v___y_3881_;
v___y_3825_ = v___x_3901_;
v___y_3826_ = v___y_3886_;
v___y_3827_ = v_run_x27_3895_;
v___y_3828_ = v___y_3885_;
v___y_3829_ = v___x_3898_;
v___y_3830_ = v_hasTrace_3891_;
v___y_3831_ = v___y_3887_;
v___y_3832_ = v___y_3880_;
v___y_3833_ = v___y_3879_;
v___y_3834_ = v___y_3882_;
goto v___jp_3815_;
}
}
}
v___jp_3905_:
{
if (lean_obj_tag(v___y_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3929_; 
v_a_3920_ = lean_ctor_get(v___y_3919_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___y_3919_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3922_ = v___y_3919_;
v_isShared_3923_ = v_isSharedCheck_3929_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___y_3919_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3929_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
uint8_t v___x_3924_; 
v___x_3924_ = lean_unbox(v_a_3920_);
lean_dec(v_a_3920_);
if (v___x_3924_ == 0)
{
lean_del_object(v___x_3922_);
v___y_3876_ = v___y_3910_;
v___y_3877_ = v___y_3909_;
v___y_3878_ = v___y_3913_;
v___y_3879_ = v___y_3906_;
v___y_3880_ = v___y_3916_;
v___y_3881_ = v___y_3911_;
v___y_3882_ = v___y_3907_;
v___y_3883_ = v___y_3914_;
v___y_3884_ = v___y_3917_;
v___y_3885_ = v___y_3912_;
v___y_3886_ = v___y_3918_;
v___y_3887_ = v___y_3915_;
goto v___jp_3875_;
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3927_; 
v___x_3925_ = lean_box(v___y_3908_);
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 0, v___x_3925_);
v___x_3927_ = v___x_3922_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
return v___y_3919_;
}
}
v___jp_3930_:
{
lean_object* v___x_3953_; double v___x_3954_; double v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3953_ = lean_io_get_num_heartbeats();
v___x_3954_ = lean_float_of_nat(v___y_3934_);
v___x_3955_ = lean_float_of_nat(v___x_3953_);
v___x_3956_ = lean_box_float(v___x_3954_);
v___x_3957_ = lean_box_float(v___x_3955_);
v___x_3958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3956_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
v___x_3959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3959_, 0, v_a_3952_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
lean_inc_ref(v___y_3951_);
lean_inc(v___y_3943_);
v___x_3960_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3943_, v___y_3949_, v___y_3951_, v___y_3947_, v___y_3939_, v___y_3935_, v___y_3950_, v___x_3959_, v___y_3937_, v___y_3941_, v___y_3932_, v___y_3945_, v___y_3938_, v___y_3931_, v___y_3942_, v___y_3946_, v___y_3940_, v___y_3948_, v___y_3944_);
v___y_3906_ = v___y_3932_;
v___y_3907_ = v___y_3931_;
v___y_3908_ = v___y_3933_;
v___y_3909_ = v___y_3937_;
v___y_3910_ = v___y_3936_;
v___y_3911_ = v___y_3938_;
v___y_3912_ = v___y_3940_;
v___y_3913_ = v___y_3941_;
v___y_3914_ = v___y_3942_;
v___y_3915_ = v___y_3944_;
v___y_3916_ = v___y_3945_;
v___y_3917_ = v___y_3946_;
v___y_3918_ = v___y_3948_;
v___y_3919_ = v___x_3960_;
goto v___jp_3905_;
}
v___jp_3961_:
{
lean_object* v___x_3984_; double v___x_3985_; double v___x_3986_; double v___x_3987_; double v___x_3988_; double v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3984_ = lean_io_mono_nanos_now();
v___x_3985_ = lean_float_of_nat(v___y_3966_);
v___x_3986_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_3987_ = lean_float_div(v___x_3985_, v___x_3986_);
v___x_3988_ = lean_float_of_nat(v___x_3984_);
v___x_3989_ = lean_float_div(v___x_3988_, v___x_3986_);
v___x_3990_ = lean_box_float(v___x_3987_);
v___x_3991_ = lean_box_float(v___x_3989_);
v___x_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3990_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v_a_3983_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
lean_inc_ref(v___y_3982_);
lean_inc(v___y_3974_);
v___x_3994_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_3974_, v___y_3980_, v___y_3982_, v___y_3978_, v___y_3970_, v___y_3965_, v___y_3981_, v___x_3993_, v___y_3968_, v___y_3972_, v___y_3963_, v___y_3976_, v___y_3969_, v___y_3962_, v___y_3973_, v___y_3977_, v___y_3971_, v___y_3979_, v___y_3975_);
v___y_3906_ = v___y_3963_;
v___y_3907_ = v___y_3962_;
v___y_3908_ = v___y_3964_;
v___y_3909_ = v___y_3968_;
v___y_3910_ = v___y_3967_;
v___y_3911_ = v___y_3969_;
v___y_3912_ = v___y_3971_;
v___y_3913_ = v___y_3972_;
v___y_3914_ = v___y_3973_;
v___y_3915_ = v___y_3975_;
v___y_3916_ = v___y_3976_;
v___y_3917_ = v___y_3977_;
v___y_3918_ = v___y_3979_;
v___y_3919_ = v___x_3994_;
goto v___jp_3905_;
}
v___jp_3995_:
{
lean_object* v___x_4016_; lean_object* v_a_4017_; lean_object* v___x_4018_; uint8_t v___x_4019_; 
v___x_4016_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v___y_4008_);
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref(v___x_4016_);
v___x_4018_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4019_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v___y_4011_, v___x_4018_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_io_mono_nanos_now();
lean_inc(v___y_4008_);
lean_inc_ref(v___y_4012_);
lean_inc(v___y_4004_);
lean_inc_ref(v___y_4010_);
lean_inc(v___y_4006_);
lean_inc_ref(v___y_3996_);
lean_inc(v___y_4001_);
lean_inc_ref(v___y_4009_);
lean_inc(v___y_3997_);
lean_inc(v___y_4005_);
lean_inc_ref(v___y_4000_);
v___x_4021_ = lean_apply_12(v___y_4003_, v___y_4000_, v___y_4005_, v___y_3997_, v___y_4009_, v___y_4001_, v___y_3996_, v___y_4006_, v___y_4010_, v___y_4004_, v___y_4012_, v___y_4008_, lean_box(0));
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
lean_ctor_set_tag(v___x_4024_, 1);
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
v___y_3962_ = v___y_3996_;
v___y_3963_ = v___y_3997_;
v___y_3964_ = v___y_3998_;
v___y_3965_ = v_a_4017_;
v___y_3966_ = v___x_4020_;
v___y_3967_ = v___y_3999_;
v___y_3968_ = v___y_4000_;
v___y_3969_ = v___y_4001_;
v___y_3970_ = v___y_4002_;
v___y_3971_ = v___y_4004_;
v___y_3972_ = v___y_4005_;
v___y_3973_ = v___y_4006_;
v___y_3974_ = v___y_4007_;
v___y_3975_ = v___y_4008_;
v___y_3976_ = v___y_4009_;
v___y_3977_ = v___y_4010_;
v___y_3978_ = v___y_4011_;
v___y_3979_ = v___y_4012_;
v___y_3980_ = v___y_4013_;
v___y_3981_ = v___y_4014_;
v___y_3982_ = v___y_4015_;
v_a_3983_ = v___x_4027_;
goto v___jp_3961_;
}
}
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
v_a_4030_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4021_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4021_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set_tag(v___x_4032_, 0);
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
v___y_3962_ = v___y_3996_;
v___y_3963_ = v___y_3997_;
v___y_3964_ = v___y_3998_;
v___y_3965_ = v_a_4017_;
v___y_3966_ = v___x_4020_;
v___y_3967_ = v___y_3999_;
v___y_3968_ = v___y_4000_;
v___y_3969_ = v___y_4001_;
v___y_3970_ = v___y_4002_;
v___y_3971_ = v___y_4004_;
v___y_3972_ = v___y_4005_;
v___y_3973_ = v___y_4006_;
v___y_3974_ = v___y_4007_;
v___y_3975_ = v___y_4008_;
v___y_3976_ = v___y_4009_;
v___y_3977_ = v___y_4010_;
v___y_3978_ = v___y_4011_;
v___y_3979_ = v___y_4012_;
v___y_3980_ = v___y_4013_;
v___y_3981_ = v___y_4014_;
v___y_3982_ = v___y_4015_;
v_a_3983_ = v___x_4035_;
goto v___jp_3961_;
}
}
}
}
else
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4008_);
lean_inc_ref(v___y_4012_);
lean_inc(v___y_4004_);
lean_inc_ref(v___y_4010_);
lean_inc(v___y_4006_);
lean_inc_ref(v___y_3996_);
lean_inc(v___y_4001_);
lean_inc_ref(v___y_4009_);
lean_inc(v___y_3997_);
lean_inc(v___y_4005_);
lean_inc_ref(v___y_4000_);
v___x_4039_ = lean_apply_12(v___y_4003_, v___y_4000_, v___y_4005_, v___y_3997_, v___y_4009_, v___y_4001_, v___y_3996_, v___y_4006_, v___y_4010_, v___y_4004_, v___y_4012_, v___y_4008_, lean_box(0));
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4039_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4039_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set_tag(v___x_4042_, 1);
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
v___y_3931_ = v___y_3996_;
v___y_3932_ = v___y_3997_;
v___y_3933_ = v___y_3998_;
v___y_3934_ = v___x_4038_;
v___y_3935_ = v_a_4017_;
v___y_3936_ = v___y_3999_;
v___y_3937_ = v___y_4000_;
v___y_3938_ = v___y_4001_;
v___y_3939_ = v___y_4002_;
v___y_3940_ = v___y_4004_;
v___y_3941_ = v___y_4005_;
v___y_3942_ = v___y_4006_;
v___y_3943_ = v___y_4007_;
v___y_3944_ = v___y_4008_;
v___y_3945_ = v___y_4009_;
v___y_3946_ = v___y_4010_;
v___y_3947_ = v___y_4011_;
v___y_3948_ = v___y_4012_;
v___y_3949_ = v___y_4013_;
v___y_3950_ = v___y_4014_;
v___y_3951_ = v___y_4015_;
v_a_3952_ = v___x_4045_;
goto v___jp_3930_;
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
v_a_4048_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4039_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4039_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set_tag(v___x_4050_, 0);
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
v___y_3931_ = v___y_3996_;
v___y_3932_ = v___y_3997_;
v___y_3933_ = v___y_3998_;
v___y_3934_ = v___x_4038_;
v___y_3935_ = v_a_4017_;
v___y_3936_ = v___y_3999_;
v___y_3937_ = v___y_4000_;
v___y_3938_ = v___y_4001_;
v___y_3939_ = v___y_4002_;
v___y_3940_ = v___y_4004_;
v___y_3941_ = v___y_4005_;
v___y_3942_ = v___y_4006_;
v___y_3943_ = v___y_4007_;
v___y_3944_ = v___y_4008_;
v___y_3945_ = v___y_4009_;
v___y_3946_ = v___y_4010_;
v___y_3947_ = v___y_4011_;
v___y_3948_ = v___y_4012_;
v___y_3949_ = v___y_4013_;
v___y_3950_ = v___y_4014_;
v___y_3951_ = v___y_4015_;
v_a_3952_ = v___x_4053_;
goto v___jp_3930_;
}
}
}
}
}
v___jp_4056_:
{
lean_object* v___x_4069_; lean_object* v_toCold_4070_; lean_object* v_options_4071_; lean_object* v_name_4072_; lean_object* v_run_x27_4073_; lean_object* v_inheritedTraceOptions_4074_; uint8_t v_hasTrace_4075_; uint8_t v___x_4076_; 
v___x_4069_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_toCold_4070_ = lean_ctor_get(v___y_4068_, 0);
v_options_4071_ = lean_ctor_get(v_toCold_4070_, 2);
v_name_4072_ = lean_ctor_get(v___x_4069_, 0);
v_run_x27_4073_ = lean_ctor_get(v___x_4069_, 1);
v_inheritedTraceOptions_4074_ = lean_ctor_get(v_toCold_4070_, 11);
v_hasTrace_4075_ = lean_ctor_get_uint8(v_options_4071_, sizeof(void*)*1);
v___x_4076_ = 1;
if (v_hasTrace_4075_ == 0)
{
lean_object* v___x_4077_; 
lean_inc_ref(v_run_x27_4073_);
lean_inc(v___y_4065_);
lean_inc_ref(v___y_4068_);
lean_inc(v___y_4062_);
lean_inc_ref(v___y_4067_);
lean_inc(v___y_4064_);
lean_inc_ref(v___y_4058_);
lean_inc(v___y_4061_);
lean_inc_ref(v___y_4066_);
lean_inc(v___y_4057_);
lean_inc(v___y_4063_);
lean_inc_ref(v___y_4059_);
v___x_4077_ = lean_apply_12(v_run_x27_4073_, v___y_4059_, v___y_4063_, v___y_4057_, v___y_4066_, v___y_4061_, v___y_4058_, v___y_4064_, v___y_4067_, v___y_4062_, v___y_4068_, v___y_4065_, lean_box(0));
v___y_3906_ = v___y_4057_;
v___y_3907_ = v___y_4058_;
v___y_3908_ = v___x_4076_;
v___y_3909_ = v___y_4059_;
v___y_3910_ = v___y_4060_;
v___y_3911_ = v___y_4061_;
v___y_3912_ = v___y_4062_;
v___y_3913_ = v___y_4063_;
v___y_3914_ = v___y_4064_;
v___y_3915_ = v___y_4065_;
v___y_3916_ = v___y_4066_;
v___y_3917_ = v___y_4067_;
v___y_3918_ = v___y_4068_;
v___y_3919_ = v___x_4077_;
goto v___jp_3905_;
}
else
{
lean_object* v___f_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; 
lean_inc(v_name_4072_);
v___f_4078_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_4078_, 0, v_name_4072_);
v___x_4079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_4080_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_4081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_4082_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4074_, v_options_4071_, v___x_4081_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; uint8_t v___x_4084_; 
v___x_4083_ = l_Lean_trace_profiler;
v___x_4084_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_4071_, v___x_4083_);
if (v___x_4084_ == 0)
{
lean_object* v___x_4085_; 
lean_dec_ref(v___f_4078_);
lean_inc_ref(v_run_x27_4073_);
lean_inc(v___y_4065_);
lean_inc_ref(v___y_4068_);
lean_inc(v___y_4062_);
lean_inc_ref(v___y_4067_);
lean_inc(v___y_4064_);
lean_inc_ref(v___y_4058_);
lean_inc(v___y_4061_);
lean_inc_ref(v___y_4066_);
lean_inc(v___y_4057_);
lean_inc(v___y_4063_);
lean_inc_ref(v___y_4059_);
v___x_4085_ = lean_apply_12(v_run_x27_4073_, v___y_4059_, v___y_4063_, v___y_4057_, v___y_4066_, v___y_4061_, v___y_4058_, v___y_4064_, v___y_4067_, v___y_4062_, v___y_4068_, v___y_4065_, lean_box(0));
v___y_3906_ = v___y_4057_;
v___y_3907_ = v___y_4058_;
v___y_3908_ = v___x_4076_;
v___y_3909_ = v___y_4059_;
v___y_3910_ = v___y_4060_;
v___y_3911_ = v___y_4061_;
v___y_3912_ = v___y_4062_;
v___y_3913_ = v___y_4063_;
v___y_3914_ = v___y_4064_;
v___y_3915_ = v___y_4065_;
v___y_3916_ = v___y_4066_;
v___y_3917_ = v___y_4067_;
v___y_3918_ = v___y_4068_;
v___y_3919_ = v___x_4085_;
goto v___jp_3905_;
}
else
{
lean_inc_ref(v_run_x27_4073_);
v___y_3996_ = v___y_4058_;
v___y_3997_ = v___y_4057_;
v___y_3998_ = v___x_4076_;
v___y_3999_ = v___y_4060_;
v___y_4000_ = v___y_4059_;
v___y_4001_ = v___y_4061_;
v___y_4002_ = v___x_4082_;
v___y_4003_ = v_run_x27_4073_;
v___y_4004_ = v___y_4062_;
v___y_4005_ = v___y_4063_;
v___y_4006_ = v___y_4064_;
v___y_4007_ = v___x_4079_;
v___y_4008_ = v___y_4065_;
v___y_4009_ = v___y_4066_;
v___y_4010_ = v___y_4067_;
v___y_4011_ = v_options_4071_;
v___y_4012_ = v___y_4068_;
v___y_4013_ = v_hasTrace_4075_;
v___y_4014_ = v___f_4078_;
v___y_4015_ = v___x_4080_;
goto v___jp_3995_;
}
}
else
{
lean_inc_ref(v_run_x27_4073_);
v___y_3996_ = v___y_4058_;
v___y_3997_ = v___y_4057_;
v___y_3998_ = v___x_4076_;
v___y_3999_ = v___y_4060_;
v___y_4000_ = v___y_4059_;
v___y_4001_ = v___y_4061_;
v___y_4002_ = v___x_4082_;
v___y_4003_ = v_run_x27_4073_;
v___y_4004_ = v___y_4062_;
v___y_4005_ = v___y_4063_;
v___y_4006_ = v___y_4064_;
v___y_4007_ = v___x_4079_;
v___y_4008_ = v___y_4065_;
v___y_4009_ = v___y_4066_;
v___y_4010_ = v___y_4067_;
v___y_4011_ = v_options_4071_;
v___y_4012_ = v___y_4068_;
v___y_4013_ = v_hasTrace_4075_;
v___y_4014_ = v___f_4078_;
v___y_4015_ = v___x_4080_;
goto v___jp_3995_;
}
}
}
v___jp_4086_:
{
lean_object* v_config_4098_; uint8_t v_structures_4099_; 
v_config_4098_ = lean_ctor_get(v___y_4087_, 0);
v_structures_4099_ = lean_ctor_get_uint8(v_config_4098_, sizeof(void*)*3 + 5);
if (v_structures_4099_ == 0)
{
uint8_t v_enums_4100_; 
v_enums_4100_ = lean_ctor_get_uint8(v_config_4098_, sizeof(void*)*3 + 7);
if (v_enums_4100_ == 0)
{
v___y_3876_ = v_config_4098_;
v___y_3877_ = v___y_4087_;
v___y_3878_ = v___y_4088_;
v___y_3879_ = v___y_4089_;
v___y_3880_ = v___y_4090_;
v___y_3881_ = v___y_4091_;
v___y_3882_ = v___y_4092_;
v___y_3883_ = v___y_4093_;
v___y_3884_ = v___y_4094_;
v___y_3885_ = v___y_4095_;
v___y_3886_ = v___y_4096_;
v___y_3887_ = v___y_4097_;
goto v___jp_3875_;
}
else
{
v___y_4057_ = v___y_4089_;
v___y_4058_ = v___y_4092_;
v___y_4059_ = v___y_4087_;
v___y_4060_ = v_config_4098_;
v___y_4061_ = v___y_4091_;
v___y_4062_ = v___y_4095_;
v___y_4063_ = v___y_4088_;
v___y_4064_ = v___y_4093_;
v___y_4065_ = v___y_4097_;
v___y_4066_ = v___y_4090_;
v___y_4067_ = v___y_4094_;
v___y_4068_ = v___y_4096_;
goto v___jp_4056_;
}
}
else
{
v___y_4057_ = v___y_4089_;
v___y_4058_ = v___y_4092_;
v___y_4059_ = v___y_4087_;
v___y_4060_ = v_config_4098_;
v___y_4061_ = v___y_4091_;
v___y_4062_ = v___y_4095_;
v___y_4063_ = v___y_4088_;
v___y_4064_ = v___y_4093_;
v___y_4065_ = v___y_4097_;
v___y_4066_ = v___y_4090_;
v___y_4067_ = v___y_4094_;
v___y_4068_ = v___y_4096_;
goto v___jp_4056_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___boxed(lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline(v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
lean_dec(v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
lean_dec(v_a_4120_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object* v_____r_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___boxed), 12, 0);
v___x_4145_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(v___x_4144_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object* v_____r_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(v_____r_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(lean_object* v_hyps_x3f_4160_, lean_object* v___f_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
if (lean_obj_tag(v_hyps_x3f_4160_) == 1)
{
lean_object* v_val_4174_; lean_object* v___x_4175_; lean_object* v_caches_4176_; lean_object* v_typeAnalysis_4177_; lean_object* v_target_4178_; uint8_t v_didChange_4179_; lean_object* v_eprBvProblem_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4190_; 
v_val_4174_ = lean_ctor_get(v_hyps_x3f_4160_, 0);
v___x_4175_ = lean_st_ref_take(v___y_4163_);
v_caches_4176_ = lean_ctor_get(v___x_4175_, 0);
v_typeAnalysis_4177_ = lean_ctor_get(v___x_4175_, 1);
v_target_4178_ = lean_ctor_get(v___x_4175_, 2);
v_didChange_4179_ = lean_ctor_get_uint8(v___x_4175_, sizeof(void*)*5);
v_eprBvProblem_4180_ = lean_ctor_get(v___x_4175_, 4);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; 
v_unused_4191_ = lean_ctor_get(v___x_4175_, 3);
lean_dec(v_unused_4191_);
v___x_4182_ = v___x_4175_;
v_isShared_4183_ = v_isSharedCheck_4190_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_eprBvProblem_4180_);
lean_inc(v_target_4178_);
lean_inc(v_typeAnalysis_4177_);
lean_inc(v_caches_4176_);
lean_dec(v___x_4175_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4190_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4184_; lean_object* v___x_4186_; 
v___x_4184_ = lean_box(0);
lean_inc(v_val_4174_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 3, v_val_4174_);
v___x_4186_ = v___x_4182_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_caches_4176_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v_typeAnalysis_4177_);
lean_ctor_set(v_reuseFailAlloc_4189_, 2, v_target_4178_);
lean_ctor_set(v_reuseFailAlloc_4189_, 3, v_val_4174_);
lean_ctor_set(v_reuseFailAlloc_4189_, 4, v_eprBvProblem_4180_);
lean_ctor_set_uint8(v_reuseFailAlloc_4189_, sizeof(void*)*5, v_didChange_4179_);
v___x_4186_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = lean_st_ref_put(v___y_4163_, v___x_4186_);
lean_inc(v___y_4172_);
lean_inc_ref(v___y_4171_);
lean_inc(v___y_4170_);
lean_inc_ref(v___y_4169_);
lean_inc(v___y_4168_);
lean_inc_ref(v___y_4167_);
lean_inc(v___y_4166_);
lean_inc_ref(v___y_4165_);
lean_inc(v___y_4164_);
lean_inc(v___y_4163_);
lean_inc_ref(v___y_4162_);
v___x_4188_ = lean_apply_13(v___f_4161_, v___x_4184_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, lean_box(0));
return v___x_4188_;
}
}
}
else
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; uint8_t v___x_4194_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
v___x_4194_ = lean_unbox(v_a_4193_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
lean_dec_ref_known(v___x_4192_, 1);
v___x_4195_ = lean_box(0);
lean_inc(v___y_4172_);
lean_inc_ref(v___y_4171_);
lean_inc(v___y_4170_);
lean_inc_ref(v___y_4169_);
lean_inc(v___y_4168_);
lean_inc_ref(v___y_4167_);
lean_inc(v___y_4166_);
lean_inc_ref(v___y_4165_);
lean_inc(v___y_4164_);
lean_inc(v___y_4163_);
lean_inc_ref(v___y_4162_);
v___x_4196_ = lean_apply_13(v___f_4161_, v___x_4195_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, lean_box(0));
return v___x_4196_;
}
else
{
lean_dec_ref(v___f_4161_);
return v___x_4192_;
}
}
else
{
lean_dec_ref(v___f_4161_);
return v___x_4192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1___boxed(lean_object* v_hyps_x3f_4197_, lean_object* v___f_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_4197_, v___f_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v_hyps_x3f_4197_);
return v_res_4211_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__1));
v___x_4216_ = l_Lean_MessageData_ofFormat(v___x_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2(lean_object* v_x_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2);
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___boxed(lean_object* v_x_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2(v_x_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec_ref(v_x_4232_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object* v_hyps_x3f_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v_toCold_4261_; lean_object* v_options_4262_; lean_object* v_inheritedTraceOptions_4263_; uint8_t v_hasTrace_4264_; lean_object* v___f_4265_; 
v_toCold_4261_ = lean_ctor_get(v_a_4258_, 0);
v_options_4262_ = lean_ctor_get(v_toCold_4261_, 2);
v_inheritedTraceOptions_4263_ = lean_ctor_get(v_toCold_4261_, 11);
v_hasTrace_4264_ = lean_ctor_get_uint8(v_options_4262_, sizeof(void*)*1);
v___f_4265_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0));
if (v_hasTrace_4264_ == 0)
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_4248_, v___f_4265_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4266_;
}
else
{
lean_object* v___f_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v_a_4275_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v_a_4290_; 
v___f_4267_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1));
v___x_4268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0));
v___x_4269_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_normalizeEprFact_spec__3___redArg___closed__1));
v___x_4270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1);
v___x_4271_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4263_, v_options_4262_, v___x_4270_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4340_ = l_Lean_trace_profiler;
v___x_4341_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_4262_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_4248_, v___f_4265_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4342_;
}
else
{
goto v___jp_4299_;
}
}
else
{
goto v___jp_4299_;
}
v___jp_4272_:
{
lean_object* v___x_4276_; double v___x_4277_; double v___x_4278_; double v___x_4279_; double v___x_4280_; double v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4276_ = lean_io_mono_nanos_now();
v___x_4277_ = lean_float_of_nat(v___y_4273_);
v___x_4278_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers___closed__1);
v___x_4279_ = lean_float_div(v___x_4277_, v___x_4278_);
v___x_4280_ = lean_float_of_nat(v___x_4276_);
v___x_4281_ = lean_float_div(v___x_4280_, v___x_4278_);
v___x_4282_ = lean_box_float(v___x_4279_);
v___x_4283_ = lean_box_float(v___x_4281_);
v___x_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4282_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4285_, 0, v_a_4275_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___x_4268_, v_hasTrace_4264_, v___x_4269_, v_options_4262_, v___x_4271_, v___y_4274_, v___f_4267_, v___x_4285_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4286_;
}
v___jp_4287_:
{
lean_object* v___x_4291_; double v___x_4292_; double v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4291_ = lean_io_get_num_heartbeats();
v___x_4292_ = lean_float_of_nat(v___y_4288_);
v___x_4293_ = lean_float_of_nat(v___x_4291_);
v___x_4294_ = lean_box_float(v___x_4292_);
v___x_4295_ = lean_box_float(v___x_4293_);
v___x_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4294_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
v___x_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4297_, 0, v_a_4290_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
v___x_4298_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___x_4268_, v_hasTrace_4264_, v___x_4269_, v_options_4262_, v___x_4271_, v___y_4289_, v___f_4267_, v___x_4297_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4298_;
}
v___jp_4299_:
{
lean_object* v___x_4300_; lean_object* v_a_4301_; lean_object* v___x_4302_; uint8_t v___x_4303_; 
v___x_4300_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__1___redArg(v_a_4259_);
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref(v___x_4300_);
v___x_4302_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4303_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_normalizeEprQuantifiers_spec__2(v_options_4262_, v___x_4302_);
if (v___x_4303_ == 0)
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = lean_io_mono_nanos_now();
v___x_4305_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_4248_, v___f_4265_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
lean_ctor_set_tag(v___x_4308_, 1);
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
v___y_4273_ = v___x_4304_;
v___y_4274_ = v_a_4301_;
v_a_4275_ = v___x_4311_;
goto v___jp_4272_;
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
v_a_4314_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4305_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4305_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set_tag(v___x_4316_, 0);
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
v___y_4273_ = v___x_4304_;
v___y_4274_ = v_a_4301_;
v_a_4275_ = v___x_4319_;
goto v___jp_4272_;
}
}
}
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4322_ = lean_io_get_num_heartbeats();
v___x_4323_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_4248_, v___f_4265_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set_tag(v___x_4326_, 1);
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
v___y_4288_ = v___x_4322_;
v___y_4289_ = v_a_4301_;
v_a_4290_ = v___x_4329_;
goto v___jp_4287_;
}
}
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
v_a_4332_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4323_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4323_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
lean_ctor_set_tag(v___x_4334_, 0);
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
v___y_4288_ = v___x_4322_;
v___y_4289_ = v_a_4301_;
v_a_4290_ = v___x_4337_;
goto v___jp_4287_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object* v_hyps_x3f_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v_hyps_x3f_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_);
lean_dec(v_a_4354_);
lean_dec_ref(v_a_4353_);
lean_dec(v_a_4352_);
lean_dec_ref(v_a_4351_);
lean_dec(v_a_4350_);
lean_dec_ref(v_a_4349_);
lean_dec(v_a_4348_);
lean_dec_ref(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_hyps_x3f_4343_);
return v_res_4356_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
}
#ifdef __cplusplus
}
#endif
