// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Attr public import Std.Tactic.BVDecide.Syntax public import Lean.Meta.Sym.ExprPtr public import Lean.Meta.Sym.SymM public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.Result public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.BVDecide.Types public import Lean.Meta.Tactic.BVDecide.TacticContext
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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Result_getResultExpr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assignFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO___redArg();
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_instMonadControlReaderT___redArg();
lean_object* l_instMonadControlStateRefT_x27___redArg();
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_GoalM_runCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_instExceptToTraceResultBool___redArg___lam__0___boxed(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_cegar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_cegar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "assumption "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "enum domain size lemma for "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "structure lemma projection: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "and flattening from "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grind state"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cegar refinement loop"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Learned hypothesis: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultBool___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object**);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Fixpoint iteration solved the goal"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pipeline reached a fixpoint"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Rerunning pipeline"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v_contextDependent_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_12_; 
v_contextDependent_3_ = lean_ctor_get_uint8(v_x_2_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_12_ == 0)
{
v___x_5_ = v_x_2_;
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
else
{
lean_dec(v_x_2_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
uint8_t v___x_7_; lean_object* v___x_9_; 
v___x_7_ = 1;
if (v_isShared_6_ == 0)
{
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_11_, 1, v_contextDependent_3_);
v___x_9_ = v_reuseFailAlloc_11_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
lean_object* v___x_10_; 
lean_ctor_set_uint8(v___x_9_, 0, v___x_7_);
v___x_10_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_9_);
return v___x_10_;
}
}
}
else
{
lean_object* v_e_x27_13_; lean_object* v_proof_14_; uint8_t v_contextDependent_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v_e_x27_13_ = lean_ctor_get(v_x_2_, 0);
v_proof_14_ = lean_ctor_get(v_x_2_, 1);
v_contextDependent_15_ = lean_ctor_get_uint8(v_x_2_, sizeof(void*)*2 + 1);
v_isSharedCheck_24_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_24_ == 0)
{
v___x_17_ = v_x_2_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_proof_14_);
lean_inc(v_e_x27_13_);
lean_dec(v_x_2_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
uint8_t v___x_19_; lean_object* v___x_21_; 
v___x_19_ = 1;
if (v_isShared_18_ == 0)
{
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_e_x27_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_proof_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_23_, sizeof(void*)*2 + 1, v_contextDependent_15_);
v___x_21_ = v_reuseFailAlloc_23_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; 
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*2, v___x_19_);
v___x_22_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_21_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg(lean_object* v_inst_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_toApplicative_27_; lean_object* v_toBind_28_; lean_object* v_toPure_29_; lean_object* v___f_30_; lean_object* v___x_31_; 
v_toApplicative_27_ = lean_ctor_get(v_inst_25_, 0);
lean_inc_ref(v_toApplicative_27_);
v_toBind_28_ = lean_ctor_get(v_inst_25_, 1);
lean_inc(v_toBind_28_);
lean_dec_ref(v_inst_25_);
v_toPure_29_ = lean_ctor_get(v_toApplicative_27_, 1);
lean_inc(v_toPure_29_);
lean_dec_ref(v_toApplicative_27_);
v___f_30_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0), 2, 1);
lean_closure_set(v___f_30_, 0, v_toPure_29_);
v___x_31_ = lean_apply_4(v_toBind_28_, lean_box(0), lean_box(0), v_x_26_, v___f_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult(lean_object* v_m_32_, lean_object* v_inst_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_toApplicative_35_; lean_object* v_toBind_36_; lean_object* v_toPure_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v_toApplicative_35_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref(v_toApplicative_35_);
v_toBind_36_ = lean_ctor_get(v_inst_33_, 1);
lean_inc(v_toBind_36_);
lean_dec_ref(v_inst_33_);
v_toPure_37_ = lean_ctor_get(v_toApplicative_35_, 1);
lean_inc(v_toPure_37_);
lean_dec_ref(v_toApplicative_35_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0), 2, 1);
lean_closure_set(v___f_38_, 0, v_toPure_37_);
v___x_39_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v_x_34_, v___f_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___impl(lean_object* v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_tag_nat(v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___impl___boxed(lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___impl(v_x_42_);
lean_dec_ref(v_x_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(lean_object* v_t_44_, lean_object* v_k_45_){
_start:
{
if (lean_obj_tag(v_t_44_) == 0)
{
lean_object* v_mvar_46_; lean_object* v___x_47_; 
v_mvar_46_ = lean_ctor_get(v_t_44_, 0);
lean_inc(v_mvar_46_);
lean_dec_ref_known(v_t_44_, 1);
v___x_47_ = lean_apply_1(v_k_45_, v_mvar_46_);
return v___x_47_;
}
else
{
lean_object* v_goal_48_; lean_object* v___x_49_; 
v_goal_48_ = lean_ctor_get(v_t_44_, 0);
lean_inc_ref(v_goal_48_);
lean_dec_ref_known(v_t_44_, 1);
v___x_49_ = lean_apply_1(v_k_45_, v_goal_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim(lean_object* v_motive_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_52_, v_k_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___boxed(lean_object* v_motive_56_, lean_object* v_ctorIdx_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_k_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim(v_motive_56_, v_ctorIdx_57_, v_t_58_, v_h_59_, v_k_60_);
lean_dec(v_ctorIdx_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim___redArg(lean_object* v_t_62_, lean_object* v_mvarIdTarget_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_62_, v_mvarIdTarget_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_mvarIdTarget_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_66_, v_mvarIdTarget_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim___redArg(lean_object* v_t_70_, lean_object* v_grindTarget_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_70_, v_grindTarget_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_grindTarget_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_74_, v_grindTarget_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v_mvar_83_; 
v_mvar_83_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_mvar_83_);
return v_mvar_83_;
}
else
{
lean_object* v_goal_84_; lean_object* v_mvarId_85_; 
v_goal_84_ = lean_ctor_get(v_x_82_, 0);
v_mvarId_85_ = lean_ctor_get(v_goal_84_, 1);
lean_inc(v_mvarId_85_);
return v_mvarId_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId___boxed(lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_x_86_);
lean_dec_ref(v_x_86_);
return v_res_87_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind(lean_object* v_x_88_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 1;
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind___boxed(lean_object* v_x_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isGrind(v_x_91_);
lean_dec_ref(v_x_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar(lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 1;
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar___boxed(lean_object* v_x_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_isMVar(v_x_97_);
lean_dec_ref(v_x_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___impl(lean_object* v_x_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_tag_nat(v_x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___impl___boxed(lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___impl(v_x_102_);
lean_dec_ref(v_x_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object* v_t_104_, lean_object* v_k_105_){
_start:
{
lean_object* v_info_106_; lean_object* v_ctors_107_; lean_object* v___x_108_; 
v_info_106_ = lean_ctor_get(v_t_104_, 0);
lean_inc_ref(v_info_106_);
v_ctors_107_ = lean_ctor_get(v_t_104_, 1);
lean_inc_ref(v_ctors_107_);
lean_dec_ref(v_t_104_);
v___x_108_ = lean_apply_2(v_k_105_, v_info_106_, v_ctors_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object* v_motive_109_, lean_object* v_ctorIdx_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_k_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_111_, v_k_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object* v_motive_115_, lean_object* v_ctorIdx_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_k_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(v_motive_115_, v_ctorIdx_116_, v_t_117_, v_h_118_, v_k_119_);
lean_dec(v_ctorIdx_116_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object* v_t_121_, lean_object* v_simpleEnum_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_121_, v_simpleEnum_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_simpleEnum_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_125_, v_simpleEnum_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object* v_t_129_, lean_object* v_enumWithDefault_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_129_, v_enumWithDefault_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_enumWithDefault_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_133_, v_enumWithDefault_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(lean_object* v_x_137_){
_start:
{
lean_object* v_info_138_; 
v_info_138_ = lean_ctor_get(v_x_137_, 0);
lean_inc_ref(v_info_138_);
return v_info_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo___boxed(lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(v_x_139_);
lean_dec_ref(v_x_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___impl(lean_object* v_x_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_tag_nat(v_x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___impl___boxed(lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___impl(v_x_143_);
lean_dec(v_x_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object* v_t_145_, lean_object* v_k_146_){
_start:
{
switch(lean_obj_tag(v_t_145_))
{
case 0:
{
lean_object* v_fvar_147_; lean_object* v___x_148_; 
v_fvar_147_ = lean_ctor_get(v_t_145_, 0);
lean_inc(v_fvar_147_);
lean_dec_ref_known(v_t_145_, 1);
v___x_148_ = lean_apply_1(v_k_146_, v_fvar_147_);
return v___x_148_;
}
case 1:
{
lean_object* v_n_149_; lean_object* v___x_150_; 
v_n_149_ = lean_ctor_get(v_t_145_, 0);
lean_inc(v_n_149_);
lean_dec_ref_known(v_t_145_, 1);
v___x_150_ = lean_apply_1(v_k_146_, v_n_149_);
return v___x_150_;
}
case 2:
{
lean_object* v_e_151_; lean_object* v___x_152_; 
v_e_151_ = lean_ctor_get(v_t_145_, 0);
lean_inc_ref(v_e_151_);
lean_dec_ref_known(v_t_145_, 1);
v___x_152_ = lean_apply_1(v_k_146_, v_e_151_);
return v___x_152_;
}
case 3:
{
lean_object* v_s_153_; lean_object* v___x_154_; 
v_s_153_ = lean_ctor_get(v_t_145_, 0);
lean_inc(v_s_153_);
lean_dec_ref_known(v_t_145_, 1);
v___x_154_ = lean_apply_1(v_k_146_, v_s_153_);
return v___x_154_;
}
default: 
{
lean_dec(v_t_145_);
return v_k_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object* v_motive_155_, lean_object* v_ctorIdx_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_k_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_157_, v_k_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object* v_motive_161_, lean_object* v_ctorIdx_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_k_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(v_motive_161_, v_ctorIdx_162_, v_t_163_, v_h_164_, v_k_165_);
lean_dec(v_ctorIdx_162_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object* v_t_167_, lean_object* v_lctx_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_167_, v_lctx_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object* v_motive_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_lctx_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_171_, v_lctx_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object* v_t_175_, lean_object* v_enumDomain_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_175_, v_enumDomain_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_enumDomain_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_179_, v_enumDomain_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object* v_t_183_, lean_object* v_structureProjection_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_183_, v_structureProjection_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object* v_motive_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_structureProjection_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_187_, v_structureProjection_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object* v_t_191_, lean_object* v_andFlattened_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_191_, v_andFlattened_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object* v_motive_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_andFlattened_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_195_, v_andFlattened_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim___redArg(lean_object* v_t_199_, lean_object* v_grind_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_199_, v_grind_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_grind_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_203_, v_grind_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_cegar_elim___redArg(lean_object* v_t_207_, lean_object* v_cegar_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_207_, v_cegar_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_cegar_elim(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_cegar_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_211_, v_cegar_213_);
return v___x_214_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object* v_x_219_){
_start:
{
switch(lean_obj_tag(v_x_219_))
{
case 0:
{
lean_object* v_fvar_220_; uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; 
v_fvar_220_ = lean_ctor_get(v_x_219_, 0);
v___x_221_ = 0ULL;
v___x_222_ = l_Lean_instHashableFVarId_hash(v_fvar_220_);
v___x_223_ = lean_uint64_mix_hash(v___x_221_, v___x_222_);
return v___x_223_;
}
case 1:
{
lean_object* v_n_224_; uint64_t v___x_225_; 
v_n_224_ = lean_ctor_get(v_x_219_, 0);
v___x_225_ = 1ULL;
if (lean_obj_tag(v_n_224_) == 0)
{
uint64_t v___x_226_; 
v___x_226_ = 13067028307566252276ULL;
return v___x_226_;
}
else
{
uint64_t v_hash_227_; uint64_t v___x_228_; 
v_hash_227_ = lean_ctor_get_uint64(v_n_224_, sizeof(void*)*2);
v___x_228_ = lean_uint64_mix_hash(v___x_225_, v_hash_227_);
return v___x_228_;
}
}
case 2:
{
lean_object* v_e_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; 
v_e_229_ = lean_ctor_get(v_x_219_, 0);
v___x_230_ = 2ULL;
v___x_231_ = l_Lean_Expr_hash(v_e_229_);
v___x_232_ = lean_uint64_mix_hash(v___x_230_, v___x_231_);
return v___x_232_;
}
case 3:
{
lean_object* v_s_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; 
v_s_233_ = lean_ctor_get(v_x_219_, 0);
v___x_234_ = 3ULL;
v___x_235_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_s_233_);
v___x_236_ = lean_uint64_mix_hash(v___x_234_, v___x_235_);
return v___x_236_;
}
case 4:
{
uint64_t v___x_237_; 
v___x_237_ = 4ULL;
return v___x_237_;
}
default: 
{
uint64_t v___x_238_; 
v___x_238_ = 5ULL;
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object* v_x_239_){
_start:
{
uint64_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_239_);
lean_dec(v_x_239_);
v_r_241_ = lean_box_uint64(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
switch(lean_obj_tag(v_x_244_))
{
case 0:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_object* v_fvar_246_; lean_object* v_fvar_247_; uint8_t v___x_248_; 
v_fvar_246_ = lean_ctor_get(v_x_244_, 0);
v_fvar_247_ = lean_ctor_get(v_x_245_, 0);
v___x_248_ = l_Lean_instBEqFVarId_beq(v_fvar_246_, v_fvar_247_);
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
}
case 1:
{
if (lean_obj_tag(v_x_245_) == 1)
{
lean_object* v_n_250_; lean_object* v_n_251_; uint8_t v___x_252_; 
v_n_250_ = lean_ctor_get(v_x_244_, 0);
v_n_251_ = lean_ctor_get(v_x_245_, 0);
v___x_252_ = lean_name_eq(v_n_250_, v_n_251_);
return v___x_252_;
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
}
case 2:
{
if (lean_obj_tag(v_x_245_) == 2)
{
lean_object* v_e_254_; lean_object* v_e_255_; uint8_t v___x_256_; 
v_e_254_ = lean_ctor_get(v_x_244_, 0);
v_e_255_ = lean_ctor_get(v_x_245_, 0);
v___x_256_ = lean_expr_eqv(v_e_254_, v_e_255_);
return v___x_256_;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
case 3:
{
if (lean_obj_tag(v_x_245_) == 3)
{
lean_object* v_s_258_; lean_object* v_s_259_; 
v_s_258_ = lean_ctor_get(v_x_244_, 0);
v_s_259_ = lean_ctor_get(v_x_245_, 0);
v_x_244_ = v_s_258_;
v_x_245_ = v_s_259_;
goto _start;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
}
case 4:
{
if (lean_obj_tag(v_x_245_) == 4)
{
uint8_t v___x_262_; 
v___x_262_ = 1;
return v___x_262_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = 0;
return v___x_263_;
}
}
default: 
{
if (lean_obj_tag(v_x_245_) == 5)
{
uint8_t v___x_264_; 
v___x_264_ = 1;
return v___x_264_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = 0;
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_266_, v_x_267_);
lean_dec(v_x_267_);
lean_dec(v_x_266_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object* v_s_272_){
_start:
{
if (lean_obj_tag(v_s_272_) == 3)
{
lean_object* v_s_273_; 
v_s_273_ = lean_ctor_get(v_s_272_, 0);
v_s_272_ = v_s_273_;
goto _start;
}
else
{
lean_inc(v_s_272_);
return v_s_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object* v_s_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_275_);
lean_dec(v_s_275_);
return v_res_276_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2));
v___x_282_ = l_Lean_stringToMessageData(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4));
v___x_285_ = l_Lean_stringToMessageData(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6));
v___x_288_ = l_Lean_stringToMessageData(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__10));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object* v_s_295_){
_start:
{
switch(lean_obj_tag(v_s_295_))
{
case 0:
{
lean_object* v_fvar_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_fvar_296_ = lean_ctor_get(v_s_295_, 0);
lean_inc(v_fvar_296_);
lean_dec_ref_known(v_s_295_, 1);
v___x_297_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1);
v___x_298_ = l_Lean_mkFVar(v_fvar_296_);
v___x_299_ = l_Lean_MessageData_ofExpr(v___x_298_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_297_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
return v___x_300_;
}
case 1:
{
lean_object* v_n_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_n_301_ = lean_ctor_get(v_s_295_, 0);
lean_inc(v_n_301_);
lean_dec_ref_known(v_s_295_, 1);
v___x_302_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3);
v___x_303_ = l_Lean_MessageData_ofName(v_n_301_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
return v___x_304_;
}
case 2:
{
lean_object* v_e_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_e_305_ = lean_ctor_get(v_s_295_, 0);
lean_inc_ref(v_e_305_);
lean_dec_ref_known(v_s_295_, 1);
v___x_306_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5);
v___x_307_ = l_Lean_MessageData_ofExpr(v_e_305_);
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
return v___x_308_;
}
case 3:
{
lean_object* v_s_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_s_309_ = lean_ctor_get(v_s_295_, 0);
lean_inc(v_s_309_);
lean_dec_ref_known(v_s_295_, 1);
v___x_310_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7);
v___x_311_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_309_);
lean_dec(v_s_309_);
v___x_312_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v___x_311_);
v___x_313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_310_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
case 4:
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9);
return v___x_314_;
}
default: 
{
lean_object* v___x_315_; 
v___x_315_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__11);
return v___x_315_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_box(0);
v___x_322_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1));
v___x_323_ = l_Lean_Expr_const___override(v___x_322_, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default));
v___x_325_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2);
v___x_326_ = lean_box(0);
v___x_327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
lean_ctor_set(v___x_327_, 2, v___x_325_);
lean_ctor_set(v___x_327_, 3, v___x_324_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
return v___x_329_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object* v_lhs_330_, lean_object* v_rhs_331_){
_start:
{
lean_object* v_type_332_; lean_object* v_type_333_; uint8_t v___x_334_; 
v_type_332_ = lean_ctor_get(v_lhs_330_, 1);
v_type_333_ = lean_ctor_get(v_rhs_331_, 1);
v___x_334_ = lean_expr_eqv(v_type_332_, v_type_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object* v_lhs_335_, lean_object* v_rhs_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_335_, v_rhs_336_);
lean_dec_ref(v_rhs_336_);
lean_dec_ref(v_lhs_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object* v_hyp_341_){
_start:
{
lean_object* v_type_342_; uint64_t v___x_343_; 
v_type_342_ = lean_ctor_get(v_hyp_341_, 1);
v___x_343_ = l_Lean_Expr_hash(v_type_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object* v_hyp_344_){
_start:
{
uint64_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_344_);
lean_dec_ref(v_hyp_344_);
v_r_346_ = lean_box_uint64(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object* v_hyp_349_){
_start:
{
lean_object* v_type_350_; lean_object* v___x_351_; 
v_type_350_ = lean_ctor_get(v_hyp_349_, 1);
lean_inc_ref(v_type_350_);
lean_dec_ref(v_hyp_349_);
v___x_351_ = l_Lean_MessageData_ofExpr(v_type_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___impl(lean_object* v_x_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_tag_nat(v_x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___impl___boxed(lean_object* v_x_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorIdx___impl(v_x_356_);
lean_dec(v_x_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(lean_object* v_t_358_, lean_object* v_k_359_){
_start:
{
if (lean_obj_tag(v_t_358_) == 0)
{
lean_object* v_restrictedTypes_360_; lean_object* v___x_361_; 
v_restrictedTypes_360_ = lean_ctor_get(v_t_358_, 0);
lean_inc(v_restrictedTypes_360_);
lean_dec_ref_known(v_t_358_, 1);
v___x_361_ = lean_apply_1(v_k_359_, v_restrictedTypes_360_);
return v___x_361_;
}
else
{
return v_k_359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(lean_object* v_motive_362_, lean_object* v_ctorIdx_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_k_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_364_, v_k_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___boxed(lean_object* v_motive_368_, lean_object* v_ctorIdx_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_k_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim(v_motive_368_, v_ctorIdx_369_, v_t_370_, v_h_371_, v_k_372_);
lean_dec(v_ctorIdx_369_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim___redArg(lean_object* v_t_374_, lean_object* v_solve_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_374_, v_solve_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_solve_elim(lean_object* v_motive_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_solve_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_378_, v_solve_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim___redArg(lean_object* v_t_382_, lean_object* v_push_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_382_, v_push_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_push_elim(lean_object* v_motive_385_, lean_object* v_t_386_, lean_object* v_h_387_, lean_object* v_push_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_ctorElim___redArg(v_t_386_, v_push_388_);
return v___x_389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = 1;
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush___boxed(lean_object* v_x_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_x_393_);
lean_dec(v_x_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v_restrictedTypes_397_; 
v_restrictedTypes_397_ = lean_ctor_get(v_x_396_, 0);
lean_inc(v_restrictedTypes_397_);
return v_restrictedTypes_397_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_box(0);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes___boxed(lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_x_399_);
lean_dec(v_x_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(lean_object* v_mode_401_, lean_object* v_config_402_){
_start:
{
if (lean_obj_tag(v_mode_401_) == 0)
{
return v_config_402_;
}
else
{
lean_object* v_timeout_403_; uint8_t v_trimProofs_404_; uint8_t v_binaryProofs_405_; uint8_t v_acNf_406_; uint8_t v_graphviz_407_; lean_object* v_maxSteps_408_; uint8_t v_shortCircuit_409_; uint8_t v_solverMode_410_; uint8_t v_uf_411_; lean_object* v_cegarRounds_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_timeout_403_ = lean_ctor_get(v_config_402_, 0);
v_trimProofs_404_ = lean_ctor_get_uint8(v_config_402_, sizeof(void*)*3);
v_binaryProofs_405_ = lean_ctor_get_uint8(v_config_402_, sizeof(void*)*3 + 1);
v_acNf_406_ = lean_ctor_get_uint8(v_config_402_, sizeof(void*)*3 + 2);
v_graphviz_407_ = lean_ctor_get_uint8(v_config_402_, sizeof(void*)*3 + 8);
v_maxSteps_408_ = lean_ctor_get(v_config_402_, 1);
v_shortCircuit_409_ = lean_ctor_get_uint8(v_config_402_, sizeof(void*)*3 + 9);
v_solverMode_410_ = lean_ctor_get_uint8(v_config_402_, sizeof(void*)*3 + 10);
v_uf_411_ = lean_ctor_get_uint8(v_config_402_, sizeof(void*)*3 + 11);
v_cegarRounds_412_ = lean_ctor_get(v_config_402_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_config_402_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v_config_402_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_cegarRounds_412_);
lean_inc(v_maxSteps_408_);
lean_inc(v_timeout_403_);
lean_dec(v_config_402_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___x_416_; lean_object* v___x_418_; 
v___x_416_ = 0;
if (v_isShared_415_ == 0)
{
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_timeout_403_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_maxSteps_408_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_cegarRounds_412_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3, v_trimProofs_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 1, v_binaryProofs_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 2, v_acNf_406_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 8, v_graphviz_407_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 9, v_shortCircuit_409_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 10, v_solverMode_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 11, v_uf_411_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*3 + 3, v___x_416_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*3 + 4, v___x_416_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*3 + 5, v___x_416_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*3 + 6, v___x_416_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*3 + 7, v___x_416_);
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig___boxed(lean_object* v_mode_421_, lean_object* v_config_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_421_, v_config_422_);
lean_dec(v_mode_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object* v_mode_424_, lean_object* v_config_425_, lean_object* v_keepCaches_426_){
_start:
{
uint8_t v___y_428_; 
if (lean_obj_tag(v_keepCaches_426_) == 0)
{
uint8_t v_uf_431_; 
v_uf_431_ = lean_ctor_get_uint8(v_config_425_, sizeof(void*)*3 + 11);
if (v_uf_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_424_);
v___y_428_ = v___x_432_;
goto v___jp_427_;
}
else
{
v___y_428_ = v_uf_431_;
goto v___jp_427_;
}
}
else
{
lean_object* v_val_433_; uint8_t v___x_434_; 
v_val_433_ = lean_ctor_get(v_keepCaches_426_, 0);
v___x_434_ = lean_unbox(v_val_433_);
v___y_428_ = v___x_434_;
goto v___jp_427_;
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_adjustConfig(v_mode_424_, v_config_425_);
v___x_430_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_mode_424_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*2, v___y_428_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new___boxed(lean_object* v_mode_435_, lean_object* v_config_436_, lean_object* v_keepCaches_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_435_, v_config_436_, v_keepCaches_437_);
lean_dec(v_keepCaches_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object* v_ctx_439_){
_start:
{
lean_object* v_config_440_; lean_object* v_restrictedTypes_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_config_440_ = lean_ctor_get(v_ctx_439_, 5);
lean_inc_ref(v_config_440_);
v_restrictedTypes_441_ = lean_ctor_get(v_ctx_439_, 6);
lean_inc(v_restrictedTypes_441_);
lean_dec_ref(v_ctx_439_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_restrictedTypes_441_);
v___x_443_ = lean_box(0);
v___x_444_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_442_, v_config_440_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl(uint8_t v_x_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_box(v_x_445_);
v___x_447_ = lean_obj_tag_nat(v___x_446_);
lean_dec(v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl___boxed(lean_object* v_x_448_){
_start:
{
uint8_t v_x_4__boxed_449_; lean_object* v_res_450_; 
v_x_4__boxed_449_ = lean_unbox(v_x_448_);
v_res_450_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorIdx___impl(v_x_4__boxed_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(lean_object* v_k_451_){
_start:
{
lean_inc(v_k_451_);
return v_k_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___redArg(v_k_452_);
lean_dec(v_k_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(lean_object* v_motive_454_, lean_object* v_ctorIdx_455_, uint8_t v_t_456_, lean_object* v_h_457_, lean_object* v_k_458_){
_start:
{
lean_inc(v_k_458_);
return v_k_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim___boxed(lean_object* v_motive_459_, lean_object* v_ctorIdx_460_, lean_object* v_t_461_, lean_object* v_h_462_, lean_object* v_k_463_){
_start:
{
uint8_t v_t_boxed_464_; lean_object* v_res_465_; 
v_t_boxed_464_ = lean_unbox(v_t_461_);
v_res_465_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ctorElim(v_motive_459_, v_ctorIdx_460_, v_t_boxed_464_, v_h_462_, v_k_463_);
lean_dec(v_k_463_);
lean_dec(v_ctorIdx_460_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_466_){
_start:
{
lean_inc(v_rewrite_466_);
return v_rewrite_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___redArg(v_rewrite_467_);
lean_dec(v_rewrite_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(lean_object* v_motive_469_, uint8_t v_t_470_, lean_object* v_h_471_, lean_object* v_rewrite_472_){
_start:
{
lean_inc(v_rewrite_472_);
return v_rewrite_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim___boxed(lean_object* v_motive_473_, lean_object* v_t_474_, lean_object* v_h_475_, lean_object* v_rewrite_476_){
_start:
{
uint8_t v_t_boxed_477_; lean_object* v_res_478_; 
v_t_boxed_477_ = lean_unbox(v_t_474_);
v_res_478_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_rewrite_elim(v_motive_473_, v_t_boxed_477_, v_h_475_, v_rewrite_476_);
lean_dec(v_rewrite_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(lean_object* v_ac_479_){
_start:
{
lean_inc(v_ac_479_);
return v_ac_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg___boxed(lean_object* v_ac_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___redArg(v_ac_480_);
lean_dec(v_ac_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(lean_object* v_motive_482_, uint8_t v_t_483_, lean_object* v_h_484_, lean_object* v_ac_485_){
_start:
{
lean_inc(v_ac_485_);
return v_ac_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim___boxed(lean_object* v_motive_486_, lean_object* v_t_487_, lean_object* v_h_488_, lean_object* v_ac_489_){
_start:
{
uint8_t v_t_boxed_490_; lean_object* v_res_491_; 
v_t_boxed_490_ = lean_unbox(v_t_487_);
v_res_491_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_ac_elim(v_motive_486_, v_t_boxed_490_, v_h_488_, v_ac_489_);
lean_dec(v_ac_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl(uint8_t v_x_492_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_box(v_x_492_);
v___x_494_ = lean_obj_tag_nat(v___x_493_);
lean_dec(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl___boxed(lean_object* v_x_495_){
_start:
{
uint8_t v_x_4__boxed_496_; lean_object* v_res_497_; 
v_x_4__boxed_496_ = lean_unbox(v_x_495_);
v_res_497_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorIdx___impl(v_x_4__boxed_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(lean_object* v_k_498_){
_start:
{
lean_inc(v_k_498_);
return v_k_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg___boxed(lean_object* v_k_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___redArg(v_k_499_);
lean_dec(v_k_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(lean_object* v_motive_501_, lean_object* v_ctorIdx_502_, uint8_t v_t_503_, lean_object* v_h_504_, lean_object* v_k_505_){
_start:
{
lean_inc(v_k_505_);
return v_k_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim___boxed(lean_object* v_motive_506_, lean_object* v_ctorIdx_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_k_510_){
_start:
{
uint8_t v_t_boxed_511_; lean_object* v_res_512_; 
v_t_boxed_511_ = lean_unbox(v_t_508_);
v_res_512_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_ctorElim(v_motive_506_, v_ctorIdx_507_, v_t_boxed_511_, v_h_509_, v_k_510_);
lean_dec(v_k_510_);
lean_dec(v_ctorIdx_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(lean_object* v_rewrite_513_){
_start:
{
lean_inc(v_rewrite_513_);
return v_rewrite_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg___boxed(lean_object* v_rewrite_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___redArg(v_rewrite_514_);
lean_dec(v_rewrite_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(lean_object* v_motive_516_, uint8_t v_t_517_, lean_object* v_h_518_, lean_object* v_rewrite_519_){
_start:
{
lean_inc(v_rewrite_519_);
return v_rewrite_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim___boxed(lean_object* v_motive_520_, lean_object* v_t_521_, lean_object* v_h_522_, lean_object* v_rewrite_523_){
_start:
{
uint8_t v_t_boxed_524_; lean_object* v_res_525_; 
v_t_boxed_524_ = lean_unbox(v_t_521_);
v_res_525_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_rewrite_elim(v_motive_520_, v_t_boxed_524_, v_h_522_, v_rewrite_523_);
lean_dec(v_rewrite_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(lean_object* v_reduction_526_){
_start:
{
lean_inc(v_reduction_526_);
return v_reduction_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg___boxed(lean_object* v_reduction_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___redArg(v_reduction_527_);
lean_dec(v_reduction_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(lean_object* v_motive_529_, uint8_t v_t_530_, lean_object* v_h_531_, lean_object* v_reduction_532_){
_start:
{
lean_inc(v_reduction_532_);
return v_reduction_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim___boxed(lean_object* v_motive_533_, lean_object* v_t_534_, lean_object* v_h_535_, lean_object* v_reduction_536_){
_start:
{
uint8_t v_t_boxed_537_; lean_object* v_res_538_; 
v_t_boxed_537_ = lean_unbox(v_t_534_);
v_res_538_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_reduction_elim(v_motive_533_, v_t_boxed_537_, v_h_535_, v_reduction_536_);
lean_dec(v_reduction_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(uint8_t v_x_539_, lean_object* v_x_540_){
_start:
{
if (v_x_539_ == 0)
{
lean_object* v_rewriteSimp_541_; 
v_rewriteSimp_541_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_rewriteSimp_541_);
return v_rewriteSimp_541_;
}
else
{
lean_object* v_ac_542_; 
v_ac_542_ = lean_ctor_get(v_x_540_, 3);
lean_inc_ref(v_ac_542_);
return v_ac_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get___boxed(lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
uint8_t v_x_15__boxed_545_; lean_object* v_res_546_; 
v_x_15__boxed_545_ = lean_unbox(v_x_543_);
v_res_546_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_x_15__boxed_545_, v_x_544_);
lean_dec_ref(v_x_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(uint8_t v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
if (v_x_547_ == 0)
{
lean_object* v_reduction_550_; lean_object* v_rewriteDSimp_551_; lean_object* v_ac_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_reduction_550_ = lean_ctor_get(v_x_549_, 0);
v_rewriteDSimp_551_ = lean_ctor_get(v_x_549_, 2);
v_ac_552_ = lean_ctor_get(v_x_549_, 3);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_x_549_, 1);
lean_dec(v_unused_560_);
v___x_554_ = v_x_549_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_ac_552_);
lean_inc(v_rewriteDSimp_551_);
lean_inc(v_reduction_550_);
lean_dec(v_x_549_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v_x_548_);
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_reduction_550_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_x_548_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_rewriteDSimp_551_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_ac_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_reduction_561_; lean_object* v_rewriteSimp_562_; lean_object* v_rewriteDSimp_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_reduction_561_ = lean_ctor_get(v_x_549_, 0);
v_rewriteSimp_562_ = lean_ctor_get(v_x_549_, 1);
v_rewriteDSimp_563_ = lean_ctor_get(v_x_549_, 2);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v_x_549_, 3);
lean_dec(v_unused_571_);
v___x_565_ = v_x_549_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_rewriteDSimp_563_);
lean_inc(v_rewriteSimp_562_);
lean_inc(v_reduction_561_);
lean_dec(v_x_549_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 3, v_x_548_);
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_reduction_561_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_rewriteSimp_562_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_rewriteDSimp_563_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_x_548_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set___boxed(lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
uint8_t v_x_28__boxed_575_; lean_object* v_res_576_; 
v_x_28__boxed_575_ = lean_unbox(v_x_572_);
v_res_576_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_x_28__boxed_575_, v_x_573_, v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(uint8_t v_x_577_, lean_object* v_x_578_){
_start:
{
if (v_x_577_ == 0)
{
lean_object* v_rewriteDSimp_579_; 
v_rewriteDSimp_579_ = lean_ctor_get(v_x_578_, 2);
lean_inc_ref(v_rewriteDSimp_579_);
return v_rewriteDSimp_579_;
}
else
{
lean_object* v_reduction_580_; 
v_reduction_580_ = lean_ctor_get(v_x_578_, 0);
lean_inc_ref(v_reduction_580_);
return v_reduction_580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get___boxed(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
uint8_t v_x_15__boxed_583_; lean_object* v_res_584_; 
v_x_15__boxed_583_ = lean_unbox(v_x_581_);
v_res_584_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_x_15__boxed_583_, v_x_582_);
lean_dec_ref(v_x_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(uint8_t v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
if (v_x_585_ == 0)
{
lean_object* v_reduction_588_; lean_object* v_rewriteSimp_589_; lean_object* v_ac_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_reduction_588_ = lean_ctor_get(v_x_587_, 0);
v_rewriteSimp_589_ = lean_ctor_get(v_x_587_, 1);
v_ac_590_ = lean_ctor_get(v_x_587_, 3);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_x_587_, 2);
lean_dec(v_unused_598_);
v___x_592_ = v_x_587_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_ac_590_);
lean_inc(v_rewriteSimp_589_);
lean_inc(v_reduction_588_);
lean_dec(v_x_587_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 2, v_x_586_);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_reduction_588_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_rewriteSimp_589_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_x_586_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_ac_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_rewriteSimp_599_; lean_object* v_rewriteDSimp_600_; lean_object* v_ac_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_rewriteSimp_599_ = lean_ctor_get(v_x_587_, 1);
v_rewriteDSimp_600_ = lean_ctor_get(v_x_587_, 2);
v_ac_601_ = lean_ctor_get(v_x_587_, 3);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_587_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v_x_587_, 0);
lean_dec(v_unused_609_);
v___x_603_ = v_x_587_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_ac_601_);
lean_inc(v_rewriteDSimp_600_);
lean_inc(v_rewriteSimp_599_);
lean_dec(v_x_587_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v_x_586_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_x_586_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_rewriteSimp_599_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_rewriteDSimp_600_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_ac_601_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set___boxed(lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
uint8_t v_x_28__boxed_613_; lean_object* v_res_614_; 
v_x_28__boxed_613_ = lean_unbox(v_x_610_);
v_res_614_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_x_28__boxed_613_, v_x_611_, v_x_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object* v_hyp_620_, lean_object* v_result_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
if (lean_obj_tag(v_result_621_) == 0)
{
lean_object* v___x_628_; 
lean_dec_ref_known(v_result_621_, 0);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_hyp_620_);
return v___x_628_;
}
else
{
lean_object* v_e_x27_629_; lean_object* v_proof_630_; lean_object* v_name_631_; lean_object* v_type_632_; lean_object* v_value_633_; lean_object* v_source_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_663_; 
v_e_x27_629_ = lean_ctor_get(v_result_621_, 0);
lean_inc_ref(v_e_x27_629_);
v_proof_630_ = lean_ctor_get(v_result_621_, 1);
lean_inc_ref(v_proof_630_);
lean_dec_ref_known(v_result_621_, 2);
v_name_631_ = lean_ctor_get(v_hyp_620_, 0);
v_type_632_ = lean_ctor_get(v_hyp_620_, 1);
v_value_633_ = lean_ctor_get(v_hyp_620_, 2);
v_source_634_ = lean_ctor_get(v_hyp_620_, 3);
v_isSharedCheck_663_ = !lean_is_exclusive(v_hyp_620_);
if (v_isSharedCheck_663_ == 0)
{
v___x_636_ = v_hyp_620_;
v_isShared_637_ = v_isSharedCheck_663_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_source_634_);
lean_inc(v_value_633_);
lean_inc(v_type_632_);
lean_inc(v_name_631_);
lean_dec(v_hyp_620_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_663_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; 
lean_inc_ref(v_type_632_);
v___x_638_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_632_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_654_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_654_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_643_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2));
v___x_644_ = lean_box(0);
v___x_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_645_, 0, v_a_639_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l_Lean_mkConst(v___x_643_, v___x_645_);
lean_inc_ref(v_e_x27_629_);
v___x_647_ = l_Lean_mkApp4(v___x_646_, v_type_632_, v_e_x27_629_, v_proof_630_, v_value_633_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v___x_647_);
lean_ctor_set(v___x_636_, 1, v_e_x27_629_);
v___x_649_ = v___x_636_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_name_631_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_e_x27_629_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_source_634_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_649_);
v___x_651_ = v___x_641_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_del_object(v___x_636_);
lean_dec(v_source_634_);
lean_dec_ref(v_value_633_);
lean_dec_ref(v_type_632_);
lean_dec(v_name_631_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_e_x27_629_);
v_a_655_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_638_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_638_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object* v_hyp_664_, lean_object* v_result_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_664_, v_result_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object* v_hyp_673_, lean_object* v_result_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_673_, v_result_674_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object* v_hyp_683_, lean_object* v_result_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_683_, v_result_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object* v_hyp_693_, lean_object* v_result_694_){
_start:
{
lean_object* v_name_696_; lean_object* v_type_697_; lean_object* v_value_698_; lean_object* v_source_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_708_; 
v_name_696_ = lean_ctor_get(v_hyp_693_, 0);
v_type_697_ = lean_ctor_get(v_hyp_693_, 1);
v_value_698_ = lean_ctor_get(v_hyp_693_, 2);
v_source_699_ = lean_ctor_get(v_hyp_693_, 3);
v_isSharedCheck_708_ = !lean_is_exclusive(v_hyp_693_);
if (v_isSharedCheck_708_ == 0)
{
v___x_701_ = v_hyp_693_;
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_source_699_);
lean_inc(v_value_698_);
lean_inc(v_type_697_);
lean_inc(v_name_696_);
lean_dec(v_hyp_693_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_type_697_, v_result_694_);
lean_dec_ref(v_type_697_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_name_696_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_value_698_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_source_699_);
v___x_705_ = v_reuseFailAlloc_707_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object* v_hyp_709_, lean_object* v_result_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_709_, v_result_710_);
lean_dec_ref(v_result_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object* v_hyp_713_, lean_object* v_result_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_713_, v_result_714_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object* v_hyp_723_, lean_object* v_result_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_723_, v_result_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec_ref(v_result_724_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_733_){
_start:
{
lean_object* v_config_735_; lean_object* v___x_736_; 
v_config_735_ = lean_ctor_get(v_a_733_, 0);
lean_inc_ref(v_config_735_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_config_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_737_);
lean_dec_ref(v_a_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_config_752_; lean_object* v___x_753_; 
v_config_752_ = lean_ctor_get(v_a_740_, 0);
lean_inc_ref(v_config_752_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v_config_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(lean_object* v_a_767_){
_start:
{
lean_object* v_mode_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_mode_769_ = lean_ctor_get(v_a_767_, 1);
v___x_770_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_769_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg___boxed(lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(v_a_772_);
lean_dec_ref(v_a_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_mode_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_mode_787_ = lean_ctor_get(v_a_775_, 1);
v___x_788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_restrictedTypes(v_mode_787_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___boxed(lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(lean_object* v_a_803_){
_start:
{
lean_object* v_mode_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_mode_805_ = lean_ctor_get(v_a_803_, 1);
v___x_806_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_805_);
v___x_807_ = lean_box(v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg___boxed(lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___redArg(v_a_809_);
lean_dec_ref(v_a_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_mode_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_mode_824_ = lean_ctor_get(v_a_812_, 1);
v___x_825_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_824_);
v___x_826_ = lean_box(v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode___boxed(lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_isPushMode(v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; lean_object* v_target_844_; lean_object* v___x_845_; 
v___x_843_ = lean_st_ref_get(v_a_841_);
v_target_844_ = lean_ctor_get(v___x_843_, 2);
lean_inc_ref(v_target_844_);
lean_dec(v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v_target_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg___boxed(lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(v_a_846_);
lean_dec(v_a_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_861_; lean_object* v_target_862_; lean_object* v___x_863_; 
v___x_861_ = lean_st_ref_get(v_a_850_);
v_target_862_ = lean_ctor_get(v___x_861_, 2);
lean_inc_ref(v_target_862_);
lean_dec(v___x_861_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_target_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___boxed(lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_target_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_st_ref_get(v_a_877_);
v_target_880_ = lean_ctor_get(v___x_879_, 2);
lean_inc_ref(v_target_880_);
lean_dec(v___x_879_);
v___x_881_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_880_);
lean_dec_ref(v_target_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg___boxed(lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(v_a_883_);
lean_dec(v_a_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_target_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_898_ = lean_st_ref_get(v_a_887_);
v_target_899_ = lean_ctor_get(v___x_898_, 2);
lean_inc_ref(v_target_899_);
lean_dec(v___x_898_);
v___x_900_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_899_);
lean_dec_ref(v_target_899_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed(lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(lean_object* v_target_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; lean_object* v_caches_919_; lean_object* v_typeAnalysis_920_; lean_object* v_hypotheses_921_; uint8_t v_didChange_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_932_; 
v___x_918_ = lean_st_ref_take(v_a_916_);
v_caches_919_ = lean_ctor_get(v___x_918_, 0);
v_typeAnalysis_920_ = lean_ctor_get(v___x_918_, 1);
v_hypotheses_921_ = lean_ctor_get(v___x_918_, 3);
v_didChange_922_ = lean_ctor_get_uint8(v___x_918_, sizeof(void*)*4);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v___x_918_, 2);
lean_dec(v_unused_933_);
v___x_924_ = v___x_918_;
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_hypotheses_921_);
lean_inc(v_typeAnalysis_920_);
lean_inc(v_caches_919_);
lean_dec(v___x_918_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_932_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_box(0);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 2, v_target_915_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_caches_919_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_typeAnalysis_920_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_target_915_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_hypotheses_921_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*4, v_didChange_922_);
v___x_928_ = v_reuseFailAlloc_931_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_st_ref_put(v_a_916_, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_926_);
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg___boxed(lean_object* v_target_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(v_target_934_, v_a_935_);
lean_dec(v_a_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(lean_object* v_target_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; lean_object* v_caches_952_; lean_object* v_typeAnalysis_953_; lean_object* v_hypotheses_954_; uint8_t v_didChange_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_965_; 
v___x_951_ = lean_st_ref_take(v_a_940_);
v_caches_952_ = lean_ctor_get(v___x_951_, 0);
v_typeAnalysis_953_ = lean_ctor_get(v___x_951_, 1);
v_hypotheses_954_ = lean_ctor_get(v___x_951_, 3);
v_didChange_955_ = lean_ctor_get_uint8(v___x_951_, sizeof(void*)*4);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v___x_951_, 2);
lean_dec(v_unused_966_);
v___x_957_ = v___x_951_;
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_hypotheses_954_);
lean_inc(v_typeAnalysis_953_);
lean_inc(v_caches_952_);
lean_dec(v___x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_box(0);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 2, v_target_938_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_caches_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_typeAnalysis_953_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_target_938_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_hypotheses_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_964_, sizeof(void*)*4, v_didChange_955_);
v___x_961_ = v_reuseFailAlloc_964_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_st_ref_put(v_a_940_, v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___boxed(lean_object* v_target_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(v_target_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0(void){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_instMonadControlReaderT___redArg();
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_instMonadControlStateRefT_x27___redArg();
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2(void){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_instMonadEIO___redArg();
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__2);
v___x_985_ = l_StateRefT_x27_instMonad___redArg(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(lean_object* v_x_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v_target_1003_; 
v___x_1002_ = lean_st_ref_get(v_a_991_);
v_target_1003_ = lean_ctor_get(v___x_1002_, 2);
lean_inc_ref(v_target_1003_);
lean_dec(v___x_1002_);
if (lean_obj_tag(v_target_1003_) == 1)
{
lean_object* v_goal_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1132_; 
v_goal_1004_ = lean_ctor_get(v_target_1003_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_target_1003_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1006_ = v_target_1003_;
v_isShared_1007_ = v_isSharedCheck_1132_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_goal_1004_);
lean_dec(v_target_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1132_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_toApplicative_1011_; lean_object* v_toFunctor_1012_; lean_object* v_toSeq_1013_; lean_object* v_toSeqLeft_1014_; lean_object* v_toSeqRight_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___x_1043_; lean_object* v_toApplicative_1044_; lean_object* v_toFunctor_1045_; lean_object* v_toSeq_1046_; lean_object* v_toSeqLeft_1047_; lean_object* v_toSeqRight_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_toApplicative_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1130_; 
v___x_1008_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_1009_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_1011_ = lean_ctor_get(v___x_1010_, 0);
v_toFunctor_1012_ = lean_ctor_get(v_toApplicative_1011_, 0);
v_toSeq_1013_ = lean_ctor_get(v_toApplicative_1011_, 2);
v_toSeqLeft_1014_ = lean_ctor_get(v_toApplicative_1011_, 3);
v_toSeqRight_1015_ = lean_ctor_get(v_toApplicative_1011_, 4);
v___f_1016_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_1017_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_1012_, 2);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toFunctor_1012_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toFunctor_1012_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___f_1018_);
lean_ctor_set(v___x_1020_, 1, v___f_1019_);
lean_inc(v_toSeqRight_1015_);
v___f_1021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1021_, 0, v_toSeqRight_1015_);
lean_inc(v_toSeqLeft_1014_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toSeqLeft_1014_);
lean_inc(v_toSeq_1013_);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toSeq_1013_);
v___x_1024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1020_);
lean_ctor_set(v___x_1024_, 1, v___f_1016_);
lean_ctor_set(v___x_1024_, 2, v___f_1023_);
lean_ctor_set(v___x_1024_, 3, v___f_1022_);
lean_ctor_set(v___x_1024_, 4, v___f_1021_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___f_1017_);
v___x_1026_ = l_StateRefT_x27_instMonad___redArg(v___x_1025_);
v___x_1027_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1027_, 0, lean_box(0));
lean_closure_set(v___x_1027_, 1, lean_box(0));
lean_closure_set(v___x_1027_, 2, v___x_1026_);
v___x_1028_ = l_instMonadControlTOfPure___redArg(v___x_1027_);
lean_inc_ref(v___x_1028_);
v___f_1029_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1029_, 0, v___x_1009_);
lean_closure_set(v___f_1029_, 1, v___x_1028_);
v___f_1030_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1030_, 0, v___x_1009_);
lean_closure_set(v___f_1030_, 1, v___x_1028_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___f_1029_);
lean_ctor_set(v___x_1031_, 1, v___f_1030_);
lean_inc_ref(v___x_1031_);
v___f_1032_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1032_, 0, v___x_1008_);
lean_closure_set(v___f_1032_, 1, v___x_1031_);
v___f_1033_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1033_, 0, v___x_1008_);
lean_closure_set(v___f_1033_, 1, v___x_1031_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___f_1032_);
lean_ctor_set(v___x_1034_, 1, v___f_1033_);
lean_inc_ref(v___x_1034_);
v___f_1035_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1035_, 0, v___x_1009_);
lean_closure_set(v___f_1035_, 1, v___x_1034_);
v___f_1036_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1036_, 0, v___x_1009_);
lean_closure_set(v___f_1036_, 1, v___x_1034_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___f_1035_);
lean_ctor_set(v___x_1037_, 1, v___f_1036_);
lean_inc_ref(v___x_1037_);
v___f_1038_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1038_, 0, v___x_1008_);
lean_closure_set(v___f_1038_, 1, v___x_1037_);
v___f_1039_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1039_, 0, v___x_1008_);
lean_closure_set(v___f_1039_, 1, v___x_1037_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___f_1038_);
lean_ctor_set(v___x_1040_, 1, v___f_1039_);
lean_inc_ref(v___x_1040_);
v___f_1041_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1041_, 0, v___x_1008_);
lean_closure_set(v___f_1041_, 1, v___x_1040_);
v___f_1042_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1042_, 0, v___x_1008_);
lean_closure_set(v___f_1042_, 1, v___x_1040_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___f_1041_);
lean_ctor_set(v___x_1043_, 1, v___f_1042_);
v_toApplicative_1044_ = lean_ctor_get(v___x_1010_, 0);
v_toFunctor_1045_ = lean_ctor_get(v_toApplicative_1044_, 0);
v_toSeq_1046_ = lean_ctor_get(v_toApplicative_1044_, 2);
v_toSeqLeft_1047_ = lean_ctor_get(v_toApplicative_1044_, 3);
v_toSeqRight_1048_ = lean_ctor_get(v_toApplicative_1044_, 4);
lean_inc_ref_n(v_toFunctor_1045_, 2);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toFunctor_1045_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toFunctor_1045_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___f_1049_);
lean_ctor_set(v___x_1051_, 1, v___f_1050_);
lean_inc(v_toSeqRight_1048_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toSeqRight_1048_);
lean_inc(v_toSeqLeft_1047_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toSeqLeft_1047_);
lean_inc(v_toSeq_1046_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toSeq_1046_);
v___x_1055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1051_);
lean_ctor_set(v___x_1055_, 1, v___f_1016_);
lean_ctor_set(v___x_1055_, 2, v___f_1054_);
lean_ctor_set(v___x_1055_, 3, v___f_1053_);
lean_ctor_set(v___x_1055_, 4, v___f_1052_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v___f_1017_);
v___x_1057_ = l_StateRefT_x27_instMonad___redArg(v___x_1056_);
v_toApplicative_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v___x_1057_, 1);
lean_dec(v_unused_1131_);
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1130_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_toApplicative_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1130_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_toFunctor_1062_; lean_object* v_toSeq_1063_; lean_object* v_toSeqLeft_1064_; lean_object* v_toSeqRight_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1128_; 
v_toFunctor_1062_ = lean_ctor_get(v_toApplicative_1058_, 0);
v_toSeq_1063_ = lean_ctor_get(v_toApplicative_1058_, 2);
v_toSeqLeft_1064_ = lean_ctor_get(v_toApplicative_1058_, 3);
v_toSeqRight_1065_ = lean_ctor_get(v_toApplicative_1058_, 4);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_toApplicative_1058_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_toApplicative_1058_, 1);
lean_dec(v_unused_1129_);
v___x_1067_ = v_toApplicative_1058_;
v_isShared_1068_ = v_isSharedCheck_1128_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_toSeqRight_1065_);
lean_inc(v_toSeqLeft_1064_);
lean_inc(v_toSeq_1063_);
lean_inc(v_toFunctor_1062_);
lean_dec(v_toApplicative_1058_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1128_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___f_1072_; lean_object* v___x_1073_; lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___x_1078_; 
v___f_1069_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1070_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1062_);
v___f_1071_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1071_, 0, v_toFunctor_1062_);
v___f_1072_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1072_, 0, v_toFunctor_1062_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___f_1071_);
lean_ctor_set(v___x_1073_, 1, v___f_1072_);
v___f_1074_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1074_, 0, v_toSeqRight_1065_);
v___f_1075_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1075_, 0, v_toSeqLeft_1064_);
v___f_1076_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1076_, 0, v_toSeq_1063_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 4, v___f_1074_);
lean_ctor_set(v___x_1067_, 3, v___f_1075_);
lean_ctor_set(v___x_1067_, 2, v___f_1076_);
lean_ctor_set(v___x_1067_, 1, v___f_1069_);
lean_ctor_set(v___x_1067_, 0, v___x_1073_);
v___x_1078_ = v___x_1067_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___f_1069_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v___f_1076_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v___f_1075_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v___f_1074_);
v___x_1078_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v___f_1070_);
lean_ctor_set(v___x_1060_, 0, v___x_1078_);
v___x_1080_ = v___x_1060_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___f_1070_);
v___x_1080_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_mvarId_1086_; lean_object* v___x_1087_; lean_object* v___x_5100__overap_1088_; lean_object* v___x_1089_; 
v___x_1081_ = l_StateRefT_x27_instMonad___redArg(v___x_1080_);
v___x_1082_ = l_ReaderT_instMonad___redArg(v___x_1081_);
v___x_1083_ = l_StateRefT_x27_instMonad___redArg(v___x_1082_);
v___x_1084_ = l_ReaderT_instMonad___redArg(v___x_1083_);
v___x_1085_ = l_ReaderT_instMonad___redArg(v___x_1084_);
v_mvarId_1086_ = lean_ctor_get(v_goal_1004_, 1);
lean_inc(v_mvarId_1086_);
v___x_1087_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1087_, 0, lean_box(0));
lean_closure_set(v___x_1087_, 1, v_goal_1004_);
lean_closure_set(v___x_1087_, 2, v_x_990_);
v___x_5100__overap_1088_ = l_Lean_MVarId_withContext___redArg(v___x_1043_, v___x_1085_, v_mvarId_1086_, v___x_1087_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_a_996_);
lean_inc_ref(v_a_995_);
lean_inc(v_a_994_);
lean_inc_ref(v_a_993_);
lean_inc(v_a_992_);
v___x_1089_ = lean_apply_10(v___x_5100__overap_1088_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1117_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1117_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1117_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1097_; 
v_fst_1094_ = lean_ctor_get(v_a_1090_, 0);
lean_inc(v_fst_1094_);
v_snd_1095_ = lean_ctor_get(v_a_1090_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_a_1090_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_snd_1095_);
v___x_1097_ = v___x_1006_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_snd_1095_);
v___x_1097_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; lean_object* v_caches_1099_; lean_object* v_typeAnalysis_1100_; lean_object* v_hypotheses_1101_; uint8_t v_didChange_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1114_; 
v___x_1098_ = lean_st_ref_take(v_a_991_);
v_caches_1099_ = lean_ctor_get(v___x_1098_, 0);
v_typeAnalysis_1100_ = lean_ctor_get(v___x_1098_, 1);
v_hypotheses_1101_ = lean_ctor_get(v___x_1098_, 3);
v_didChange_1102_ = lean_ctor_get_uint8(v___x_1098_, sizeof(void*)*4);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; 
v_unused_1115_ = lean_ctor_get(v___x_1098_, 2);
lean_dec(v_unused_1115_);
v___x_1104_ = v___x_1098_;
v_isShared_1105_ = v_isSharedCheck_1114_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_hypotheses_1101_);
lean_inc(v_typeAnalysis_1100_);
lean_inc(v_caches_1099_);
lean_dec(v___x_1098_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1114_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 2, v___x_1097_);
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_caches_1099_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_typeAnalysis_1100_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_hypotheses_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, sizeof(void*)*4, v_didChange_1102_);
v___x_1107_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = lean_st_ref_put(v_a_991_, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_fst_1094_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1109_);
v___x_1111_ = v___x_1092_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
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
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_del_object(v___x_1006_);
v_a_1118_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1089_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1089_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
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
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v_target_1003_);
lean_dec_ref(v_x_990_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___boxed(lean_object* v_x_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg(v_x_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec(v_a_1136_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(lean_object* v_00_u03b1_1148_, lean_object* v_x_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v_target_1163_; 
v___x_1162_ = lean_st_ref_get(v_a_1151_);
v_target_1163_ = lean_ctor_get(v___x_1162_, 2);
lean_inc_ref(v_target_1163_);
lean_dec(v___x_1162_);
if (lean_obj_tag(v_target_1163_) == 1)
{
lean_object* v_goal_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1292_; 
v_goal_1164_ = lean_ctor_get(v_target_1163_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_target_1163_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1166_ = v_target_1163_;
v_isShared_1167_ = v_isSharedCheck_1292_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_goal_1164_);
lean_dec(v_target_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1292_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_toApplicative_1171_; lean_object* v_toFunctor_1172_; lean_object* v_toSeq_1173_; lean_object* v_toSeqLeft_1174_; lean_object* v_toSeqRight_1175_; lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v_toApplicative_1204_; lean_object* v_toFunctor_1205_; lean_object* v_toSeq_1206_; lean_object* v_toSeqLeft_1207_; lean_object* v_toSeqRight_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_toApplicative_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1290_; 
v___x_1168_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__0);
v___x_1169_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__1);
v___x_1170_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_1171_ = lean_ctor_get(v___x_1170_, 0);
v_toFunctor_1172_ = lean_ctor_get(v_toApplicative_1171_, 0);
v_toSeq_1173_ = lean_ctor_get(v_toApplicative_1171_, 2);
v_toSeqLeft_1174_ = lean_ctor_get(v_toApplicative_1171_, 3);
v_toSeqRight_1175_ = lean_ctor_get(v_toApplicative_1171_, 4);
v___f_1176_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_1177_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_1172_, 2);
v___f_1178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1178_, 0, v_toFunctor_1172_);
v___f_1179_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1179_, 0, v_toFunctor_1172_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___f_1178_);
lean_ctor_set(v___x_1180_, 1, v___f_1179_);
lean_inc(v_toSeqRight_1175_);
v___f_1181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1181_, 0, v_toSeqRight_1175_);
lean_inc(v_toSeqLeft_1174_);
v___f_1182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1182_, 0, v_toSeqLeft_1174_);
lean_inc(v_toSeq_1173_);
v___f_1183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1183_, 0, v_toSeq_1173_);
v___x_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1180_);
lean_ctor_set(v___x_1184_, 1, v___f_1176_);
lean_ctor_set(v___x_1184_, 2, v___f_1183_);
lean_ctor_set(v___x_1184_, 3, v___f_1182_);
lean_ctor_set(v___x_1184_, 4, v___f_1181_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___f_1177_);
v___x_1186_ = l_StateRefT_x27_instMonad___redArg(v___x_1185_);
v___x_1187_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1187_, 0, lean_box(0));
lean_closure_set(v___x_1187_, 1, lean_box(0));
lean_closure_set(v___x_1187_, 2, v___x_1186_);
v___x_1188_ = l_instMonadControlTOfPure___redArg(v___x_1187_);
lean_inc_ref(v___x_1188_);
v___f_1189_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1189_, 0, v___x_1169_);
lean_closure_set(v___f_1189_, 1, v___x_1188_);
v___f_1190_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1190_, 0, v___x_1169_);
lean_closure_set(v___f_1190_, 1, v___x_1188_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___f_1189_);
lean_ctor_set(v___x_1191_, 1, v___f_1190_);
lean_inc_ref(v___x_1191_);
v___f_1192_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1192_, 0, v___x_1168_);
lean_closure_set(v___f_1192_, 1, v___x_1191_);
v___f_1193_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1193_, 0, v___x_1168_);
lean_closure_set(v___f_1193_, 1, v___x_1191_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___f_1192_);
lean_ctor_set(v___x_1194_, 1, v___f_1193_);
lean_inc_ref(v___x_1194_);
v___f_1195_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1195_, 0, v___x_1169_);
lean_closure_set(v___f_1195_, 1, v___x_1194_);
v___f_1196_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1196_, 0, v___x_1169_);
lean_closure_set(v___f_1196_, 1, v___x_1194_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___f_1195_);
lean_ctor_set(v___x_1197_, 1, v___f_1196_);
lean_inc_ref(v___x_1197_);
v___f_1198_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1198_, 0, v___x_1168_);
lean_closure_set(v___f_1198_, 1, v___x_1197_);
v___f_1199_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1199_, 0, v___x_1168_);
lean_closure_set(v___f_1199_, 1, v___x_1197_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___f_1198_);
lean_ctor_set(v___x_1200_, 1, v___f_1199_);
lean_inc_ref(v___x_1200_);
v___f_1201_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_1201_, 0, v___x_1168_);
lean_closure_set(v___f_1201_, 1, v___x_1200_);
v___f_1202_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_1202_, 0, v___x_1168_);
lean_closure_set(v___f_1202_, 1, v___x_1200_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___f_1201_);
lean_ctor_set(v___x_1203_, 1, v___f_1202_);
v_toApplicative_1204_ = lean_ctor_get(v___x_1170_, 0);
v_toFunctor_1205_ = lean_ctor_get(v_toApplicative_1204_, 0);
v_toSeq_1206_ = lean_ctor_get(v_toApplicative_1204_, 2);
v_toSeqLeft_1207_ = lean_ctor_get(v_toApplicative_1204_, 3);
v_toSeqRight_1208_ = lean_ctor_get(v_toApplicative_1204_, 4);
lean_inc_ref_n(v_toFunctor_1205_, 2);
v___f_1209_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1209_, 0, v_toFunctor_1205_);
v___f_1210_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1210_, 0, v_toFunctor_1205_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___f_1209_);
lean_ctor_set(v___x_1211_, 1, v___f_1210_);
lean_inc(v_toSeqRight_1208_);
v___f_1212_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1212_, 0, v_toSeqRight_1208_);
lean_inc(v_toSeqLeft_1207_);
v___f_1213_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1213_, 0, v_toSeqLeft_1207_);
lean_inc(v_toSeq_1206_);
v___f_1214_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1214_, 0, v_toSeq_1206_);
v___x_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1211_);
lean_ctor_set(v___x_1215_, 1, v___f_1176_);
lean_ctor_set(v___x_1215_, 2, v___f_1214_);
lean_ctor_set(v___x_1215_, 3, v___f_1213_);
lean_ctor_set(v___x_1215_, 4, v___f_1212_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___f_1177_);
v___x_1217_ = l_StateRefT_x27_instMonad___redArg(v___x_1216_);
v_toApplicative_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v___x_1217_, 1);
lean_dec(v_unused_1291_);
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1290_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_toApplicative_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1290_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_toFunctor_1222_; lean_object* v_toSeq_1223_; lean_object* v_toSeqLeft_1224_; lean_object* v_toSeqRight_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1288_; 
v_toFunctor_1222_ = lean_ctor_get(v_toApplicative_1218_, 0);
v_toSeq_1223_ = lean_ctor_get(v_toApplicative_1218_, 2);
v_toSeqLeft_1224_ = lean_ctor_get(v_toApplicative_1218_, 3);
v_toSeqRight_1225_ = lean_ctor_get(v_toApplicative_1218_, 4);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_toApplicative_1218_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_toApplicative_1218_, 1);
lean_dec(v_unused_1289_);
v___x_1227_ = v_toApplicative_1218_;
v_isShared_1228_ = v_isSharedCheck_1288_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_toSeqRight_1225_);
lean_inc(v_toSeqLeft_1224_);
lean_inc(v_toSeq_1223_);
lean_inc(v_toFunctor_1222_);
lean_dec(v_toApplicative_1218_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1288_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___x_1238_; 
v___f_1229_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_1230_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_1222_);
v___f_1231_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1231_, 0, v_toFunctor_1222_);
v___f_1232_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1232_, 0, v_toFunctor_1222_);
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___f_1231_);
lean_ctor_set(v___x_1233_, 1, v___f_1232_);
v___f_1234_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1234_, 0, v_toSeqRight_1225_);
v___f_1235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1235_, 0, v_toSeqLeft_1224_);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toSeq_1223_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 4, v___f_1234_);
lean_ctor_set(v___x_1227_, 3, v___f_1235_);
lean_ctor_set(v___x_1227_, 2, v___f_1236_);
lean_ctor_set(v___x_1227_, 1, v___f_1229_);
lean_ctor_set(v___x_1227_, 0, v___x_1233_);
v___x_1238_ = v___x_1227_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___f_1229_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v___f_1236_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v___f_1235_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v___f_1234_);
v___x_1238_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___f_1230_);
lean_ctor_set(v___x_1220_, 0, v___x_1238_);
v___x_1240_ = v___x_1220_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___f_1230_);
v___x_1240_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v_mvarId_1246_; lean_object* v___x_1247_; lean_object* v___x_5171__overap_1248_; lean_object* v___x_1249_; 
v___x_1241_ = l_StateRefT_x27_instMonad___redArg(v___x_1240_);
v___x_1242_ = l_ReaderT_instMonad___redArg(v___x_1241_);
v___x_1243_ = l_StateRefT_x27_instMonad___redArg(v___x_1242_);
v___x_1244_ = l_ReaderT_instMonad___redArg(v___x_1243_);
v___x_1245_ = l_ReaderT_instMonad___redArg(v___x_1244_);
v_mvarId_1246_ = lean_ctor_get(v_goal_1164_, 1);
lean_inc(v_mvarId_1246_);
v___x_1247_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_GoalM_runCore___boxed), 13, 3);
lean_closure_set(v___x_1247_, 0, lean_box(0));
lean_closure_set(v___x_1247_, 1, v_goal_1164_);
lean_closure_set(v___x_1247_, 2, v_x_1149_);
v___x_5171__overap_1248_ = l_Lean_MVarId_withContext___redArg(v___x_1203_, v___x_1245_, v_mvarId_1246_, v___x_1247_);
lean_inc(v_a_1160_);
lean_inc_ref(v_a_1159_);
lean_inc(v_a_1158_);
lean_inc_ref(v_a_1157_);
lean_inc(v_a_1156_);
lean_inc_ref(v_a_1155_);
lean_inc(v_a_1154_);
lean_inc_ref(v_a_1153_);
lean_inc(v_a_1152_);
v___x_1249_ = lean_apply_10(v___x_5171__overap_1248_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, lean_box(0));
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1277_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1277_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1277_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1257_; 
v_fst_1254_ = lean_ctor_get(v_a_1250_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v_a_1250_, 1);
lean_inc(v_snd_1255_);
lean_dec(v_a_1250_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v_snd_1255_);
v___x_1257_ = v___x_1166_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_snd_1255_);
v___x_1257_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v_caches_1259_; lean_object* v_typeAnalysis_1260_; lean_object* v_hypotheses_1261_; uint8_t v_didChange_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1274_; 
v___x_1258_ = lean_st_ref_take(v_a_1151_);
v_caches_1259_ = lean_ctor_get(v___x_1258_, 0);
v_typeAnalysis_1260_ = lean_ctor_get(v___x_1258_, 1);
v_hypotheses_1261_ = lean_ctor_get(v___x_1258_, 3);
v_didChange_1262_ = lean_ctor_get_uint8(v___x_1258_, sizeof(void*)*4);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1258_, 2);
lean_dec(v_unused_1275_);
v___x_1264_ = v___x_1258_;
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_hypotheses_1261_);
lean_inc(v_typeAnalysis_1260_);
lean_inc(v_caches_1259_);
lean_dec(v___x_1258_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 2, v___x_1257_);
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_caches_1259_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_typeAnalysis_1260_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_hypotheses_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*4, v_didChange_1262_);
v___x_1267_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1268_ = lean_st_ref_put(v_a_1151_, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_fst_1254_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1269_);
v___x_1271_ = v___x_1252_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_del_object(v___x_1166_);
v_a_1278_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1249_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1249_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
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
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref(v_target_1163_);
lean_dec_ref(v_x_1149_);
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___boxed(lean_object* v_00_u03b1_1295_, lean_object* v_x_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal(v_00_u03b1_1295_, v_x_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(lean_object* v_x_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
lean_inc(v___y_1315_);
lean_inc_ref(v___y_1314_);
lean_inc(v___y_1313_);
lean_inc_ref(v___y_1312_);
lean_inc(v___y_1311_);
v___x_1321_ = lean_apply_10(v_x_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, lean_box(0));
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed(lean_object* v_x_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0(v_x_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(lean_object* v_mvarId_1334_, lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___f_1346_; lean_object* v___x_1347_; 
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_1346_, 0, v_x_1335_);
lean_closure_set(v___f_1346_, 1, v___y_1336_);
lean_closure_set(v___f_1346_, 2, v___y_1337_);
lean_closure_set(v___f_1346_, 3, v___y_1338_);
lean_closure_set(v___f_1346_, 4, v___y_1339_);
lean_closure_set(v___f_1346_, 5, v___y_1340_);
v___x_1347_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1334_, v___f_1346_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1347_) == 0)
{
return v___x_1347_;
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg___boxed(lean_object* v_mvarId_1356_, lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1356_, v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(lean_object* v_00_u03b1_1369_, lean_object* v_mvarId_1370_, lean_object* v_x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1370_, v_x_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_mvarId_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0(v_00_u03b1_1383_, v_mvarId_1384_, v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(lean_object* v_goal_1397_, lean_object* v_falseProof_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_st_mk_ref(v_goal_1397_);
v___x_1410_ = l_Lean_Meta_Grind_closeGoal(v_falseProof_1398_, v___x_1409_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1420_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1415_ = lean_st_ref_get(v___x_1409_);
lean_dec(v___x_1409_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_a_1411_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1416_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v___x_1409_);
v_a_1421_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1410_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1410_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed(lean_object* v_goal_1429_, lean_object* v_falseProof_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0(v_goal_1429_, v_falseProof_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object* v_falseProof_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1454_; lean_object* v_target_1455_; 
v___x_1454_ = lean_st_ref_get(v_a_1443_);
v_target_1455_ = lean_ctor_get(v___x_1454_, 2);
lean_inc_ref(v_target_1455_);
lean_dec(v___x_1454_);
if (lean_obj_tag(v_target_1455_) == 0)
{
lean_object* v_mvar_1456_; lean_object* v___x_1457_; 
v_mvar_1456_ = lean_ctor_get(v_target_1455_, 0);
lean_inc(v_mvar_1456_);
lean_dec_ref_known(v_target_1455_, 1);
v___x_1457_ = l_Lean_MVarId_assignFalseProof(v_mvar_1456_, v_falseProof_1442_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
return v___x_1457_;
}
else
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1509_; 
v_isSharedCheck_1509_ = !lean_is_exclusive(v_target_1455_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_target_1455_, 0);
lean_dec(v_unused_1510_);
v___x_1459_ = v_target_1455_;
v_isShared_1460_ = v_isSharedCheck_1509_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_target_1455_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1509_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_target_1463_; 
v___x_1461_ = lean_box(0);
v___x_1462_ = lean_st_ref_get(v_a_1443_);
v_target_1463_ = lean_ctor_get(v___x_1462_, 2);
lean_inc_ref(v_target_1463_);
lean_dec(v___x_1462_);
if (lean_obj_tag(v_target_1463_) == 1)
{
lean_object* v_goal_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1505_; 
lean_del_object(v___x_1459_);
v_goal_1464_ = lean_ctor_get(v_target_1463_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_target_1463_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1466_ = v_target_1463_;
v_isShared_1467_ = v_isSharedCheck_1505_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_goal_1464_);
lean_dec(v_target_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1505_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_mvarId_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; 
v_mvarId_1468_ = lean_ctor_get(v_goal_1464_, 1);
lean_inc(v_mvarId_1468_);
v___f_1469_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1469_, 0, v_goal_1464_);
lean_closure_set(v___f_1469_, 1, v_falseProof_1442_);
v___x_1470_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget_spec__0___redArg(v_mvarId_1468_, v___f_1469_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1496_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1496_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1496_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_snd_1475_; lean_object* v___x_1477_; 
v_snd_1475_ = lean_ctor_get(v_a_1471_, 1);
lean_inc(v_snd_1475_);
lean_dec(v_a_1471_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_snd_1475_);
v___x_1477_ = v___x_1466_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_snd_1475_);
v___x_1477_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v_caches_1479_; lean_object* v_typeAnalysis_1480_; lean_object* v_hypotheses_1481_; uint8_t v_didChange_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1493_; 
v___x_1478_ = lean_st_ref_take(v_a_1443_);
v_caches_1479_ = lean_ctor_get(v___x_1478_, 0);
v_typeAnalysis_1480_ = lean_ctor_get(v___x_1478_, 1);
v_hypotheses_1481_ = lean_ctor_get(v___x_1478_, 3);
v_didChange_1482_ = lean_ctor_get_uint8(v___x_1478_, sizeof(void*)*4);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v___x_1478_, 2);
lean_dec(v_unused_1494_);
v___x_1484_ = v___x_1478_;
v_isShared_1485_ = v_isSharedCheck_1493_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_hypotheses_1481_);
lean_inc(v_typeAnalysis_1480_);
lean_inc(v_caches_1479_);
lean_dec(v___x_1478_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1493_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 2, v___x_1477_);
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_caches_1479_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_typeAnalysis_1480_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_hypotheses_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*4, v_didChange_1482_);
v___x_1487_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = lean_st_ref_put(v_a_1443_, v___x_1487_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1461_);
v___x_1490_ = v___x_1473_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1461_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1466_);
v_a_1497_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1470_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1470_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
else
{
lean_object* v___x_1507_; 
lean_dec_ref(v_target_1463_);
lean_dec_ref(v_falseProof_1442_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set_tag(v___x_1459_, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1507_ = v___x_1459_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1461_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg___boxed(lean_object* v_falseProof_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec(v_a_1512_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(lean_object* v_falseProof_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_falseProof_1524_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed(lean_object* v_falseProof_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget(v_falseProof_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1554_; uint8_t v_didChange_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = lean_st_ref_get(v_a_1552_);
v_didChange_1555_ = lean_ctor_get_uint8(v___x_1554_, sizeof(void*)*4);
lean_dec(v___x_1554_);
v___x_1556_ = lean_box(v_didChange_1555_);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_1558_);
lean_dec(v_a_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1573_; uint8_t v_didChange_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1573_ = lean_st_ref_get(v_a_1562_);
v_didChange_1574_ = lean_ctor_get_uint8(v___x_1573_, sizeof(void*)*4);
lean_dec(v___x_1573_);
v___x_1575_ = lean_box(v_didChange_1574_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v_caches_1593_; lean_object* v_typeAnalysis_1594_; lean_object* v_target_1595_; lean_object* v_hypotheses_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1607_; 
v___x_1592_ = lean_st_ref_take(v_a_1590_);
v_caches_1593_ = lean_ctor_get(v___x_1592_, 0);
v_typeAnalysis_1594_ = lean_ctor_get(v___x_1592_, 1);
v_target_1595_ = lean_ctor_get(v___x_1592_, 2);
v_hypotheses_1596_ = lean_ctor_get(v___x_1592_, 3);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1598_ = v___x_1592_;
v_isShared_1599_ = v_isSharedCheck_1607_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_hypotheses_1596_);
lean_inc(v_target_1595_);
lean_inc(v_typeAnalysis_1594_);
lean_inc(v_caches_1593_);
lean_dec(v___x_1592_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1607_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; uint8_t v___x_1601_; lean_object* v___x_1603_; 
v___x_1600_ = lean_box(0);
v___x_1601_ = 0;
if (v_isShared_1599_ == 0)
{
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_caches_1593_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_typeAnalysis_1594_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_target_1595_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_hypotheses_1596_);
v___x_1603_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*4, v___x_1601_);
v___x_1604_ = lean_st_ref_put(v_a_1590_, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1600_);
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_1608_);
lean_dec(v_a_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v_caches_1624_; lean_object* v_typeAnalysis_1625_; lean_object* v_target_1626_; lean_object* v_hypotheses_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1638_; 
v___x_1623_ = lean_st_ref_take(v_a_1612_);
v_caches_1624_ = lean_ctor_get(v___x_1623_, 0);
v_typeAnalysis_1625_ = lean_ctor_get(v___x_1623_, 1);
v_target_1626_ = lean_ctor_get(v___x_1623_, 2);
v_hypotheses_1627_ = lean_ctor_get(v___x_1623_, 3);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1629_ = v___x_1623_;
v_isShared_1630_ = v_isSharedCheck_1638_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_hypotheses_1627_);
lean_inc(v_target_1626_);
lean_inc(v_typeAnalysis_1625_);
lean_inc(v_caches_1624_);
lean_dec(v___x_1623_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1638_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1634_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = 0;
if (v_isShared_1630_ == 0)
{
v___x_1634_ = v___x_1629_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_caches_1624_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_typeAnalysis_1625_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_target_1626_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_hypotheses_1627_);
v___x_1634_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*4, v___x_1632_);
v___x_1635_ = lean_st_ref_put(v_a_1612_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1631_);
return v___x_1636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object* v_a_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v_caches_1655_; lean_object* v_typeAnalysis_1656_; lean_object* v_target_1657_; lean_object* v_hypotheses_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1669_; 
v___x_1654_ = lean_st_ref_take(v_a_1652_);
v_caches_1655_ = lean_ctor_get(v___x_1654_, 0);
v_typeAnalysis_1656_ = lean_ctor_get(v___x_1654_, 1);
v_target_1657_ = lean_ctor_get(v___x_1654_, 2);
v_hypotheses_1658_ = lean_ctor_get(v___x_1654_, 3);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1660_ = v___x_1654_;
v_isShared_1661_ = v_isSharedCheck_1669_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_hypotheses_1658_);
lean_inc(v_target_1657_);
lean_inc(v_typeAnalysis_1656_);
lean_inc(v_caches_1655_);
lean_dec(v___x_1654_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1669_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = lean_box(0);
v___x_1663_ = 1;
if (v_isShared_1661_ == 0)
{
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_caches_1655_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_typeAnalysis_1656_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_target_1657_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_hypotheses_1658_);
v___x_1665_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*4, v___x_1663_);
v___x_1666_ = lean_st_ref_put(v_a_1652_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1662_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_1670_);
lean_dec(v_a_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v_caches_1686_; lean_object* v_typeAnalysis_1687_; lean_object* v_target_1688_; lean_object* v_hypotheses_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1700_; 
v___x_1685_ = lean_st_ref_take(v_a_1674_);
v_caches_1686_ = lean_ctor_get(v___x_1685_, 0);
v_typeAnalysis_1687_ = lean_ctor_get(v___x_1685_, 1);
v_target_1688_ = lean_ctor_get(v___x_1685_, 2);
v_hypotheses_1689_ = lean_ctor_get(v___x_1685_, 3);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1691_ = v___x_1685_;
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_hypotheses_1689_);
lean_inc(v_target_1688_);
lean_inc(v_typeAnalysis_1687_);
lean_inc(v_caches_1686_);
lean_dec(v___x_1685_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; uint8_t v___x_1694_; lean_object* v___x_1696_; 
v___x_1693_ = lean_box(0);
v___x_1694_ = 1;
if (v_isShared_1692_ == 0)
{
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_caches_1686_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_typeAnalysis_1687_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_target_1688_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_hypotheses_1689_);
v___x_1696_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*4, v___x_1694_);
v___x_1697_ = lean_st_ref_put(v_a_1674_, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1693_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1716_; lean_object* v_caches_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_st_ref_get(v_a_1714_);
v_caches_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc_ref(v_caches_1717_);
lean_dec(v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_caches_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg___boxed(lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___redArg(v_a_1719_);
lean_dec(v_a_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v_caches_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_st_ref_get(v_a_1723_);
v_caches_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_caches_1735_);
lean_dec(v___x_1734_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_caches_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches___boxed(lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getCaches(v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(lean_object* v_caches_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v_typeAnalysis_1754_; lean_object* v_target_1755_; lean_object* v_hypotheses_1756_; uint8_t v_didChange_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1767_; 
v___x_1753_ = lean_st_ref_take(v_a_1751_);
v_typeAnalysis_1754_ = lean_ctor_get(v___x_1753_, 1);
v_target_1755_ = lean_ctor_get(v___x_1753_, 2);
v_hypotheses_1756_ = lean_ctor_get(v___x_1753_, 3);
v_didChange_1757_ = lean_ctor_get_uint8(v___x_1753_, sizeof(void*)*4);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v___x_1753_, 0);
lean_dec(v_unused_1768_);
v___x_1759_ = v___x_1753_;
v_isShared_1760_ = v_isSharedCheck_1767_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_hypotheses_1756_);
lean_inc(v_target_1755_);
lean_inc(v_typeAnalysis_1754_);
lean_dec(v___x_1753_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1767_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_box(0);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v_caches_1750_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_caches_1750_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_typeAnalysis_1754_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_target_1755_);
lean_ctor_set(v_reuseFailAlloc_1766_, 3, v_hypotheses_1756_);
lean_ctor_set_uint8(v_reuseFailAlloc_1766_, sizeof(void*)*4, v_didChange_1757_);
v___x_1763_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_st_ref_put(v_a_1751_, v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1761_);
return v___x_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg___boxed(lean_object* v_caches_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___redArg(v_caches_1769_, v_a_1770_);
lean_dec(v_a_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(lean_object* v_caches_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v_typeAnalysis_1787_; lean_object* v_target_1788_; lean_object* v_hypotheses_1789_; uint8_t v_didChange_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1800_; 
v___x_1786_ = lean_st_ref_take(v_a_1775_);
v_typeAnalysis_1787_ = lean_ctor_get(v___x_1786_, 1);
v_target_1788_ = lean_ctor_get(v___x_1786_, 2);
v_hypotheses_1789_ = lean_ctor_get(v___x_1786_, 3);
v_didChange_1790_ = lean_ctor_get_uint8(v___x_1786_, sizeof(void*)*4);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1786_, 0);
lean_dec(v_unused_1801_);
v___x_1792_ = v___x_1786_;
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_hypotheses_1789_);
lean_inc(v_target_1788_);
lean_inc(v_typeAnalysis_1787_);
lean_dec(v___x_1786_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1800_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1794_ = lean_box(0);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_caches_1773_);
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_caches_1773_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_typeAnalysis_1787_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_target_1788_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_hypotheses_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1799_, sizeof(void*)*4, v_didChange_1790_);
v___x_1796_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_st_ref_put(v_a_1775_, v___x_1796_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1794_);
return v___x_1798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches___boxed(lean_object* v_caches_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setCaches(v_caches_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
return v_res_1815_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0(void){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_1820_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
lean_ctor_set(v___x_1820_, 2, v___x_1819_);
lean_ctor_set(v___x_1820_, 3, v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
uint8_t v_keepCaches_1824_; 
v_keepCaches_1824_ = lean_ctor_get_uint8(v_a_1821_, sizeof(void*)*2);
if (v_keepCaches_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v_typeAnalysis_1827_; lean_object* v_target_1828_; lean_object* v_hypotheses_1829_; uint8_t v_didChange_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1840_; 
v___x_1825_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_1826_ = lean_st_ref_take(v_a_1822_);
v_typeAnalysis_1827_ = lean_ctor_get(v___x_1826_, 1);
v_target_1828_ = lean_ctor_get(v___x_1826_, 2);
v_hypotheses_1829_ = lean_ctor_get(v___x_1826_, 3);
v_didChange_1830_ = lean_ctor_get_uint8(v___x_1826_, sizeof(void*)*4);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; 
v_unused_1841_ = lean_ctor_get(v___x_1826_, 0);
lean_dec(v_unused_1841_);
v___x_1832_ = v___x_1826_;
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_hypotheses_1829_);
lean_inc(v_target_1828_);
lean_inc(v_typeAnalysis_1827_);
lean_dec(v___x_1826_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = lean_box(0);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1825_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_typeAnalysis_1827_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_target_1828_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v_hypotheses_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, sizeof(void*)*4, v_didChange_1830_);
v___x_1836_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_st_ref_put(v_a_1822_, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1834_);
return v___x_1838_;
}
}
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_box(0);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___boxed(lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_1848_, v_a_1849_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___boxed(lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches(v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; lean_object* v_typeAnalysis_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_st_ref_get(v_a_1874_);
v_typeAnalysis_1877_ = lean_ctor_get(v___x_1876_, 1);
lean_inc_ref(v_typeAnalysis_1877_);
lean_dec(v___x_1876_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_typeAnalysis_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1879_);
lean_dec(v_a_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1894_; lean_object* v_typeAnalysis_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_st_ref_get(v_a_1883_);
v_typeAnalysis_1895_ = lean_ctor_get(v___x_1894_, 1);
lean_inc_ref(v_typeAnalysis_1895_);
lean_dec(v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_typeAnalysis_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_typeAnalysis_1921_; lean_object* v_interestingStructures_1922_; lean_object* v_uninteresting_1923_; uint8_t v___x_1924_; 
v___x_1918_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1919_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1920_ = lean_st_ref_get(v_a_1916_);
v_typeAnalysis_1921_ = lean_ctor_get(v___x_1920_, 1);
lean_inc_ref(v_typeAnalysis_1921_);
lean_dec(v___x_1920_);
v_interestingStructures_1922_ = lean_ctor_get(v_typeAnalysis_1921_, 0);
lean_inc_ref(v_interestingStructures_1922_);
v_uninteresting_1923_ = lean_ctor_get(v_typeAnalysis_1921_, 3);
lean_inc_ref(v_uninteresting_1923_);
lean_dec_ref(v_typeAnalysis_1921_);
lean_inc(v_n_1915_);
v___x_1924_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1918_, v___x_1919_, v_uninteresting_1923_, v_n_1915_);
lean_dec_ref(v_uninteresting_1923_);
if (v___x_1924_ == 0)
{
uint8_t v___x_1925_; 
v___x_1925_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1918_, v___x_1919_, v_interestingStructures_1922_, v_n_1915_);
lean_dec_ref(v_interestingStructures_1922_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_box(v___x_1925_);
v___x_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec_ref(v_interestingStructures_1922_);
lean_dec(v_n_1915_);
v___x_1931_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1933_, v_a_1934_);
lean_dec(v_a_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_typeAnalysis_1953_; lean_object* v_interestingStructures_1954_; lean_object* v_uninteresting_1955_; uint8_t v___x_1956_; 
v___x_1950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1951_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1952_ = lean_st_ref_get(v_a_1939_);
v_typeAnalysis_1953_ = lean_ctor_get(v___x_1952_, 1);
lean_inc_ref(v_typeAnalysis_1953_);
lean_dec(v___x_1952_);
v_interestingStructures_1954_ = lean_ctor_get(v_typeAnalysis_1953_, 0);
lean_inc_ref(v_interestingStructures_1954_);
v_uninteresting_1955_ = lean_ctor_get(v_typeAnalysis_1953_, 3);
lean_inc_ref(v_uninteresting_1955_);
lean_dec_ref(v_typeAnalysis_1953_);
lean_inc(v_n_1937_);
v___x_1956_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1950_, v___x_1951_, v_uninteresting_1955_, v_n_1937_);
lean_dec_ref(v_uninteresting_1955_);
if (v___x_1956_ == 0)
{
uint8_t v___x_1957_; 
v___x_1957_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1950_, v___x_1951_, v_interestingStructures_1954_, v_n_1937_);
lean_dec_ref(v_interestingStructures_1954_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_box(v___x_1957_);
v___x_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec_ref(v_interestingStructures_1954_);
lean_dec(v_n_1937_);
v___x_1963_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v_caches_1983_; lean_object* v_typeAnalysis_1984_; lean_object* v_target_1985_; lean_object* v_hypotheses_1986_; uint8_t v_didChange_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1998_; 
v___x_1982_ = lean_st_ref_take(v_a_1980_);
v_caches_1983_ = lean_ctor_get(v___x_1982_, 0);
v_typeAnalysis_1984_ = lean_ctor_get(v___x_1982_, 1);
v_target_1985_ = lean_ctor_get(v___x_1982_, 2);
v_hypotheses_1986_ = lean_ctor_get(v___x_1982_, 3);
v_didChange_1987_ = lean_ctor_get_uint8(v___x_1982_, sizeof(void*)*4);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1989_ = v___x_1982_;
v_isShared_1990_ = v_isSharedCheck_1998_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_hypotheses_1986_);
lean_inc(v_target_1985_);
lean_inc(v_typeAnalysis_1984_);
lean_inc(v_caches_1983_);
lean_dec(v___x_1982_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1998_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1991_ = lean_box(0);
v___x_1992_ = lean_apply_1(v_f_1979_, v_typeAnalysis_1984_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 1, v___x_1992_);
v___x_1994_ = v___x_1989_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_caches_1983_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v_target_1985_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v_hypotheses_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1997_, sizeof(void*)*4, v_didChange_1987_);
v___x_1994_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_st_ref_put(v_a_1980_, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1991_);
return v___x_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_1999_, v_a_2000_);
lean_dec(v_a_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; lean_object* v_caches_2017_; lean_object* v_typeAnalysis_2018_; lean_object* v_target_2019_; lean_object* v_hypotheses_2020_; uint8_t v_didChange_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2032_; 
v___x_2016_ = lean_st_ref_take(v_a_2005_);
v_caches_2017_ = lean_ctor_get(v___x_2016_, 0);
v_typeAnalysis_2018_ = lean_ctor_get(v___x_2016_, 1);
v_target_2019_ = lean_ctor_get(v___x_2016_, 2);
v_hypotheses_2020_ = lean_ctor_get(v___x_2016_, 3);
v_didChange_2021_ = lean_ctor_get_uint8(v___x_2016_, sizeof(void*)*4);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2023_ = v___x_2016_;
v_isShared_2024_ = v_isSharedCheck_2032_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_hypotheses_2020_);
lean_inc(v_target_2019_);
lean_inc(v_typeAnalysis_2018_);
lean_inc(v_caches_2017_);
lean_dec(v___x_2016_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2032_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_apply_1(v_f_2003_, v_typeAnalysis_2018_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v___x_2026_);
v___x_2028_ = v___x_2023_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_caches_2017_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_target_2019_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v_hypotheses_2020_);
lean_ctor_set_uint8(v_reuseFailAlloc_2031_, sizeof(void*)*4, v_didChange_2021_);
v___x_2028_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_st_ref_put(v_a_2005_, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2025_);
return v___x_2030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v_typeAnalysis_2053_; lean_object* v_caches_2054_; lean_object* v_target_2055_; lean_object* v_hypotheses_2056_; uint8_t v_didChange_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2079_; 
v___x_2050_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2051_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2052_ = lean_st_ref_take(v_a_2048_);
v_typeAnalysis_2053_ = lean_ctor_get(v___x_2052_, 1);
v_caches_2054_ = lean_ctor_get(v___x_2052_, 0);
v_target_2055_ = lean_ctor_get(v___x_2052_, 2);
v_hypotheses_2056_ = lean_ctor_get(v___x_2052_, 3);
v_didChange_2057_ = lean_ctor_get_uint8(v___x_2052_, sizeof(void*)*4);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2059_ = v___x_2052_;
v_isShared_2060_ = v_isSharedCheck_2079_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_hypotheses_2056_);
lean_inc(v_target_2055_);
lean_inc(v_typeAnalysis_2053_);
lean_inc(v_caches_2054_);
lean_dec(v___x_2052_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2079_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_interestingStructures_2061_; lean_object* v_interestingEnums_2062_; lean_object* v_interestingMatchers_2063_; lean_object* v_uninteresting_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2078_; 
v_interestingStructures_2061_ = lean_ctor_get(v_typeAnalysis_2053_, 0);
v_interestingEnums_2062_ = lean_ctor_get(v_typeAnalysis_2053_, 1);
v_interestingMatchers_2063_ = lean_ctor_get(v_typeAnalysis_2053_, 2);
v_uninteresting_2064_ = lean_ctor_get(v_typeAnalysis_2053_, 3);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_typeAnalysis_2053_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2066_ = v_typeAnalysis_2053_;
v_isShared_2067_ = v_isSharedCheck_2078_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_uninteresting_2064_);
lean_inc(v_interestingMatchers_2063_);
lean_inc(v_interestingEnums_2062_);
lean_inc(v_interestingStructures_2061_);
lean_dec(v_typeAnalysis_2053_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2078_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2068_ = lean_box(0);
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2050_, v___x_2051_, v_interestingStructures_2061_, v_n_2047_, v___x_2068_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2069_);
v___x_2071_ = v___x_2066_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_interestingEnums_2062_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_interestingMatchers_2063_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_uninteresting_2064_);
v___x_2071_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2073_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2071_);
v___x_2073_ = v___x_2059_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_caches_2054_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_target_2055_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_hypotheses_2056_);
lean_ctor_set_uint8(v_reuseFailAlloc_2076_, sizeof(void*)*4, v_didChange_2057_);
v___x_2073_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_st_ref_put(v_a_2048_, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2068_);
return v___x_2075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_2080_, v_a_2081_);
lean_dec(v_a_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v_typeAnalysis_2100_; lean_object* v_caches_2101_; lean_object* v_target_2102_; lean_object* v_hypotheses_2103_; uint8_t v_didChange_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2126_; 
v___x_2097_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2098_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2099_ = lean_st_ref_take(v_a_2086_);
v_typeAnalysis_2100_ = lean_ctor_get(v___x_2099_, 1);
v_caches_2101_ = lean_ctor_get(v___x_2099_, 0);
v_target_2102_ = lean_ctor_get(v___x_2099_, 2);
v_hypotheses_2103_ = lean_ctor_get(v___x_2099_, 3);
v_didChange_2104_ = lean_ctor_get_uint8(v___x_2099_, sizeof(void*)*4);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2106_ = v___x_2099_;
v_isShared_2107_ = v_isSharedCheck_2126_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_hypotheses_2103_);
lean_inc(v_target_2102_);
lean_inc(v_typeAnalysis_2100_);
lean_inc(v_caches_2101_);
lean_dec(v___x_2099_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2126_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v_interestingStructures_2108_; lean_object* v_interestingEnums_2109_; lean_object* v_interestingMatchers_2110_; lean_object* v_uninteresting_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2125_; 
v_interestingStructures_2108_ = lean_ctor_get(v_typeAnalysis_2100_, 0);
v_interestingEnums_2109_ = lean_ctor_get(v_typeAnalysis_2100_, 1);
v_interestingMatchers_2110_ = lean_ctor_get(v_typeAnalysis_2100_, 2);
v_uninteresting_2111_ = lean_ctor_get(v_typeAnalysis_2100_, 3);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_typeAnalysis_2100_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2113_ = v_typeAnalysis_2100_;
v_isShared_2114_ = v_isSharedCheck_2125_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_uninteresting_2111_);
lean_inc(v_interestingMatchers_2110_);
lean_inc(v_interestingEnums_2109_);
lean_inc(v_interestingStructures_2108_);
lean_dec(v_typeAnalysis_2100_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2125_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2115_ = lean_box(0);
v___x_2116_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2097_, v___x_2098_, v_interestingStructures_2108_, v_n_2084_, v___x_2115_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2116_);
v___x_2118_ = v___x_2113_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_interestingEnums_2109_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_interestingMatchers_2110_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_uninteresting_2111_);
v___x_2118_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2120_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v___x_2118_);
v___x_2120_ = v___x_2106_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_caches_2101_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_target_2102_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_hypotheses_2103_);
lean_ctor_set_uint8(v_reuseFailAlloc_2123_, sizeof(void*)*4, v_didChange_2104_);
v___x_2120_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_st_ref_put(v_a_2086_, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2115_);
return v___x_2122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_typeAnalysis_2147_; lean_object* v_caches_2148_; lean_object* v_target_2149_; lean_object* v_hypotheses_2150_; uint8_t v_didChange_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2173_; 
v___x_2144_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2145_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2146_ = lean_st_ref_take(v_a_2142_);
v_typeAnalysis_2147_ = lean_ctor_get(v___x_2146_, 1);
v_caches_2148_ = lean_ctor_get(v___x_2146_, 0);
v_target_2149_ = lean_ctor_get(v___x_2146_, 2);
v_hypotheses_2150_ = lean_ctor_get(v___x_2146_, 3);
v_didChange_2151_ = lean_ctor_get_uint8(v___x_2146_, sizeof(void*)*4);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2153_ = v___x_2146_;
v_isShared_2154_ = v_isSharedCheck_2173_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_hypotheses_2150_);
lean_inc(v_target_2149_);
lean_inc(v_typeAnalysis_2147_);
lean_inc(v_caches_2148_);
lean_dec(v___x_2146_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2173_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_interestingStructures_2155_; lean_object* v_interestingEnums_2156_; lean_object* v_interestingMatchers_2157_; lean_object* v_uninteresting_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2172_; 
v_interestingStructures_2155_ = lean_ctor_get(v_typeAnalysis_2147_, 0);
v_interestingEnums_2156_ = lean_ctor_get(v_typeAnalysis_2147_, 1);
v_interestingMatchers_2157_ = lean_ctor_get(v_typeAnalysis_2147_, 2);
v_uninteresting_2158_ = lean_ctor_get(v_typeAnalysis_2147_, 3);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_typeAnalysis_2147_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2160_ = v_typeAnalysis_2147_;
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_uninteresting_2158_);
lean_inc(v_interestingMatchers_2157_);
lean_inc(v_interestingEnums_2156_);
lean_inc(v_interestingStructures_2155_);
lean_dec(v_typeAnalysis_2147_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2162_ = lean_box(0);
v___x_2163_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2144_, v___x_2145_, v_interestingEnums_2156_, v_n_2141_, v___x_2162_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 1, v___x_2163_);
v___x_2165_ = v___x_2160_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_interestingStructures_2155_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_interestingMatchers_2157_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_uninteresting_2158_);
v___x_2165_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___x_2165_);
v___x_2167_ = v___x_2153_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_caches_2148_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_target_2149_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_hypotheses_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*4, v_didChange_2151_);
v___x_2167_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = lean_st_ref_put(v_a_2142_, v___x_2167_);
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2162_);
return v___x_2169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_2174_, v_a_2175_);
lean_dec(v_a_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v_typeAnalysis_2194_; lean_object* v_caches_2195_; lean_object* v_target_2196_; lean_object* v_hypotheses_2197_; uint8_t v_didChange_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2220_; 
v___x_2191_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2192_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2193_ = lean_st_ref_take(v_a_2180_);
v_typeAnalysis_2194_ = lean_ctor_get(v___x_2193_, 1);
v_caches_2195_ = lean_ctor_get(v___x_2193_, 0);
v_target_2196_ = lean_ctor_get(v___x_2193_, 2);
v_hypotheses_2197_ = lean_ctor_get(v___x_2193_, 3);
v_didChange_2198_ = lean_ctor_get_uint8(v___x_2193_, sizeof(void*)*4);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2200_ = v___x_2193_;
v_isShared_2201_ = v_isSharedCheck_2220_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_hypotheses_2197_);
lean_inc(v_target_2196_);
lean_inc(v_typeAnalysis_2194_);
lean_inc(v_caches_2195_);
lean_dec(v___x_2193_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2220_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_interestingStructures_2202_; lean_object* v_interestingEnums_2203_; lean_object* v_interestingMatchers_2204_; lean_object* v_uninteresting_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2219_; 
v_interestingStructures_2202_ = lean_ctor_get(v_typeAnalysis_2194_, 0);
v_interestingEnums_2203_ = lean_ctor_get(v_typeAnalysis_2194_, 1);
v_interestingMatchers_2204_ = lean_ctor_get(v_typeAnalysis_2194_, 2);
v_uninteresting_2205_ = lean_ctor_get(v_typeAnalysis_2194_, 3);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_typeAnalysis_2194_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2207_ = v_typeAnalysis_2194_;
v_isShared_2208_ = v_isSharedCheck_2219_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_uninteresting_2205_);
lean_inc(v_interestingMatchers_2204_);
lean_inc(v_interestingEnums_2203_);
lean_inc(v_interestingStructures_2202_);
lean_dec(v_typeAnalysis_2194_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2219_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2209_ = lean_box(0);
v___x_2210_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2191_, v___x_2192_, v_interestingEnums_2203_, v_n_2178_, v___x_2209_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v___x_2210_);
v___x_2212_ = v___x_2207_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_interestingStructures_2202_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_interestingMatchers_2204_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v_uninteresting_2205_);
v___x_2212_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2214_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 1, v___x_2212_);
v___x_2214_ = v___x_2200_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_caches_2195_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_target_2196_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v_hypotheses_2197_);
lean_ctor_set_uint8(v_reuseFailAlloc_2217_, sizeof(void*)*4, v_didChange_2198_);
v___x_2214_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_st_ref_put(v_a_2180_, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2209_);
return v___x_2216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_2235_, lean_object* v_k_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v_typeAnalysis_2242_; lean_object* v_caches_2243_; lean_object* v_target_2244_; lean_object* v_hypotheses_2245_; uint8_t v_didChange_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2268_; 
v___x_2239_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2240_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2241_ = lean_st_ref_take(v_a_2237_);
v_typeAnalysis_2242_ = lean_ctor_get(v___x_2241_, 1);
v_caches_2243_ = lean_ctor_get(v___x_2241_, 0);
v_target_2244_ = lean_ctor_get(v___x_2241_, 2);
v_hypotheses_2245_ = lean_ctor_get(v___x_2241_, 3);
v_didChange_2246_ = lean_ctor_get_uint8(v___x_2241_, sizeof(void*)*4);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2248_ = v___x_2241_;
v_isShared_2249_ = v_isSharedCheck_2268_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_hypotheses_2245_);
lean_inc(v_target_2244_);
lean_inc(v_typeAnalysis_2242_);
lean_inc(v_caches_2243_);
lean_dec(v___x_2241_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2268_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_interestingStructures_2250_; lean_object* v_interestingEnums_2251_; lean_object* v_interestingMatchers_2252_; lean_object* v_uninteresting_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2267_; 
v_interestingStructures_2250_ = lean_ctor_get(v_typeAnalysis_2242_, 0);
v_interestingEnums_2251_ = lean_ctor_get(v_typeAnalysis_2242_, 1);
v_interestingMatchers_2252_ = lean_ctor_get(v_typeAnalysis_2242_, 2);
v_uninteresting_2253_ = lean_ctor_get(v_typeAnalysis_2242_, 3);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_typeAnalysis_2242_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2255_ = v_typeAnalysis_2242_;
v_isShared_2256_ = v_isSharedCheck_2267_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_uninteresting_2253_);
lean_inc(v_interestingMatchers_2252_);
lean_inc(v_interestingEnums_2251_);
lean_inc(v_interestingStructures_2250_);
lean_dec(v_typeAnalysis_2242_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2267_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2257_ = lean_box(0);
v___x_2258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2239_, v___x_2240_, v_interestingMatchers_2252_, v_n_2235_, v_k_2236_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 2, v___x_2258_);
v___x_2260_ = v___x_2255_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_interestingStructures_2250_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_interestingEnums_2251_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_uninteresting_2253_);
v___x_2260_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2262_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 1, v___x_2260_);
v___x_2262_ = v___x_2248_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_caches_2243_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_target_2244_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_hypotheses_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2265_, sizeof(void*)*4, v_didChange_2246_);
v___x_2262_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_st_ref_put(v_a_2237_, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2257_);
return v___x_2264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_2269_, lean_object* v_k_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_2269_, v_k_2270_, v_a_2271_);
lean_dec(v_a_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_2274_, lean_object* v_k_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_typeAnalysis_2291_; lean_object* v_caches_2292_; lean_object* v_target_2293_; lean_object* v_hypotheses_2294_; uint8_t v_didChange_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2317_; 
v___x_2288_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2289_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2290_ = lean_st_ref_take(v_a_2277_);
v_typeAnalysis_2291_ = lean_ctor_get(v___x_2290_, 1);
v_caches_2292_ = lean_ctor_get(v___x_2290_, 0);
v_target_2293_ = lean_ctor_get(v___x_2290_, 2);
v_hypotheses_2294_ = lean_ctor_get(v___x_2290_, 3);
v_didChange_2295_ = lean_ctor_get_uint8(v___x_2290_, sizeof(void*)*4);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2297_ = v___x_2290_;
v_isShared_2298_ = v_isSharedCheck_2317_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_hypotheses_2294_);
lean_inc(v_target_2293_);
lean_inc(v_typeAnalysis_2291_);
lean_inc(v_caches_2292_);
lean_dec(v___x_2290_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2317_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_interestingStructures_2299_; lean_object* v_interestingEnums_2300_; lean_object* v_interestingMatchers_2301_; lean_object* v_uninteresting_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2316_; 
v_interestingStructures_2299_ = lean_ctor_get(v_typeAnalysis_2291_, 0);
v_interestingEnums_2300_ = lean_ctor_get(v_typeAnalysis_2291_, 1);
v_interestingMatchers_2301_ = lean_ctor_get(v_typeAnalysis_2291_, 2);
v_uninteresting_2302_ = lean_ctor_get(v_typeAnalysis_2291_, 3);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_typeAnalysis_2291_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2304_ = v_typeAnalysis_2291_;
v_isShared_2305_ = v_isSharedCheck_2316_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_uninteresting_2302_);
lean_inc(v_interestingMatchers_2301_);
lean_inc(v_interestingEnums_2300_);
lean_inc(v_interestingStructures_2299_);
lean_dec(v_typeAnalysis_2291_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2316_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = lean_box(0);
v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2288_, v___x_2289_, v_interestingMatchers_2301_, v_n_2274_, v_k_2275_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 2, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_interestingStructures_2299_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_interestingEnums_2300_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_uninteresting_2302_);
v___x_2309_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2311_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2309_);
v___x_2311_ = v___x_2297_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_caches_2292_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_target_2293_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_hypotheses_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*4, v_didChange_2295_);
v___x_2311_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_st_ref_put(v_a_2277_, v___x_2311_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2306_);
return v___x_2313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_2318_, lean_object* v_k_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_2318_, v_k_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v_typeAnalysis_2339_; lean_object* v_caches_2340_; lean_object* v_target_2341_; lean_object* v_hypotheses_2342_; uint8_t v_didChange_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2365_; 
v___x_2336_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2337_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2338_ = lean_st_ref_take(v_a_2334_);
v_typeAnalysis_2339_ = lean_ctor_get(v___x_2338_, 1);
v_caches_2340_ = lean_ctor_get(v___x_2338_, 0);
v_target_2341_ = lean_ctor_get(v___x_2338_, 2);
v_hypotheses_2342_ = lean_ctor_get(v___x_2338_, 3);
v_didChange_2343_ = lean_ctor_get_uint8(v___x_2338_, sizeof(void*)*4);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2345_ = v___x_2338_;
v_isShared_2346_ = v_isSharedCheck_2365_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_hypotheses_2342_);
lean_inc(v_target_2341_);
lean_inc(v_typeAnalysis_2339_);
lean_inc(v_caches_2340_);
lean_dec(v___x_2338_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2365_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v_interestingStructures_2347_; lean_object* v_interestingEnums_2348_; lean_object* v_interestingMatchers_2349_; lean_object* v_uninteresting_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2364_; 
v_interestingStructures_2347_ = lean_ctor_get(v_typeAnalysis_2339_, 0);
v_interestingEnums_2348_ = lean_ctor_get(v_typeAnalysis_2339_, 1);
v_interestingMatchers_2349_ = lean_ctor_get(v_typeAnalysis_2339_, 2);
v_uninteresting_2350_ = lean_ctor_get(v_typeAnalysis_2339_, 3);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_typeAnalysis_2339_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2352_ = v_typeAnalysis_2339_;
v_isShared_2353_ = v_isSharedCheck_2364_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_uninteresting_2350_);
lean_inc(v_interestingMatchers_2349_);
lean_inc(v_interestingEnums_2348_);
lean_inc(v_interestingStructures_2347_);
lean_dec(v_typeAnalysis_2339_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2364_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2354_ = lean_box(0);
v___x_2355_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2336_, v___x_2337_, v_uninteresting_2350_, v_n_2333_, v___x_2354_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 3, v___x_2355_);
v___x_2357_ = v___x_2352_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_interestingStructures_2347_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_interestingEnums_2348_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_interestingMatchers_2349_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 1, v___x_2357_);
v___x_2359_ = v___x_2345_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_caches_2340_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_target_2341_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_hypotheses_2342_);
lean_ctor_set_uint8(v_reuseFailAlloc_2362_, sizeof(void*)*4, v_didChange_2343_);
v___x_2359_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_st_ref_put(v_a_2334_, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2354_);
return v___x_2361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_2366_, v_a_2367_);
lean_dec(v_a_2367_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_typeAnalysis_2386_; lean_object* v_caches_2387_; lean_object* v_target_2388_; lean_object* v_hypotheses_2389_; uint8_t v_didChange_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2412_; 
v___x_2383_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2384_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2385_ = lean_st_ref_take(v_a_2372_);
v_typeAnalysis_2386_ = lean_ctor_get(v___x_2385_, 1);
v_caches_2387_ = lean_ctor_get(v___x_2385_, 0);
v_target_2388_ = lean_ctor_get(v___x_2385_, 2);
v_hypotheses_2389_ = lean_ctor_get(v___x_2385_, 3);
v_didChange_2390_ = lean_ctor_get_uint8(v___x_2385_, sizeof(void*)*4);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2392_ = v___x_2385_;
v_isShared_2393_ = v_isSharedCheck_2412_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_hypotheses_2389_);
lean_inc(v_target_2388_);
lean_inc(v_typeAnalysis_2386_);
lean_inc(v_caches_2387_);
lean_dec(v___x_2385_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2412_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v_interestingStructures_2394_; lean_object* v_interestingEnums_2395_; lean_object* v_interestingMatchers_2396_; lean_object* v_uninteresting_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2411_; 
v_interestingStructures_2394_ = lean_ctor_get(v_typeAnalysis_2386_, 0);
v_interestingEnums_2395_ = lean_ctor_get(v_typeAnalysis_2386_, 1);
v_interestingMatchers_2396_ = lean_ctor_get(v_typeAnalysis_2386_, 2);
v_uninteresting_2397_ = lean_ctor_get(v_typeAnalysis_2386_, 3);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_typeAnalysis_2386_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2399_ = v_typeAnalysis_2386_;
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_uninteresting_2397_);
lean_inc(v_interestingMatchers_2396_);
lean_inc(v_interestingEnums_2395_);
lean_inc(v_interestingStructures_2394_);
lean_dec(v_typeAnalysis_2386_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2401_ = lean_box(0);
v___x_2402_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2383_, v___x_2384_, v_uninteresting_2397_, v_n_2370_, v___x_2401_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 3, v___x_2402_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_interestingStructures_2394_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_interestingEnums_2395_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_interestingMatchers_2396_);
lean_ctor_set(v_reuseFailAlloc_2410_, 3, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 1, v___x_2404_);
v___x_2406_ = v___x_2392_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_caches_2387_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_target_2388_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_hypotheses_2389_);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, sizeof(void*)*4, v_didChange_2390_);
v___x_2406_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_st_ref_put(v_a_2372_, v___x_2406_);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2401_);
return v___x_2408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
return v_res_2426_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_box(0);
v___x_2428_ = lean_unsigned_to_nat(16u);
v___x_2429_ = lean_mk_array(v___x_2428_, v___x_2427_);
return v___x_2429_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
lean_ctor_set(v___x_2432_, 1, v___x_2430_);
return v___x_2432_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_2434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
lean_ctor_set(v___x_2434_, 2, v___x_2433_);
lean_ctor_set(v___x_2434_, 3, v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_ctx_2437_, lean_object* v_target_2438_, lean_object* v_x_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2450_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2451_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2452_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2453_ = 0;
v___x_2454_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2454_, 0, v___x_2450_);
lean_ctor_set(v___x_2454_, 1, v___x_2451_);
lean_ctor_set(v___x_2454_, 2, v_target_2438_);
lean_ctor_set(v___x_2454_, 3, v___x_2452_);
lean_ctor_set_uint8(v___x_2454_, sizeof(void*)*4, v___x_2453_);
v___x_2455_ = lean_st_mk_ref(v___x_2454_);
lean_inc(v_a_2448_);
lean_inc_ref(v_a_2447_);
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
lean_inc(v_a_2440_);
lean_inc(v___x_2455_);
v___x_2456_ = lean_apply_12(v_x_2439_, v_ctx_2437_, v___x_2455_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, lean_box(0));
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2466_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2466_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2466_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2461_ = lean_st_ref_get(v___x_2455_);
lean_dec(v___x_2455_);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_a_2457_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2462_);
v___x_2464_ = v___x_2459_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v___x_2455_);
v_a_2467_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2456_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2456_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_ctx_2475_, lean_object* v_target_2476_, lean_object* v_x_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_ctx_2475_, v_target_2476_, v_x_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_2489_, lean_object* v_ctx_2490_, lean_object* v_target_2491_, lean_object* v_x_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2503_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2504_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2505_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2506_ = 0;
v___x_2507_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2507_, 0, v___x_2503_);
lean_ctor_set(v___x_2507_, 1, v___x_2504_);
lean_ctor_set(v___x_2507_, 2, v_target_2491_);
lean_ctor_set(v___x_2507_, 3, v___x_2505_);
lean_ctor_set_uint8(v___x_2507_, sizeof(void*)*4, v___x_2506_);
v___x_2508_ = lean_st_mk_ref(v___x_2507_);
lean_inc(v_a_2501_);
lean_inc_ref(v_a_2500_);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
lean_inc(v_a_2497_);
lean_inc_ref(v_a_2496_);
lean_inc(v_a_2495_);
lean_inc_ref(v_a_2494_);
lean_inc(v_a_2493_);
lean_inc(v___x_2508_);
v___x_2509_ = lean_apply_12(v_x_2492_, v_ctx_2490_, v___x_2508_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, lean_box(0));
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2519_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2519_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2519_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2514_ = lean_st_ref_get(v___x_2508_);
lean_dec(v___x_2508_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_a_2510_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2515_);
v___x_2517_ = v___x_2512_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v___x_2508_);
v_a_2520_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2509_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2509_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_2528_, lean_object* v_ctx_2529_, lean_object* v_target_2530_, lean_object* v_x_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_2528_, v_ctx_2529_, v_target_2530_, v_x_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_ctx_2543_, lean_object* v_target_2544_, lean_object* v_x_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2556_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2557_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2558_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2559_ = 0;
v___x_2560_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2560_, 0, v___x_2556_);
lean_ctor_set(v___x_2560_, 1, v___x_2557_);
lean_ctor_set(v___x_2560_, 2, v_target_2544_);
lean_ctor_set(v___x_2560_, 3, v___x_2558_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*4, v___x_2559_);
v___x_2561_ = lean_st_mk_ref(v___x_2560_);
lean_inc(v_a_2554_);
lean_inc_ref(v_a_2553_);
lean_inc(v_a_2552_);
lean_inc_ref(v_a_2551_);
lean_inc(v_a_2550_);
lean_inc_ref(v_a_2549_);
lean_inc(v_a_2548_);
lean_inc_ref(v_a_2547_);
lean_inc(v_a_2546_);
lean_inc(v___x_2561_);
v___x_2562_ = lean_apply_12(v_x_2545_, v_ctx_2543_, v___x_2561_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, lean_box(0));
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2571_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = lean_st_ref_get(v___x_2561_);
lean_dec(v___x_2561_);
lean_dec(v___x_2567_);
if (v_isShared_2566_ == 0)
{
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2563_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
else
{
lean_dec(v___x_2561_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_ctx_2572_, lean_object* v_target_2573_, lean_object* v_x_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_ctx_2572_, v_target_2573_, v_x_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_2586_, lean_object* v_ctx_2587_, lean_object* v_target_2588_, lean_object* v_x_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2600_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__2);
v___x_2601_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2602_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2603_ = 0;
v___x_2604_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2604_, 0, v___x_2600_);
lean_ctor_set(v___x_2604_, 1, v___x_2601_);
lean_ctor_set(v___x_2604_, 2, v_target_2588_);
lean_ctor_set(v___x_2604_, 3, v___x_2602_);
lean_ctor_set_uint8(v___x_2604_, sizeof(void*)*4, v___x_2603_);
v___x_2605_ = lean_st_mk_ref(v___x_2604_);
lean_inc(v_a_2598_);
lean_inc_ref(v_a_2597_);
lean_inc(v_a_2596_);
lean_inc_ref(v_a_2595_);
lean_inc(v_a_2594_);
lean_inc_ref(v_a_2593_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc(v___x_2605_);
v___x_2606_ = lean_apply_12(v_x_2589_, v_ctx_2587_, v___x_2605_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, lean_box(0));
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2615_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_st_ref_get(v___x_2605_);
lean_dec(v___x_2605_);
lean_dec(v___x_2611_);
if (v_isShared_2610_ == 0)
{
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2607_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
else
{
lean_dec(v___x_2605_);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_2616_, lean_object* v_ctx_2617_, lean_object* v_target_2618_, lean_object* v_x_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_2616_, v_ctx_2617_, v_target_2618_, v_x_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
return v_res_2630_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2634_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2635_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2634_, v___x_2633_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___f_2637_; lean_object* v___x_2638_; 
v___x_2636_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2);
v___f_2637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2638_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2637_, v___x_2636_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3);
v___x_2640_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2641_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2640_, v___x_2639_);
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___f_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4);
v___f_2643_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2644_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2643_, v___x_2642_);
return v___x_2644_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2645_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5);
v___x_2646_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2647_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2646_, v___x_2645_);
return v___x_2647_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; 
v___x_2648_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6);
v___f_2649_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2650_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2649_, v___x_2648_);
return v___x_2650_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___f_2652_; lean_object* v___x_2653_; 
v___x_2651_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7);
v___f_2652_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2653_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2652_, v___x_2651_);
return v___x_2653_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___x_2655_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2656_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2655_, v___x_2654_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___f_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___f_2658_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___x_2659_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2658_, v___x_2657_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2662_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2663_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2664_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2665_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2664_, v___x_2663_, v___x_2662_);
return v___x_2665_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___f_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; 
v___x_2666_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___f_2667_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2668_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2669_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2668_, v___f_2667_, v___x_2666_);
return v___x_2669_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2670_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14);
v___x_2671_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2672_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2673_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2672_, v___x_2671_, v___x_2670_);
return v___x_2673_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___f_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; 
v___x_2674_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15);
v___f_2675_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2676_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2677_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2676_, v___f_2675_, v___x_2674_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2678_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16);
v___x_2679_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2680_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2681_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2680_, v___x_2679_, v___x_2678_);
return v___x_2681_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___f_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; 
v___x_2682_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17);
v___f_2683_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2684_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2685_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2684_, v___f_2683_, v___x_2682_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___f_2687_; lean_object* v___f_2688_; lean_object* v___x_2689_; 
v___x_2686_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18);
v___f_2687_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2688_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2689_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2688_, v___f_2687_, v___x_2686_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2690_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19);
v___x_2691_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2692_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12));
v___x_2693_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2692_, v___x_2691_, v___x_2690_);
return v___x_2693_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; 
v___x_2694_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___f_2695_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2696_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11));
v___x_2697_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2696_, v___f_2695_, v___x_2694_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v_cls_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_cls_2708_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2709_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_2710_ = l_Lean_Name_append(v___x_2709_, v_cls_2708_);
return v___x_2710_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___f_2713_; 
v___x_2711_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___x_2712_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2713_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2713_, 0, v___x_2712_);
lean_closure_set(v___f_2713_, 1, v___x_2711_);
return v___f_2713_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___f_2714_; lean_object* v___f_2715_; lean_object* v___f_2716_; 
v___f_2714_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2715_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___f_2716_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2716_, 0, v___f_2715_);
lean_closure_set(v___f_2716_, 1, v___f_2714_);
return v___f_2716_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___f_2718_; lean_object* v___f_2719_; 
v___x_2717_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2718_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_2719_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2719_, 0, v___f_2718_);
lean_closure_set(v___f_2719_, 1, v___x_2717_);
return v___f_2719_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___f_2720_; lean_object* v___f_2721_; lean_object* v___f_2722_; 
v___f_2720_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2721_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_2722_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2722_, 0, v___f_2721_);
lean_closure_set(v___f_2722_, 1, v___f_2720_);
return v___f_2722_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33(void){
_start:
{
lean_object* v___f_2723_; lean_object* v___f_2724_; lean_object* v___f_2725_; 
v___f_2723_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2724_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___f_2725_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2725_, 0, v___f_2724_);
lean_closure_set(v___f_2725_, 1, v___f_2723_);
return v___f_2725_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___f_2727_; lean_object* v___f_2728_; 
v___x_2726_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1));
v___f_2727_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33);
v___f_2728_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2728_, 0, v___f_2727_);
lean_closure_set(v___f_2728_, 1, v___x_2726_);
return v___f_2728_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35(void){
_start:
{
lean_object* v___f_2729_; lean_object* v___f_2730_; lean_object* v___f_2731_; 
v___f_2729_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0));
v___f_2730_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v___f_2731_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2731_, 0, v___f_2730_);
lean_closure_set(v___f_2731_, 1, v___f_2729_);
return v___f_2731_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36));
v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v___y_2749_; lean_object* v___x_2767_; lean_object* v_toApplicative_2768_; lean_object* v_toFunctor_2769_; lean_object* v_toSeq_2770_; lean_object* v_toSeqLeft_2771_; lean_object* v_toSeqRight_2772_; lean_object* v___f_2773_; lean_object* v___f_2774_; lean_object* v___f_2775_; lean_object* v___f_2776_; lean_object* v___x_2777_; lean_object* v___f_2778_; lean_object* v___f_2779_; lean_object* v___f_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v_toApplicative_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2835_; 
v___x_2767_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2768_ = lean_ctor_get(v___x_2767_, 0);
v_toFunctor_2769_ = lean_ctor_get(v_toApplicative_2768_, 0);
v_toSeq_2770_ = lean_ctor_get(v_toApplicative_2768_, 2);
v_toSeqLeft_2771_ = lean_ctor_get(v_toApplicative_2768_, 3);
v_toSeqRight_2772_ = lean_ctor_get(v_toApplicative_2768_, 4);
v___f_2773_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2774_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2769_, 2);
v___f_2775_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2775_, 0, v_toFunctor_2769_);
v___f_2776_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2776_, 0, v_toFunctor_2769_);
v___x_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___f_2775_);
lean_ctor_set(v___x_2777_, 1, v___f_2776_);
lean_inc(v_toSeqRight_2772_);
v___f_2778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2778_, 0, v_toSeqRight_2772_);
lean_inc(v_toSeqLeft_2771_);
v___f_2779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2779_, 0, v_toSeqLeft_2771_);
lean_inc(v_toSeq_2770_);
v___f_2780_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2780_, 0, v_toSeq_2770_);
v___x_2781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2777_);
lean_ctor_set(v___x_2781_, 1, v___f_2773_);
lean_ctor_set(v___x_2781_, 2, v___f_2780_);
lean_ctor_set(v___x_2781_, 3, v___f_2779_);
lean_ctor_set(v___x_2781_, 4, v___f_2778_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v___f_2774_);
v___x_2783_ = l_StateRefT_x27_instMonad___redArg(v___x_2782_);
v_toApplicative_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2783_, 1);
lean_dec(v_unused_2836_);
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2835_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_toApplicative_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2835_;
goto v_resetjp_2785_;
}
v___jp_2748_:
{
lean_object* v___x_2750_; lean_object* v_caches_2751_; lean_object* v_typeAnalysis_2752_; lean_object* v_target_2753_; lean_object* v_hypotheses_2754_; uint8_t v_didChange_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2766_; 
v___x_2750_ = lean_st_ref_take(v___y_2749_);
v_caches_2751_ = lean_ctor_get(v___x_2750_, 0);
v_typeAnalysis_2752_ = lean_ctor_get(v___x_2750_, 1);
v_target_2753_ = lean_ctor_get(v___x_2750_, 2);
v_hypotheses_2754_ = lean_ctor_get(v___x_2750_, 3);
v_didChange_2755_ = lean_ctor_get_uint8(v___x_2750_, sizeof(void*)*4);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2757_ = v___x_2750_;
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_hypotheses_2754_);
lean_inc(v_target_2753_);
lean_inc(v_typeAnalysis_2752_);
lean_inc(v_caches_2751_);
lean_dec(v___x_2750_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2759_ = lean_box(0);
v___x_2760_ = lean_array_push(v_hypotheses_2754_, v_hyp_2735_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 3, v___x_2760_);
v___x_2762_ = v___x_2757_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_caches_2751_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_typeAnalysis_2752_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_target_2753_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v___x_2760_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*4, v_didChange_2755_);
v___x_2762_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_st_ref_put(v___y_2749_, v___x_2762_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2759_);
return v___x_2764_;
}
}
}
v_resetjp_2785_:
{
lean_object* v_toFunctor_2788_; lean_object* v_toSeq_2789_; lean_object* v_toSeqLeft_2790_; lean_object* v_toSeqRight_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2833_; 
v_toFunctor_2788_ = lean_ctor_get(v_toApplicative_2784_, 0);
v_toSeq_2789_ = lean_ctor_get(v_toApplicative_2784_, 2);
v_toSeqLeft_2790_ = lean_ctor_get(v_toApplicative_2784_, 3);
v_toSeqRight_2791_ = lean_ctor_get(v_toApplicative_2784_, 4);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_toApplicative_2784_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v_toApplicative_2784_, 1);
lean_dec(v_unused_2834_);
v___x_2793_ = v_toApplicative_2784_;
v_isShared_2794_ = v_isSharedCheck_2833_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_toSeqRight_2791_);
lean_inc(v_toSeqLeft_2790_);
lean_inc(v_toSeq_2789_);
lean_inc(v_toFunctor_2788_);
lean_dec(v_toApplicative_2784_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2833_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v___f_2797_; lean_object* v___f_2798_; lean_object* v___x_2799_; lean_object* v___f_2800_; lean_object* v___f_2801_; lean_object* v___f_2802_; lean_object* v___x_2804_; 
v___f_2795_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2796_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2788_);
v___f_2797_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2797_, 0, v_toFunctor_2788_);
v___f_2798_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2798_, 0, v_toFunctor_2788_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___f_2797_);
lean_ctor_set(v___x_2799_, 1, v___f_2798_);
v___f_2800_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2800_, 0, v_toSeqRight_2791_);
v___f_2801_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2801_, 0, v_toSeqLeft_2790_);
v___f_2802_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2802_, 0, v_toSeq_2789_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 4, v___f_2800_);
lean_ctor_set(v___x_2793_, 3, v___f_2801_);
lean_ctor_set(v___x_2793_, 2, v___f_2802_);
lean_ctor_set(v___x_2793_, 1, v___f_2795_);
lean_ctor_set(v___x_2793_, 0, v___x_2799_);
v___x_2804_ = v___x_2793_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___f_2795_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v___f_2802_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v___f_2801_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v___f_2800_);
v___x_2804_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2806_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 1, v___f_2796_);
lean_ctor_set(v___x_2786_, 0, v___x_2804_);
v___x_2806_ = v___x_2786_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v___f_2796_);
v___x_2806_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v_toCold_2816_; lean_object* v_options_2817_; uint8_t v_hasTrace_2818_; 
v___x_2807_ = l_StateRefT_x27_instMonad___redArg(v___x_2806_);
v___x_2808_ = l_ReaderT_instMonad___redArg(v___x_2807_);
v___x_2809_ = l_StateRefT_x27_instMonad___redArg(v___x_2808_);
v___x_2810_ = l_ReaderT_instMonad___redArg(v___x_2809_);
v___x_2811_ = l_ReaderT_instMonad___redArg(v___x_2810_);
v___x_2812_ = l_StateRefT_x27_instMonad___redArg(v___x_2811_);
v___x_2813_ = l_ReaderT_instMonad___redArg(v___x_2812_);
v___x_2814_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2815_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toCold_2816_ = lean_ctor_get(v_a_2745_, 0);
v_options_2817_ = lean_ctor_get(v_toCold_2816_, 2);
v_hasTrace_2818_ = lean_ctor_get_uint8(v_options_2817_, sizeof(void*)*1);
if (v_hasTrace_2818_ == 0)
{
lean_dec_ref(v___x_2813_);
v___y_2749_ = v_a_2737_;
goto v___jp_2748_;
}
else
{
lean_object* v_toMonadRef_2819_; lean_object* v_inheritedTraceOptions_2820_; lean_object* v_cls_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_toMonadRef_2819_ = lean_ctor_get(v___x_2815_, 0);
v_inheritedTraceOptions_2820_ = lean_ctor_get(v_toCold_2816_, 11);
v_cls_2821_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2820_, v_options_2817_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_dec_ref(v___x_2813_);
v___y_2749_ = v_a_2737_;
goto v___jp_2748_;
}
else
{
lean_object* v_type_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_5398__overap_2829_; lean_object* v___x_2830_; 
v_type_2824_ = lean_ctor_get(v_hyp_2735_, 1);
v___f_2825_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_2826_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
lean_inc_ref(v_type_2824_);
v___x_2827_ = l_Lean_MessageData_ofExpr(v_type_2824_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
lean_inc_ref(v_toMonadRef_2819_);
v___x_5398__overap_2829_ = l_Lean_addTrace___redArg(v___x_2813_, v___x_2814_, v_toMonadRef_2819_, v___f_2825_, v_cls_2821_, v___x_2828_);
lean_inc(v_a_2746_);
lean_inc_ref(v_a_2745_);
lean_inc(v_a_2744_);
lean_inc_ref(v_a_2743_);
lean_inc(v_a_2742_);
lean_inc_ref(v_a_2741_);
lean_inc(v_a_2740_);
lean_inc_ref(v_a_2739_);
lean_inc(v_a_2738_);
lean_inc(v_a_2737_);
lean_inc_ref(v_a_2736_);
v___x_2830_ = lean_apply_12(v___x_5398__overap_2829_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, lean_box(0));
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_dec_ref_known(v___x_2830_, 1);
v___y_2749_ = v_a_2737_;
goto v___jp_2748_;
}
else
{
lean_dec_ref(v_hyp_2735_);
return v___x_2830_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2851_, lean_object* v___x_2852_, lean_object* v_toMonadRef_2853_, lean_object* v___f_2854_, lean_object* v_x_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_toCold_2872_; lean_object* v_options_2873_; uint8_t v_hasTrace_2874_; 
v_toCold_2872_ = lean_ctor_get(v___y_2866_, 0);
v_options_2873_ = lean_ctor_get(v_toCold_2872_, 2);
v_hasTrace_2874_ = lean_ctor_get_uint8(v_options_2873_, sizeof(void*)*1);
if (v_hasTrace_2874_ == 0)
{
lean_dec_ref(v___y_2856_);
lean_dec(v___f_2854_);
lean_dec_ref(v_toMonadRef_2853_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v___x_2851_);
goto v___jp_2869_;
}
else
{
lean_object* v_inheritedTraceOptions_2875_; lean_object* v_cls_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v_inheritedTraceOptions_2875_ = lean_ctor_get(v_toCold_2872_, 11);
v_cls_2876_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2877_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_2878_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2875_, v_options_2873_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_dec_ref(v___y_2856_);
lean_dec(v___f_2854_);
lean_dec_ref(v_toMonadRef_2853_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v___x_2851_);
goto v___jp_2869_;
}
else
{
lean_object* v_type_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_6393__overap_2883_; lean_object* v___x_2884_; 
v_type_2879_ = lean_ctor_get(v___y_2856_, 1);
lean_inc_ref(v_type_2879_);
lean_dec_ref(v___y_2856_);
v___x_2880_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___x_2881_ = l_Lean_MessageData_ofExpr(v_type_2879_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_6393__overap_2883_ = l_Lean_addTrace___redArg(v___x_2851_, v___x_2852_, v_toMonadRef_2853_, v___f_2854_, v_cls_2876_, v___x_2882_);
lean_inc(v___y_2867_);
lean_inc_ref(v___y_2866_);
lean_inc(v___y_2865_);
lean_inc_ref(v___y_2864_);
lean_inc(v___y_2863_);
lean_inc_ref(v___y_2862_);
lean_inc(v___y_2861_);
lean_inc_ref(v___y_2860_);
lean_inc(v___y_2859_);
lean_inc(v___y_2858_);
lean_inc_ref(v___y_2857_);
v___x_2884_ = lean_apply_12(v___x_6393__overap_2883_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, lean_box(0));
return v___x_2884_;
}
}
v___jp_2869_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_box(0);
v___x_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2885_ = _args[0];
lean_object* v___x_2886_ = _args[1];
lean_object* v_toMonadRef_2887_ = _args[2];
lean_object* v___f_2888_ = _args[3];
lean_object* v_x_2889_ = _args[4];
lean_object* v___y_2890_ = _args[5];
lean_object* v___y_2891_ = _args[6];
lean_object* v___y_2892_ = _args[7];
lean_object* v___y_2893_ = _args[8];
lean_object* v___y_2894_ = _args[9];
lean_object* v___y_2895_ = _args[10];
lean_object* v___y_2896_ = _args[11];
lean_object* v___y_2897_ = _args[12];
lean_object* v___y_2898_ = _args[13];
lean_object* v___y_2899_ = _args[14];
lean_object* v___y_2900_ = _args[15];
lean_object* v___y_2901_ = _args[16];
lean_object* v___y_2902_ = _args[17];
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2885_, v___x_2886_, v_toMonadRef_2887_, v___f_2888_, v_x_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v___x_2935_; lean_object* v_toApplicative_2936_; lean_object* v_toFunctor_2937_; lean_object* v_toSeq_2938_; lean_object* v_toSeqLeft_2939_; lean_object* v_toSeqRight_2940_; lean_object* v___f_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___x_2945_; lean_object* v___f_2946_; lean_object* v___f_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v_toApplicative_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2999_; 
v___x_2935_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_2936_ = lean_ctor_get(v___x_2935_, 0);
v_toFunctor_2937_ = lean_ctor_get(v_toApplicative_2936_, 0);
v_toSeq_2938_ = lean_ctor_get(v_toApplicative_2936_, 2);
v_toSeqLeft_2939_ = lean_ctor_get(v_toApplicative_2936_, 3);
v_toSeqRight_2940_ = lean_ctor_get(v_toApplicative_2936_, 4);
v___f_2941_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_2942_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_2937_, 2);
v___f_2943_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2943_, 0, v_toFunctor_2937_);
v___f_2944_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2944_, 0, v_toFunctor_2937_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___f_2943_);
lean_ctor_set(v___x_2945_, 1, v___f_2944_);
lean_inc(v_toSeqRight_2940_);
v___f_2946_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2946_, 0, v_toSeqRight_2940_);
lean_inc(v_toSeqLeft_2939_);
v___f_2947_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2947_, 0, v_toSeqLeft_2939_);
lean_inc(v_toSeq_2938_);
v___f_2948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2948_, 0, v_toSeq_2938_);
v___x_2949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2945_);
lean_ctor_set(v___x_2949_, 1, v___f_2941_);
lean_ctor_set(v___x_2949_, 2, v___f_2948_);
lean_ctor_set(v___x_2949_, 3, v___f_2947_);
lean_ctor_set(v___x_2949_, 4, v___f_2946_);
v___x_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v___f_2942_);
v___x_2951_ = l_StateRefT_x27_instMonad___redArg(v___x_2950_);
v_toApplicative_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v___x_2951_, 1);
lean_dec(v_unused_3000_);
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2999_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_toApplicative_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2999_;
goto v_resetjp_2953_;
}
v___jp_2917_:
{
lean_object* v___x_2918_; lean_object* v_caches_2919_; lean_object* v_typeAnalysis_2920_; lean_object* v_target_2921_; lean_object* v_hypotheses_2922_; uint8_t v_didChange_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2934_; 
v___x_2918_ = lean_st_ref_take(v_a_2906_);
v_caches_2919_ = lean_ctor_get(v___x_2918_, 0);
v_typeAnalysis_2920_ = lean_ctor_get(v___x_2918_, 1);
v_target_2921_ = lean_ctor_get(v___x_2918_, 2);
v_hypotheses_2922_ = lean_ctor_get(v___x_2918_, 3);
v_didChange_2923_ = lean_ctor_get_uint8(v___x_2918_, sizeof(void*)*4);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2925_ = v___x_2918_;
v_isShared_2926_ = v_isSharedCheck_2934_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_hypotheses_2922_);
lean_inc(v_target_2921_);
lean_inc(v_typeAnalysis_2920_);
lean_inc(v_caches_2919_);
lean_dec(v___x_2918_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2934_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2927_ = lean_box(0);
v___x_2928_ = l_Array_append___redArg(v_hypotheses_2922_, v_hyps_2904_);
lean_dec_ref(v_hyps_2904_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 3, v___x_2928_);
v___x_2930_ = v___x_2925_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_caches_2919_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_typeAnalysis_2920_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_target_2921_);
lean_ctor_set(v_reuseFailAlloc_2933_, 3, v___x_2928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2933_, sizeof(void*)*4, v_didChange_2923_);
v___x_2930_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_st_ref_put(v_a_2906_, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2927_);
return v___x_2932_;
}
}
}
v_resetjp_2953_:
{
lean_object* v_toFunctor_2956_; lean_object* v_toSeq_2957_; lean_object* v_toSeqLeft_2958_; lean_object* v_toSeqRight_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2997_; 
v_toFunctor_2956_ = lean_ctor_get(v_toApplicative_2952_, 0);
v_toSeq_2957_ = lean_ctor_get(v_toApplicative_2952_, 2);
v_toSeqLeft_2958_ = lean_ctor_get(v_toApplicative_2952_, 3);
v_toSeqRight_2959_ = lean_ctor_get(v_toApplicative_2952_, 4);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_toApplicative_2952_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v_toApplicative_2952_, 1);
lean_dec(v_unused_2998_);
v___x_2961_ = v_toApplicative_2952_;
v_isShared_2962_ = v_isSharedCheck_2997_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_toSeqRight_2959_);
lean_inc(v_toSeqLeft_2958_);
lean_inc(v_toSeq_2957_);
lean_inc(v_toFunctor_2956_);
lean_dec(v_toApplicative_2952_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2997_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___f_2963_; lean_object* v___f_2964_; lean_object* v___f_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___f_2968_; lean_object* v___f_2969_; lean_object* v___f_2970_; lean_object* v___x_2972_; 
v___f_2963_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_2964_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_2956_);
v___f_2965_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2965_, 0, v_toFunctor_2956_);
v___f_2966_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2966_, 0, v_toFunctor_2956_);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___f_2965_);
lean_ctor_set(v___x_2967_, 1, v___f_2966_);
v___f_2968_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2968_, 0, v_toSeqRight_2959_);
v___f_2969_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2969_, 0, v_toSeqLeft_2958_);
v___f_2970_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2970_, 0, v_toSeq_2957_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 4, v___f_2968_);
lean_ctor_set(v___x_2961_, 3, v___f_2969_);
lean_ctor_set(v___x_2961_, 2, v___f_2970_);
lean_ctor_set(v___x_2961_, 1, v___f_2963_);
lean_ctor_set(v___x_2961_, 0, v___x_2967_);
v___x_2972_ = v___x_2961_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v___f_2963_);
lean_ctor_set(v_reuseFailAlloc_2996_, 2, v___f_2970_);
lean_ctor_set(v_reuseFailAlloc_2996_, 3, v___f_2969_);
lean_ctor_set(v_reuseFailAlloc_2996_, 4, v___f_2968_);
v___x_2972_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2974_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___f_2964_);
lean_ctor_set(v___x_2954_, 0, v___x_2972_);
v___x_2974_ = v___x_2954_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___f_2964_);
v___x_2974_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_toMonadRef_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2975_ = l_StateRefT_x27_instMonad___redArg(v___x_2974_);
v___x_2976_ = l_ReaderT_instMonad___redArg(v___x_2975_);
v___x_2977_ = l_StateRefT_x27_instMonad___redArg(v___x_2976_);
v___x_2978_ = l_ReaderT_instMonad___redArg(v___x_2977_);
v___x_2979_ = l_ReaderT_instMonad___redArg(v___x_2978_);
v___x_2980_ = l_StateRefT_x27_instMonad___redArg(v___x_2979_);
v___x_2981_ = l_ReaderT_instMonad___redArg(v___x_2980_);
v___x_2982_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_2983_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_2984_ = lean_ctor_get(v___x_2983_, 0);
v___x_2985_ = lean_unsigned_to_nat(0u);
v___x_2986_ = lean_array_get_size(v_hyps_2904_);
v___x_2987_ = lean_nat_dec_lt(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_dec_ref(v___x_2981_);
goto v___jp_2917_;
}
else
{
lean_object* v___f_2988_; lean_object* v___f_2989_; lean_object* v___x_2990_; size_t v___x_2991_; size_t v___x_2992_; lean_object* v___x_6041__overap_2993_; lean_object* v___x_2994_; 
v___f_2988_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
lean_inc_ref(v_toMonadRef_2984_);
lean_inc_ref(v___x_2981_);
v___f_2989_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 18, 4);
lean_closure_set(v___f_2989_, 0, v___x_2981_);
lean_closure_set(v___f_2989_, 1, v___x_2982_);
lean_closure_set(v___f_2989_, 2, v_toMonadRef_2984_);
lean_closure_set(v___f_2989_, 3, v___f_2988_);
v___x_2990_ = lean_box(0);
v___x_2991_ = ((size_t)0ULL);
v___x_2992_ = lean_usize_of_nat(v___x_2986_);
lean_inc_ref(v_hyps_2904_);
v___x_6041__overap_2993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2981_, v___f_2989_, v_hyps_2904_, v___x_2991_, v___x_2992_, v___x_2990_);
lean_inc(v_a_2915_);
lean_inc_ref(v_a_2914_);
lean_inc(v_a_2913_);
lean_inc_ref(v_a_2912_);
lean_inc(v_a_2911_);
lean_inc_ref(v_a_2910_);
lean_inc(v_a_2909_);
lean_inc_ref(v_a_2908_);
lean_inc(v_a_2907_);
lean_inc(v_a_2906_);
lean_inc_ref(v_a_2905_);
v___x_2994_ = lean_apply_12(v___x_6041__overap_2993_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, lean_box(0));
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_dec_ref_known(v___x_2994_, 1);
goto v___jp_2917_;
}
else
{
lean_dec_ref(v_hyps_2904_);
return v___x_2994_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v_hypotheses_3018_; lean_object* v___x_3019_; 
v___x_3017_ = lean_st_ref_get(v_a_3015_);
v_hypotheses_3018_ = lean_ctor_get(v___x_3017_, 3);
lean_inc_ref(v_hypotheses_3018_);
lean_dec(v___x_3017_);
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_hypotheses_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_3020_);
lean_dec(v_a_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v___x_3035_; lean_object* v_hypotheses_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_st_ref_get(v_a_3024_);
v_hypotheses_3036_ = lean_ctor_get(v___x_3035_, 3);
lean_inc_ref(v_hypotheses_3036_);
lean_dec(v___x_3035_);
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_hypotheses_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v___x_3064_; lean_object* v_caches_3065_; lean_object* v_typeAnalysis_3066_; lean_object* v_target_3067_; uint8_t v_didChange_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3078_; 
v___x_3064_ = lean_st_ref_take(v___y_3053_);
v_caches_3065_ = lean_ctor_get(v___x_3064_, 0);
v_typeAnalysis_3066_ = lean_ctor_get(v___x_3064_, 1);
v_target_3067_ = lean_ctor_get(v___x_3064_, 2);
v_didChange_3068_ = lean_ctor_get_uint8(v___x_3064_, sizeof(void*)*4);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v___x_3064_, 3);
lean_dec(v_unused_3079_);
v___x_3070_ = v___x_3064_;
v_isShared_3071_ = v_isSharedCheck_3078_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_target_3067_);
lean_inc(v_typeAnalysis_3066_);
lean_inc(v_caches_3065_);
lean_dec(v___x_3064_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3078_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3072_ = lean_box(0);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 3, v_hyps_3051_);
v___x_3074_ = v___x_3070_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_caches_3065_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_typeAnalysis_3066_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_target_3067_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_hyps_3051_);
lean_ctor_set_uint8(v_reuseFailAlloc_3077_, sizeof(void*)*4, v_didChange_3068_);
v___x_3074_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_st_ref_put(v___y_3053_, v___x_3074_);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3072_);
return v___x_3076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_3094_, lean_object* v_hyps_3095_){
_start:
{
lean_object* v___f_3096_; lean_object* v___x_3097_; 
v___f_3096_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3096_, 0, v_hyps_3095_);
v___x_3097_ = lean_apply_2(v_inst_3094_, lean_box(0), v___f_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; lean_object* v_caches_3111_; lean_object* v_typeAnalysis_3112_; lean_object* v_target_3113_; uint8_t v_didChange_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3125_; 
v___x_3110_ = lean_st_ref_take(v___y_3099_);
v_caches_3111_ = lean_ctor_get(v___x_3110_, 0);
v_typeAnalysis_3112_ = lean_ctor_get(v___x_3110_, 1);
v_target_3113_ = lean_ctor_get(v___x_3110_, 2);
v_didChange_3114_ = lean_ctor_get_uint8(v___x_3110_, sizeof(void*)*4);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v___x_3110_, 3);
lean_dec(v_unused_3126_);
v___x_3116_ = v___x_3110_;
v_isShared_3117_ = v_isSharedCheck_3125_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_target_3113_);
lean_inc(v_typeAnalysis_3112_);
lean_inc(v_caches_3111_);
lean_dec(v___x_3110_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3125_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3118_ = lean_box(0);
v___x_3119_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 3, v___x_3119_);
v___x_3121_ = v___x_3116_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_caches_3111_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_typeAnalysis_3112_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_target_3113_);
lean_ctor_set(v_reuseFailAlloc_3124_, 3, v___x_3119_);
lean_ctor_set_uint8(v_reuseFailAlloc_3124_, sizeof(void*)*4, v_didChange_3114_);
v___x_3121_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_st_ref_put(v___y_3099_, v___x_3121_);
v___x_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3118_);
return v___x_3123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_3140_, lean_object* v_cls_3141_, lean_object* v_____do__lift_3142_, lean_object* v_____do__lift_3143_){
_start:
{
uint8_t v_hasTrace_3144_; 
v_hasTrace_3144_ = lean_ctor_get_uint8(v_____do__lift_3143_, sizeof(void*)*1);
if (v_hasTrace_3144_ == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec(v_cls_3141_);
v___x_3145_ = lean_box(v_hasTrace_3144_);
v___x_3146_ = lean_apply_2(v_toPure_3140_, lean_box(0), v___x_3145_);
return v___x_3146_;
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3147_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3148_ = l_Lean_Name_append(v___x_3147_, v_cls_3141_);
v___x_3149_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3142_, v_____do__lift_3143_, v___x_3148_);
lean_dec(v___x_3148_);
v___x_3150_ = lean_box(v___x_3149_);
v___x_3151_ = lean_apply_2(v_toPure_3140_, lean_box(0), v___x_3150_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_3152_, lean_object* v_cls_3153_, lean_object* v_____do__lift_3154_, lean_object* v_____do__lift_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_3152_, v_cls_3153_, v_____do__lift_3154_, v_____do__lift_3155_);
lean_dec_ref(v_____do__lift_3155_);
lean_dec_ref(v_____do__lift_3154_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_inst_3157_, lean_object* v_toPure_3158_, lean_object* v_cls_3159_, lean_object* v_toBind_3160_, lean_object* v_____do__lift_3161_){
_start:
{
lean_object* v_getOptionsUnrestricted_3162_; lean_object* v___f_3163_; lean_object* v___x_3164_; 
v_getOptionsUnrestricted_3162_ = lean_ctor_get(v_inst_3157_, 1);
lean_inc(v_getOptionsUnrestricted_3162_);
lean_dec_ref(v_inst_3157_);
v___f_3163_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3163_, 0, v_toPure_3158_);
lean_closure_set(v___f_3163_, 1, v_cls_3159_);
lean_closure_set(v___f_3163_, 2, v_____do__lift_3161_);
v___x_3164_ = lean_apply_4(v_toBind_3160_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3162_, v___f_3163_);
return v___x_3164_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_3167_ = l_Lean_stringToMessageData(v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_3168_, lean_object* v_a_3169_, lean_object* v___y_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_cls_3175_, uint8_t v_____do__lift_3176_){
_start:
{
if (v_____do__lift_3176_ == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
lean_dec(v_cls_3175_);
lean_dec(v_inst_3174_);
lean_dec_ref(v_inst_3173_);
lean_dec_ref(v_inst_3172_);
lean_dec_ref(v_inst_3171_);
lean_dec_ref(v___y_3170_);
lean_dec_ref(v_a_3169_);
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_apply_2(v_toPure_3168_, lean_box(0), v___x_3177_);
return v___x_3178_;
}
else
{
lean_object* v_type_3179_; lean_object* v_type_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v_toPure_3168_);
v_type_3179_ = lean_ctor_get(v_a_3169_, 1);
lean_inc_ref(v_type_3179_);
lean_dec_ref(v_a_3169_);
v_type_3180_ = lean_ctor_get(v___y_3170_, 1);
lean_inc_ref(v_type_3180_);
lean_dec_ref(v___y_3170_);
v___x_3181_ = l_Lean_MessageData_ofExpr(v_type_3179_);
v___x_3182_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3181_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = l_Lean_MessageData_ofExpr(v_type_3180_);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = l_Lean_addTrace___redArg(v_inst_3171_, v_inst_3172_, v_inst_3173_, v_inst_3174_, v_cls_3175_, v___x_3185_);
return v___x_3186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_3187_, lean_object* v_a_3188_, lean_object* v___y_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_inst_3193_, lean_object* v_cls_3194_, lean_object* v_____do__lift_3195_){
_start:
{
uint8_t v_____do__lift_2998__boxed_3196_; lean_object* v_res_3197_; 
v_____do__lift_2998__boxed_3196_ = lean_unbox(v_____do__lift_3195_);
v_res_3197_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_3187_, v_a_3188_, v___y_3189_, v_inst_3190_, v_inst_3191_, v_inst_3192_, v_inst_3193_, v_cls_3194_, v_____do__lift_2998__boxed_3196_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_toPure_3200_, lean_object* v_toBind_3201_, lean_object* v_a_3202_, lean_object* v_inst_3203_, lean_object* v_inst_3204_, lean_object* v_inst_3205_, lean_object* v_x_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_getInheritedTraceOptions_3208_; lean_object* v_cls_3209_; lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_getInheritedTraceOptions_3208_ = lean_ctor_get(v_inst_3198_, 2);
lean_inc(v_getInheritedTraceOptions_3208_);
v_cls_3209_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
lean_inc_n(v_toBind_3201_, 2);
lean_inc(v_toPure_3200_);
v___f_3210_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3210_, 0, v_inst_3199_);
lean_closure_set(v___f_3210_, 1, v_toPure_3200_);
lean_closure_set(v___f_3210_, 2, v_cls_3209_);
lean_closure_set(v___f_3210_, 3, v_toBind_3201_);
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_3211_, 0, v_toPure_3200_);
lean_closure_set(v___f_3211_, 1, v_a_3202_);
lean_closure_set(v___f_3211_, 2, v___y_3207_);
lean_closure_set(v___f_3211_, 3, v_inst_3203_);
lean_closure_set(v___f_3211_, 4, v_inst_3198_);
lean_closure_set(v___f_3211_, 5, v_inst_3204_);
lean_closure_set(v___f_3211_, 6, v_inst_3205_);
lean_closure_set(v___f_3211_, 7, v_cls_3209_);
v___x_3212_ = lean_apply_4(v_toBind_3201_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3208_, v___f_3210_);
v___x_3213_ = lean_apply_4(v_toBind_3201_, lean_box(0), lean_box(0), v___x_3212_, v___f_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_3214_, lean_object* v_res_3215_, lean_object* v_____r_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_apply_2(v_toPure_3214_, lean_box(0), v_res_3215_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_3218_, lean_object* v_toBind_3219_, lean_object* v___f_3220_, lean_object* v_____r_3221_){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_3223_ = lean_apply_2(v_inst_3218_, lean_box(0), v___x_3222_);
v___x_3224_ = lean_apply_4(v_toBind_3219_, lean_box(0), lean_box(0), v___x_3223_, v___f_3220_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_3225_, lean_object* v_____r_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_apply_1(v___f_3225_, v_____r_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_3228_, lean_object* v_type_3229_, lean_object* v_type_3230_, lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_cls_3235_, lean_object* v_toBind_3236_, lean_object* v___f_3237_, uint8_t v_____do__lift_3238_){
_start:
{
if (v_____do__lift_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
lean_dec(v___f_3237_);
lean_dec(v_toBind_3236_);
lean_dec(v_cls_3235_);
lean_dec(v_inst_3234_);
lean_dec_ref(v_inst_3233_);
lean_dec_ref(v_inst_3232_);
lean_dec_ref(v_inst_3231_);
lean_dec_ref(v_type_3230_);
lean_dec_ref(v_type_3229_);
v___x_3239_ = lean_box(0);
v___x_3240_ = lean_apply_1(v___f_3228_, v___x_3239_);
return v___x_3240_;
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_dec(v___f_3228_);
v___x_3241_ = l_Lean_MessageData_ofExpr(v_type_3229_);
v___x_3242_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_MessageData_ofExpr(v_type_3230_);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Lean_addTrace___redArg(v_inst_3231_, v_inst_3232_, v_inst_3233_, v_inst_3234_, v_cls_3235_, v___x_3245_);
v___x_3247_ = lean_apply_4(v_toBind_3236_, lean_box(0), lean_box(0), v___x_3246_, v___f_3237_);
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_3248_, lean_object* v_type_3249_, lean_object* v_type_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_inst_3254_, lean_object* v_cls_3255_, lean_object* v_toBind_3256_, lean_object* v___f_3257_, lean_object* v_____do__lift_3258_){
_start:
{
uint8_t v_____do__lift_3098__boxed_3259_; lean_object* v_res_3260_; 
v_____do__lift_3098__boxed_3259_ = lean_unbox(v_____do__lift_3258_);
v_res_3260_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_3248_, v_type_3249_, v_type_3250_, v_inst_3251_, v_inst_3252_, v_inst_3253_, v_inst_3254_, v_cls_3255_, v_toBind_3256_, v___f_3257_, v_____do__lift_3098__boxed_3259_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_3261_, lean_object* v_inst_3262_, lean_object* v_toBind_3263_, lean_object* v_inst_3264_, lean_object* v___f_3265_, lean_object* v_a_3266_, lean_object* v_inst_3267_, lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_inst_3270_, lean_object* v___f_3271_, lean_object* v_res_3272_){
_start:
{
lean_object* v___x_3273_; lean_object* v_zero_3274_; uint8_t v_isZero_3275_; 
v___x_3273_ = lean_array_get_size(v_res_3272_);
v_zero_3274_ = lean_unsigned_to_nat(0u);
v_isZero_3275_ = lean_nat_dec_eq(v___x_3273_, v_zero_3274_);
if (v_isZero_3275_ == 1)
{
lean_object* v___f_3276_; lean_object* v___f_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
lean_dec(v___f_3271_);
lean_dec(v_inst_3270_);
lean_dec_ref(v_inst_3269_);
lean_dec_ref(v_inst_3268_);
lean_dec_ref(v_inst_3267_);
lean_dec_ref(v_a_3266_);
lean_inc_ref(v_res_3272_);
lean_inc(v_toPure_3261_);
v___f_3276_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3276_, 0, v_toPure_3261_);
lean_closure_set(v___f_3276_, 1, v_res_3272_);
lean_inc(v_toBind_3263_);
v___f_3277_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3277_, 0, v_inst_3262_);
lean_closure_set(v___f_3277_, 1, v_toBind_3263_);
lean_closure_set(v___f_3277_, 2, v___f_3276_);
v___x_3278_ = lean_box(0);
v___x_3279_ = lean_nat_dec_lt(v_zero_3274_, v___x_3273_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec_ref(v_res_3272_);
lean_dec(v___f_3265_);
lean_dec_ref(v_inst_3264_);
v___x_3280_ = lean_apply_2(v_toPure_3261_, lean_box(0), v___x_3278_);
v___x_3281_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3280_, v___f_3277_);
return v___x_3281_;
}
else
{
size_t v___x_3282_; size_t v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v_toPure_3261_);
v___x_3282_ = ((size_t)0ULL);
v___x_3283_ = lean_usize_of_nat(v___x_3273_);
v___x_3284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3264_, v___f_3265_, v_res_3272_, v___x_3282_, v___x_3283_, v___x_3278_);
v___x_3285_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3284_, v___f_3277_);
return v___x_3285_;
}
}
else
{
lean_object* v_one_3286_; lean_object* v_n_3287_; uint8_t v_isZero_3288_; 
lean_dec(v___f_3265_);
v_one_3286_ = lean_unsigned_to_nat(1u);
v_n_3287_ = lean_nat_sub(v___x_3273_, v_one_3286_);
v_isZero_3288_ = lean_nat_dec_eq(v_n_3287_, v_zero_3274_);
lean_dec(v_n_3287_);
if (v_isZero_3288_ == 1)
{
lean_object* v_newHyp_3289_; lean_object* v_type_3290_; lean_object* v_type_3291_; uint8_t v___x_3292_; 
lean_dec(v___f_3271_);
v_newHyp_3289_ = lean_array_fget_borrowed(v_res_3272_, v_zero_3274_);
v_type_3290_ = lean_ctor_get(v_newHyp_3289_, 1);
v_type_3291_ = lean_ctor_get(v_a_3266_, 1);
lean_inc_ref(v_type_3291_);
lean_dec_ref(v_a_3266_);
v___x_3292_ = lean_expr_eqv(v_type_3290_, v_type_3291_);
if (v___x_3292_ == 0)
{
lean_object* v_getInheritedTraceOptions_3293_; lean_object* v___f_3294_; lean_object* v___f_3295_; lean_object* v___f_3296_; lean_object* v_cls_3297_; lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_inc_ref(v_type_3290_);
v_getInheritedTraceOptions_3293_ = lean_ctor_get(v_inst_3267_, 2);
lean_inc(v_getInheritedTraceOptions_3293_);
lean_inc(v_toPure_3261_);
v___f_3294_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3294_, 0, v_toPure_3261_);
lean_closure_set(v___f_3294_, 1, v_res_3272_);
lean_inc_n(v_toBind_3263_, 4);
v___f_3295_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3295_, 0, v_inst_3262_);
lean_closure_set(v___f_3295_, 1, v_toBind_3263_);
lean_closure_set(v___f_3295_, 2, v___f_3294_);
lean_inc_ref(v___f_3295_);
v___f_3296_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3296_, 0, v___f_3295_);
v_cls_3297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3298_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3298_, 0, v_inst_3268_);
lean_closure_set(v___f_3298_, 1, v_toPure_3261_);
lean_closure_set(v___f_3298_, 2, v_cls_3297_);
lean_closure_set(v___f_3298_, 3, v_toBind_3263_);
v___f_3299_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3299_, 0, v___f_3295_);
lean_closure_set(v___f_3299_, 1, v_type_3291_);
lean_closure_set(v___f_3299_, 2, v_type_3290_);
lean_closure_set(v___f_3299_, 3, v_inst_3264_);
lean_closure_set(v___f_3299_, 4, v_inst_3267_);
lean_closure_set(v___f_3299_, 5, v_inst_3269_);
lean_closure_set(v___f_3299_, 6, v_inst_3270_);
lean_closure_set(v___f_3299_, 7, v_cls_3297_);
lean_closure_set(v___f_3299_, 8, v_toBind_3263_);
lean_closure_set(v___f_3299_, 9, v___f_3296_);
v___x_3300_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3293_, v___f_3298_);
v___x_3301_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3300_, v___f_3299_);
return v___x_3301_;
}
else
{
lean_object* v___x_3302_; 
lean_dec_ref(v_type_3291_);
lean_dec(v_inst_3270_);
lean_dec_ref(v_inst_3269_);
lean_dec_ref(v_inst_3268_);
lean_dec_ref(v_inst_3267_);
lean_dec_ref(v_inst_3264_);
lean_dec(v_toBind_3263_);
lean_dec(v_inst_3262_);
v___x_3302_ = lean_apply_2(v_toPure_3261_, lean_box(0), v_res_3272_);
return v___x_3302_;
}
}
else
{
lean_object* v___f_3303_; lean_object* v___f_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
lean_dec(v_inst_3270_);
lean_dec_ref(v_inst_3269_);
lean_dec_ref(v_inst_3268_);
lean_dec_ref(v_inst_3267_);
lean_dec_ref(v_a_3266_);
lean_inc_ref(v_res_3272_);
lean_inc(v_toPure_3261_);
v___f_3303_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3303_, 0, v_toPure_3261_);
lean_closure_set(v___f_3303_, 1, v_res_3272_);
lean_inc(v_toBind_3263_);
v___f_3304_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3304_, 0, v_inst_3262_);
lean_closure_set(v___f_3304_, 1, v_toBind_3263_);
lean_closure_set(v___f_3304_, 2, v___f_3303_);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_nat_dec_lt(v_zero_3274_, v___x_3273_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
lean_dec_ref(v_res_3272_);
lean_dec(v___f_3271_);
lean_dec_ref(v_inst_3264_);
v___x_3307_ = lean_apply_2(v_toPure_3261_, lean_box(0), v___x_3305_);
v___x_3308_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3307_, v___f_3304_);
return v___x_3308_;
}
else
{
size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
lean_dec(v_toPure_3261_);
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = lean_usize_of_nat(v___x_3273_);
v___x_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3264_, v___f_3271_, v_res_3272_, v___x_3309_, v___x_3310_, v___x_3305_);
v___x_3312_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3311_, v___f_3304_);
return v___x_3312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3313_, lean_object* v_toPure_3314_, lean_object* v_____do__lift_3315_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = l_Array_append___redArg(v_bs_3313_, v_____do__lift_3315_);
v___x_3317_ = lean_apply_2(v_toPure_3314_, lean_box(0), v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3318_, lean_object* v_toPure_3319_, lean_object* v_____do__lift_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3318_, v_toPure_3319_, v_____do__lift_3320_);
lean_dec_ref(v_____do__lift_3320_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_toPure_3324_, lean_object* v_toBind_3325_, lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_f_3330_, lean_object* v_bs_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v___f_3333_; lean_object* v___f_3334_; lean_object* v___f_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_inc(v_inst_3328_);
lean_inc_ref(v_inst_3327_);
lean_inc_ref(v_inst_3326_);
lean_inc_ref_n(v_a_3332_, 2);
lean_inc_n(v_toBind_3325_, 3);
lean_inc_n(v_toPure_3324_, 2);
lean_inc_ref(v_inst_3323_);
lean_inc_ref(v_inst_3322_);
v___f_3333_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3333_, 0, v_inst_3322_);
lean_closure_set(v___f_3333_, 1, v_inst_3323_);
lean_closure_set(v___f_3333_, 2, v_toPure_3324_);
lean_closure_set(v___f_3333_, 3, v_toBind_3325_);
lean_closure_set(v___f_3333_, 4, v_a_3332_);
lean_closure_set(v___f_3333_, 5, v_inst_3326_);
lean_closure_set(v___f_3333_, 6, v_inst_3327_);
lean_closure_set(v___f_3333_, 7, v_inst_3328_);
lean_inc_ref(v___f_3333_);
v___f_3334_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3334_, 0, v_toPure_3324_);
lean_closure_set(v___f_3334_, 1, v_inst_3329_);
lean_closure_set(v___f_3334_, 2, v_toBind_3325_);
lean_closure_set(v___f_3334_, 3, v_inst_3326_);
lean_closure_set(v___f_3334_, 4, v___f_3333_);
lean_closure_set(v___f_3334_, 5, v_a_3332_);
lean_closure_set(v___f_3334_, 6, v_inst_3322_);
lean_closure_set(v___f_3334_, 7, v_inst_3323_);
lean_closure_set(v___f_3334_, 8, v_inst_3327_);
lean_closure_set(v___f_3334_, 9, v_inst_3328_);
lean_closure_set(v___f_3334_, 10, v___f_3333_);
v___f_3335_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3335_, 0, v_bs_3331_);
lean_closure_set(v___f_3335_, 1, v_toPure_3324_);
v___x_3336_ = lean_apply_1(v_f_3330_, v_a_3332_);
v___x_3337_ = lean_apply_4(v_toBind_3325_, lean_box(0), lean_box(0), v___x_3336_, v___f_3334_);
v___x_3338_ = lean_apply_4(v_toBind_3325_, lean_box(0), lean_box(0), v___x_3337_, v___f_3335_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3341_, lean_object* v_toPure_3342_, lean_object* v_toBind_3343_, lean_object* v___f_3344_, lean_object* v_inst_3345_, lean_object* v___f_3346_, lean_object* v_____r_3347_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3348_ = lean_unsigned_to_nat(0u);
v___x_3349_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3350_ = lean_array_get_size(v_hyps_3341_);
v___x_3351_ = lean_nat_dec_lt(v___x_3348_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec(v___f_3346_);
lean_dec_ref(v_inst_3345_);
lean_dec_ref(v_hyps_3341_);
v___x_3352_ = lean_apply_2(v_toPure_3342_, lean_box(0), v___x_3349_);
v___x_3353_ = lean_apply_4(v_toBind_3343_, lean_box(0), lean_box(0), v___x_3352_, v___f_3344_);
return v___x_3353_;
}
else
{
size_t v___x_3354_; size_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec(v_toPure_3342_);
v___x_3354_ = ((size_t)0ULL);
v___x_3355_ = lean_usize_of_nat(v___x_3350_);
v___x_3356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3345_, v___f_3346_, v_hyps_3341_, v___x_3354_, v___x_3355_, v___x_3349_);
v___x_3357_ = lean_apply_4(v_toBind_3343_, lean_box(0), lean_box(0), v___x_3356_, v___f_3344_);
return v___x_3357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3358_, lean_object* v_toBind_3359_, lean_object* v___f_3360_, lean_object* v_inst_3361_, lean_object* v___f_3362_, lean_object* v_inst_3363_, lean_object* v___f_3364_, lean_object* v_hyps_3365_){
_start:
{
lean_object* v___f_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_inc(v_toBind_3359_);
v___f_3366_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3366_, 0, v_hyps_3365_);
lean_closure_set(v___f_3366_, 1, v_toPure_3358_);
lean_closure_set(v___f_3366_, 2, v_toBind_3359_);
lean_closure_set(v___f_3366_, 3, v___f_3360_);
lean_closure_set(v___f_3366_, 4, v_inst_3361_);
lean_closure_set(v___f_3366_, 5, v___f_3362_);
v___x_3367_ = lean_apply_2(v_inst_3363_, lean_box(0), v___f_3364_);
v___x_3368_ = lean_apply_4(v_toBind_3359_, lean_box(0), lean_box(0), v___x_3367_, v___f_3366_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_inst_3372_, lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_inst_3375_, lean_object* v_f_3376_){
_start:
{
lean_object* v_toApplicative_3377_; lean_object* v_toBind_3378_; lean_object* v_toPure_3379_; lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___f_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; 
v_toApplicative_3377_ = lean_ctor_get(v_inst_3370_, 0);
v_toBind_3378_ = lean_ctor_get(v_inst_3370_, 1);
lean_inc_n(v_toBind_3378_, 3);
v_toPure_3379_ = lean_ctor_get(v_toApplicative_3377_, 1);
lean_inc_n(v_toPure_3379_, 2);
lean_inc_n(v_inst_3375_, 3);
v___f_3380_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3380_, 0, v_inst_3375_);
v___f_3381_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3382_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3383_ = lean_apply_2(v_inst_3375_, lean_box(0), v___x_3382_);
lean_inc_ref(v_inst_3370_);
v___f_3384_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3384_, 0, v_inst_3371_);
lean_closure_set(v___f_3384_, 1, v_inst_3372_);
lean_closure_set(v___f_3384_, 2, v_toPure_3379_);
lean_closure_set(v___f_3384_, 3, v_toBind_3378_);
lean_closure_set(v___f_3384_, 4, v_inst_3370_);
lean_closure_set(v___f_3384_, 5, v_inst_3374_);
lean_closure_set(v___f_3384_, 6, v_inst_3373_);
lean_closure_set(v___f_3384_, 7, v_inst_3375_);
lean_closure_set(v___f_3384_, 8, v_f_3376_);
v___f_3385_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3385_, 0, v_toPure_3379_);
lean_closure_set(v___f_3385_, 1, v_toBind_3378_);
lean_closure_set(v___f_3385_, 2, v___f_3380_);
lean_closure_set(v___f_3385_, 3, v_inst_3370_);
lean_closure_set(v___f_3385_, 4, v___f_3384_);
lean_closure_set(v___f_3385_, 5, v_inst_3375_);
lean_closure_set(v___f_3385_, 6, v___f_3381_);
v___x_3386_ = lean_apply_4(v_toBind_3378_, lean_box(0), lean_box(0), v___x_3383_, v___f_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3387_, lean_object* v_inst_3388_, lean_object* v_inst_3389_, lean_object* v_inst_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_f_3394_){
_start:
{
lean_object* v_toApplicative_3395_; lean_object* v_toBind_3396_; lean_object* v_toPure_3397_; lean_object* v___f_3398_; lean_object* v___f_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___f_3402_; lean_object* v___f_3403_; lean_object* v___x_3404_; 
v_toApplicative_3395_ = lean_ctor_get(v_inst_3388_, 0);
v_toBind_3396_ = lean_ctor_get(v_inst_3388_, 1);
lean_inc_n(v_toBind_3396_, 3);
v_toPure_3397_ = lean_ctor_get(v_toApplicative_3395_, 1);
lean_inc_n(v_toPure_3397_, 2);
lean_inc_n(v_inst_3393_, 3);
v___f_3398_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3398_, 0, v_inst_3393_);
v___f_3399_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3400_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3401_ = lean_apply_2(v_inst_3393_, lean_box(0), v___x_3400_);
lean_inc_ref(v_inst_3388_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3402_, 0, v_inst_3389_);
lean_closure_set(v___f_3402_, 1, v_inst_3390_);
lean_closure_set(v___f_3402_, 2, v_toPure_3397_);
lean_closure_set(v___f_3402_, 3, v_toBind_3396_);
lean_closure_set(v___f_3402_, 4, v_inst_3388_);
lean_closure_set(v___f_3402_, 5, v_inst_3392_);
lean_closure_set(v___f_3402_, 6, v_inst_3391_);
lean_closure_set(v___f_3402_, 7, v_inst_3393_);
lean_closure_set(v___f_3402_, 8, v_f_3394_);
v___f_3403_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3403_, 0, v_toPure_3397_);
lean_closure_set(v___f_3403_, 1, v_toBind_3396_);
lean_closure_set(v___f_3403_, 2, v___f_3398_);
lean_closure_set(v___f_3403_, 3, v_inst_3388_);
lean_closure_set(v___f_3403_, 4, v___f_3402_);
lean_closure_set(v___f_3403_, 5, v_inst_3393_);
lean_closure_set(v___f_3403_, 6, v___f_3399_);
v___x_3404_ = lean_apply_4(v_toBind_3396_, lean_box(0), lean_box(0), v___x_3401_, v___f_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3405_, lean_object* v_____r_3406_){
_start:
{
uint8_t v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3407_ = 0;
v___x_3408_ = lean_box(v___x_3407_);
v___x_3409_ = lean_apply_2(v_toPure_3405_, lean_box(0), v___x_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_snd_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; lean_object* v_caches_3424_; lean_object* v_typeAnalysis_3425_; lean_object* v_target_3426_; uint8_t v_didChange_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3437_; 
v___x_3423_ = lean_st_ref_take(v___y_3412_);
v_caches_3424_ = lean_ctor_get(v___x_3423_, 0);
v_typeAnalysis_3425_ = lean_ctor_get(v___x_3423_, 1);
v_target_3426_ = lean_ctor_get(v___x_3423_, 2);
v_didChange_3427_ = lean_ctor_get_uint8(v___x_3423_, sizeof(void*)*4);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3437_ == 0)
{
lean_object* v_unused_3438_; 
v_unused_3438_ = lean_ctor_get(v___x_3423_, 3);
lean_dec(v_unused_3438_);
v___x_3429_ = v___x_3423_;
v_isShared_3430_ = v_isSharedCheck_3437_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_target_3426_);
lean_inc(v_typeAnalysis_3425_);
lean_inc(v_caches_3424_);
lean_dec(v___x_3423_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3437_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3431_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 3, v_snd_3410_);
v___x_3433_ = v___x_3429_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_caches_3424_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_typeAnalysis_3425_);
lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_target_3426_);
lean_ctor_set(v_reuseFailAlloc_3436_, 3, v_snd_3410_);
lean_ctor_set_uint8(v_reuseFailAlloc_3436_, sizeof(void*)*4, v_didChange_3427_);
v___x_3433_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_st_ref_put(v___y_3412_, v___x_3433_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3431_);
return v___x_3435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed(lean_object* v_snd_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(v_snd_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_inst_3453_, lean_object* v_toBind_3454_, lean_object* v___f_3455_, lean_object* v_toPure_3456_, lean_object* v_____s_3457_){
_start:
{
lean_object* v_fst_3458_; 
v_fst_3458_ = lean_ctor_get(v_____s_3457_, 0);
if (lean_obj_tag(v_fst_3458_) == 0)
{
lean_object* v_snd_3459_; lean_object* v___f_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_dec(v_toPure_3456_);
v_snd_3459_ = lean_ctor_get(v_____s_3457_, 1);
lean_inc(v_snd_3459_);
lean_dec_ref(v_____s_3457_);
v___f_3460_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1___boxed), 13, 1);
lean_closure_set(v___f_3460_, 0, v_snd_3459_);
v___x_3461_ = lean_apply_2(v_inst_3453_, lean_box(0), v___f_3460_);
v___x_3462_ = lean_apply_4(v_toBind_3454_, lean_box(0), lean_box(0), v___x_3461_, v___f_3455_);
return v___x_3462_;
}
else
{
lean_object* v_val_3463_; lean_object* v___x_3464_; 
lean_inc_ref(v_fst_3458_);
lean_dec_ref(v_____s_3457_);
lean_dec(v___f_3455_);
lean_dec(v_toBind_3454_);
lean_dec(v_inst_3453_);
v_val_3463_ = lean_ctor_get(v_fst_3458_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v_fst_3458_, 1);
v___x_3464_ = lean_apply_2(v_toPure_3456_, lean_box(0), v_val_3463_);
return v___x_3464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_toPure_3465_, lean_object* v_____do__lift_3466_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_apply_2(v_toPure_3465_, lean_box(0), v_____do__lift_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3468_, lean_object* v_next_3469_, lean_object* v_G_3470_, lean_object* v_____do__lift_3471_){
_start:
{
if (lean_obj_tag(v_____do__lift_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; 
lean_dec(v_G_3470_);
v_a_3472_ = lean_ctor_get(v_____do__lift_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v_____do__lift_3471_, 1);
v___x_3473_ = lean_apply_2(v_toPure_3468_, lean_box(0), v_a_3472_);
return v___x_3473_;
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec(v_toPure_3468_);
v_a_3474_ = lean_ctor_get(v_____do__lift_3471_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v_____do__lift_3471_, 1);
v___x_3475_ = lean_unsigned_to_nat(1u);
v___x_3476_ = lean_nat_add(v_next_3469_, v___x_3475_);
v___x_3477_ = lean_apply_4(v_G_3470_, v___x_3476_, v_a_3474_, lean_box(0), lean_box(0));
return v___x_3477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3478_, lean_object* v_next_3479_, lean_object* v_G_3480_, lean_object* v_____do__lift_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3478_, v_next_3479_, v_G_3480_, v_____do__lift_3481_);
lean_dec(v_next_3479_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(uint8_t v___x_3483_, lean_object* v_snd_3484_, lean_object* v_toPure_3485_, lean_object* v_____r_3486_){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3487_ = lean_box(v___x_3483_);
v___x_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
v___x_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
lean_ctor_set(v___x_3489_, 1, v_snd_3484_);
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
v___x_3491_ = lean_apply_2(v_toPure_3485_, lean_box(0), v___x_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed(lean_object* v___x_3492_, lean_object* v_snd_3493_, lean_object* v_toPure_3494_, lean_object* v_____r_3495_){
_start:
{
uint8_t v___x_1723__boxed_3496_; lean_object* v_res_3497_; 
v___x_1723__boxed_3496_ = lean_unbox(v___x_3492_);
v_res_3497_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v___x_1723__boxed_3496_, v_snd_3493_, v_toPure_3494_, v_____r_3495_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_snd_3498_, lean_object* v_newHyp_3499_, lean_object* v___x_3500_, lean_object* v_toPure_3501_, lean_object* v_____r_3502_){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3503_ = lean_array_push(v_snd_3498_, v_newHyp_3499_);
v___x_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3500_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
v___x_3506_ = lean_apply_2(v_toPure_3501_, lean_box(0), v___x_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_toPure_3507_, lean_object* v___x_3508_, lean_object* v_____do__lift_3509_, lean_object* v_____do__lift_3510_){
_start:
{
uint8_t v_hasTrace_3511_; 
v_hasTrace_3511_ = lean_ctor_get_uint8(v_____do__lift_3510_, sizeof(void*)*1);
if (v_hasTrace_3511_ == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_dec(v___x_3508_);
v___x_3512_ = lean_box(v_hasTrace_3511_);
v___x_3513_ = lean_apply_2(v_toPure_3507_, lean_box(0), v___x_3512_);
return v___x_3513_;
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3514_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27));
v___x_3515_ = l_Lean_Name_append(v___x_3514_, v___x_3508_);
v___x_3516_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3509_, v_____do__lift_3510_, v___x_3515_);
lean_dec(v___x_3515_);
v___x_3517_ = lean_box(v___x_3516_);
v___x_3518_ = lean_apply_2(v_toPure_3507_, lean_box(0), v___x_3517_);
return v___x_3518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed(lean_object* v_toPure_3519_, lean_object* v___x_3520_, lean_object* v_____do__lift_3521_, lean_object* v_____do__lift_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(v_toPure_3519_, v___x_3520_, v_____do__lift_3521_, v_____do__lift_3522_);
lean_dec_ref(v_____do__lift_3522_);
lean_dec_ref(v_____do__lift_3521_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v_inst_3524_, lean_object* v_toPure_3525_, lean_object* v___x_3526_, lean_object* v_toBind_3527_, lean_object* v_____do__lift_3528_){
_start:
{
lean_object* v_getOptionsUnrestricted_3529_; lean_object* v___f_3530_; lean_object* v___x_3531_; 
v_getOptionsUnrestricted_3529_ = lean_ctor_get(v_inst_3524_, 1);
lean_inc(v_getOptionsUnrestricted_3529_);
lean_dec_ref(v_inst_3524_);
v___f_3530_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10___boxed), 4, 3);
lean_closure_set(v___f_3530_, 0, v_toPure_3525_);
lean_closure_set(v___f_3530_, 1, v___x_3526_);
lean_closure_set(v___f_3530_, 2, v_____do__lift_3528_);
v___x_3531_ = lean_apply_4(v_toBind_3527_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3529_, v___f_3530_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(lean_object* v___f_3532_, lean_object* v_type_3533_, lean_object* v_type_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_toMonadRef_3537_, lean_object* v_inst_3538_, lean_object* v___x_3539_, lean_object* v_toBind_3540_, lean_object* v___f_3541_, uint8_t v_____do__lift_3542_){
_start:
{
if (v_____do__lift_3542_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v___f_3541_);
lean_dec(v_toBind_3540_);
lean_dec(v___x_3539_);
lean_dec(v_inst_3538_);
lean_dec_ref(v_toMonadRef_3537_);
lean_dec_ref(v_inst_3536_);
lean_dec_ref(v_inst_3535_);
lean_dec_ref(v_type_3534_);
lean_dec_ref(v_type_3533_);
v___x_3543_ = lean_box(0);
v___x_3544_ = lean_apply_1(v___f_3532_, v___x_3543_);
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec(v___f_3532_);
v___x_3545_ = l_Lean_MessageData_ofExpr(v_type_3533_);
v___x_3546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = l_Lean_MessageData_ofExpr(v_type_3534_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_addTrace___redArg(v_inst_3535_, v_inst_3536_, v_toMonadRef_3537_, v_inst_3538_, v___x_3539_, v___x_3549_);
v___x_3551_ = lean_apply_4(v_toBind_3540_, lean_box(0), lean_box(0), v___x_3550_, v___f_3541_);
return v___x_3551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___f_3552_, lean_object* v_type_3553_, lean_object* v_type_3554_, lean_object* v_inst_3555_, lean_object* v_inst_3556_, lean_object* v_toMonadRef_3557_, lean_object* v_inst_3558_, lean_object* v___x_3559_, lean_object* v_toBind_3560_, lean_object* v___f_3561_, lean_object* v_____do__lift_3562_){
_start:
{
uint8_t v_____do__lift_1797__boxed_3563_; lean_object* v_res_3564_; 
v_____do__lift_1797__boxed_3563_ = lean_unbox(v_____do__lift_3562_);
v_res_3564_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___f_3552_, v_type_3553_, v_type_3554_, v_inst_3555_, v_inst_3556_, v_toMonadRef_3557_, v_inst_3558_, v___x_3559_, v_toBind_3560_, v___f_3561_, v_____do__lift_1797__boxed_3563_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v___x_3565_, lean_object* v_snd_3566_, lean_object* v___x_3567_, lean_object* v_toPure_3568_, lean_object* v_inst_3569_, lean_object* v_inst_3570_, lean_object* v_toBind_3571_, lean_object* v_inst_3572_, lean_object* v_inst_3573_, lean_object* v_toMonadRef_3574_, lean_object* v_inst_3575_, lean_object* v___f_3576_, lean_object* v_newHyp_3577_){
_start:
{
lean_object* v_type_3578_; lean_object* v_value_3579_; uint8_t v___x_3580_; 
v_type_3578_ = lean_ctor_get(v_newHyp_3577_, 1);
v_value_3579_ = lean_ctor_get(v_newHyp_3577_, 2);
lean_inc_ref(v_type_3578_);
v___x_3580_ = l_Lean_Expr_isFalse(v_type_3578_);
if (v___x_3580_ == 0)
{
lean_object* v_type_3581_; lean_object* v___f_3582_; uint8_t v___x_3583_; 
lean_dec(v___f_3576_);
v_type_3581_ = lean_ctor_get(v___x_3565_, 1);
lean_inc_ref(v_type_3581_);
lean_dec_ref(v___x_3565_);
lean_inc(v_toPure_3568_);
lean_inc(v___x_3567_);
lean_inc_ref(v_newHyp_3577_);
lean_inc(v_snd_3566_);
v___f_3582_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3582_, 0, v_snd_3566_);
lean_closure_set(v___f_3582_, 1, v_newHyp_3577_);
lean_closure_set(v___f_3582_, 2, v___x_3567_);
lean_closure_set(v___f_3582_, 3, v_toPure_3568_);
v___x_3583_ = lean_expr_eqv(v_type_3581_, v_type_3578_);
if (v___x_3583_ == 0)
{
lean_object* v_getInheritedTraceOptions_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___x_3588_; lean_object* v___f_3589_; lean_object* v___f_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
lean_inc_ref(v_type_3578_);
lean_dec_ref(v_newHyp_3577_);
lean_dec(v___x_3567_);
lean_dec(v_snd_3566_);
v_getInheritedTraceOptions_3584_ = lean_ctor_get(v_inst_3569_, 2);
lean_inc(v_getInheritedTraceOptions_3584_);
v___f_3585_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3585_, 0, v___f_3582_);
lean_inc_n(v_toBind_3571_, 4);
v___f_3586_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3586_, 0, v_inst_3570_);
lean_closure_set(v___f_3586_, 1, v_toBind_3571_);
lean_closure_set(v___f_3586_, 2, v___f_3585_);
lean_inc_ref(v___f_3586_);
v___f_3587_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3587_, 0, v___f_3586_);
v___x_3588_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3589_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3589_, 0, v_inst_3572_);
lean_closure_set(v___f_3589_, 1, v_toPure_3568_);
lean_closure_set(v___f_3589_, 2, v___x_3588_);
lean_closure_set(v___f_3589_, 3, v_toBind_3571_);
v___f_3590_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3590_, 0, v___f_3586_);
lean_closure_set(v___f_3590_, 1, v_type_3581_);
lean_closure_set(v___f_3590_, 2, v_type_3578_);
lean_closure_set(v___f_3590_, 3, v_inst_3573_);
lean_closure_set(v___f_3590_, 4, v_inst_3569_);
lean_closure_set(v___f_3590_, 5, v_toMonadRef_3574_);
lean_closure_set(v___f_3590_, 6, v_inst_3575_);
lean_closure_set(v___f_3590_, 7, v___x_3588_);
lean_closure_set(v___f_3590_, 8, v_toBind_3571_);
lean_closure_set(v___f_3590_, 9, v___f_3587_);
v___x_3591_ = lean_apply_4(v_toBind_3571_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3584_, v___f_3589_);
v___x_3592_ = lean_apply_4(v_toBind_3571_, lean_box(0), lean_box(0), v___x_3591_, v___f_3590_);
return v___x_3592_;
}
else
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
lean_dec_ref(v___f_3582_);
lean_dec_ref(v_type_3581_);
lean_dec(v_inst_3575_);
lean_dec_ref(v_toMonadRef_3574_);
lean_dec_ref(v_inst_3573_);
lean_dec_ref(v_inst_3572_);
lean_dec(v_toBind_3571_);
lean_dec(v_inst_3570_);
lean_dec_ref(v_inst_3569_);
v___x_3593_ = lean_box(0);
v___x_3594_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3566_, v_newHyp_3577_, v___x_3567_, v_toPure_3568_, v___x_3593_);
return v___x_3594_;
}
}
else
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_inc_ref(v_value_3579_);
lean_dec_ref(v_newHyp_3577_);
lean_dec(v_inst_3575_);
lean_dec_ref(v_toMonadRef_3574_);
lean_dec_ref(v_inst_3573_);
lean_dec_ref(v_inst_3572_);
lean_dec_ref(v_inst_3569_);
lean_dec(v_toPure_3568_);
lean_dec(v___x_3567_);
lean_dec(v_snd_3566_);
lean_dec_ref(v___x_3565_);
v___x_3595_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3595_, 0, v_value_3579_);
v___x_3596_ = lean_apply_2(v_inst_3570_, lean_box(0), v___x_3595_);
v___x_3597_ = lean_apply_4(v_toBind_3571_, lean_box(0), lean_box(0), v___x_3596_, v___f_3576_);
return v___x_3597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3598_, lean_object* v_toPure_3599_, lean_object* v_hyps_3600_, lean_object* v___x_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_, lean_object* v_toBind_3604_, lean_object* v_inst_3605_, lean_object* v_inst_3606_, lean_object* v_toMonadRef_3607_, lean_object* v_inst_3608_, lean_object* v_f_3609_, lean_object* v___f_3610_, lean_object* v_next_3611_, lean_object* v_acc_3612_, lean_object* v_h_3613_, lean_object* v_G_3614_){
_start:
{
uint8_t v___x_3615_; 
v___x_3615_ = lean_nat_dec_lt(v_next_3611_, v___x_3598_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
lean_dec(v_G_3614_);
lean_dec(v_next_3611_);
lean_dec(v___f_3610_);
lean_dec(v_f_3609_);
lean_dec(v_inst_3608_);
lean_dec_ref(v_toMonadRef_3607_);
lean_dec_ref(v_inst_3606_);
lean_dec_ref(v_inst_3605_);
lean_dec(v_toBind_3604_);
lean_dec(v_inst_3603_);
lean_dec_ref(v_inst_3602_);
lean_dec(v___x_3601_);
v___x_3616_ = lean_apply_2(v_toPure_3599_, lean_box(0), v_acc_3612_);
return v___x_3616_;
}
else
{
lean_object* v_snd_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_snd_3617_ = lean_ctor_get(v_acc_3612_, 1);
lean_inc_n(v_snd_3617_, 2);
lean_dec_ref(v_acc_3612_);
lean_inc(v_next_3611_);
lean_inc_n(v_toPure_3599_, 2);
v___f_3618_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3618_, 0, v_toPure_3599_);
lean_closure_set(v___f_3618_, 1, v_next_3611_);
lean_closure_set(v___f_3618_, 2, v_G_3614_);
v___x_3619_ = lean_box(v___x_3615_);
v___f_3620_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3620_, 0, v___x_3619_);
lean_closure_set(v___f_3620_, 1, v_snd_3617_);
lean_closure_set(v___f_3620_, 2, v_toPure_3599_);
v___x_3621_ = lean_array_fget_borrowed(v_hyps_3600_, v_next_3611_);
lean_inc_n(v_toBind_3604_, 3);
lean_inc_n(v___x_3621_, 2);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9), 13, 12);
lean_closure_set(v___f_3622_, 0, v___x_3621_);
lean_closure_set(v___f_3622_, 1, v_snd_3617_);
lean_closure_set(v___f_3622_, 2, v___x_3601_);
lean_closure_set(v___f_3622_, 3, v_toPure_3599_);
lean_closure_set(v___f_3622_, 4, v_inst_3602_);
lean_closure_set(v___f_3622_, 5, v_inst_3603_);
lean_closure_set(v___f_3622_, 6, v_toBind_3604_);
lean_closure_set(v___f_3622_, 7, v_inst_3605_);
lean_closure_set(v___f_3622_, 8, v_inst_3606_);
lean_closure_set(v___f_3622_, 9, v_toMonadRef_3607_);
lean_closure_set(v___f_3622_, 10, v_inst_3608_);
lean_closure_set(v___f_3622_, 11, v___f_3620_);
v___x_3623_ = lean_apply_2(v_f_3609_, v_next_3611_, v___x_3621_);
v___x_3624_ = lean_apply_4(v_toBind_3604_, lean_box(0), lean_box(0), v___x_3623_, v___f_3622_);
v___x_3625_ = lean_apply_4(v_toBind_3604_, lean_box(0), lean_box(0), v___x_3624_, v___f_3610_);
v___x_3626_ = lean_apply_4(v_toBind_3604_, lean_box(0), lean_box(0), v___x_3625_, v___f_3618_);
return v___x_3626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed(lean_object** _args){
lean_object* v___x_3627_ = _args[0];
lean_object* v_toPure_3628_ = _args[1];
lean_object* v_hyps_3629_ = _args[2];
lean_object* v___x_3630_ = _args[3];
lean_object* v_inst_3631_ = _args[4];
lean_object* v_inst_3632_ = _args[5];
lean_object* v_toBind_3633_ = _args[6];
lean_object* v_inst_3634_ = _args[7];
lean_object* v_inst_3635_ = _args[8];
lean_object* v_toMonadRef_3636_ = _args[9];
lean_object* v_inst_3637_ = _args[10];
lean_object* v_f_3638_ = _args[11];
lean_object* v___f_3639_ = _args[12];
lean_object* v_next_3640_ = _args[13];
lean_object* v_acc_3641_ = _args[14];
lean_object* v_h_3642_ = _args[15];
lean_object* v_G_3643_ = _args[16];
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(v___x_3627_, v_toPure_3628_, v_hyps_3629_, v___x_3630_, v_inst_3631_, v_inst_3632_, v_toBind_3633_, v_inst_3634_, v_inst_3635_, v_toMonadRef_3636_, v_inst_3637_, v_f_3638_, v___f_3639_, v_next_3640_, v_acc_3641_, v_h_3642_, v_G_3643_);
lean_dec_ref(v_hyps_3629_);
lean_dec(v___x_3627_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v_toPure_3645_, lean_object* v_inst_3646_, lean_object* v_inst_3647_, lean_object* v_toBind_3648_, lean_object* v_inst_3649_, lean_object* v_inst_3650_, lean_object* v_toMonadRef_3651_, lean_object* v_inst_3652_, lean_object* v_f_3653_, lean_object* v___f_3654_, lean_object* v___f_3655_, lean_object* v_hyps_3656_){
_start:
{
lean_object* v___x_3657_; lean_object* v_newHyps_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___f_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3657_ = lean_array_get_size(v_hyps_3656_);
v_newHyps_3658_ = lean_mk_empty_array_with_capacity(v___x_3657_);
v___x_3659_ = lean_unsigned_to_nat(0u);
v___x_3660_ = lean_box(0);
lean_inc(v_toBind_3648_);
v___f_3661_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11___boxed), 17, 13);
lean_closure_set(v___f_3661_, 0, v___x_3657_);
lean_closure_set(v___f_3661_, 1, v_toPure_3645_);
lean_closure_set(v___f_3661_, 2, v_hyps_3656_);
lean_closure_set(v___f_3661_, 3, v___x_3660_);
lean_closure_set(v___f_3661_, 4, v_inst_3646_);
lean_closure_set(v___f_3661_, 5, v_inst_3647_);
lean_closure_set(v___f_3661_, 6, v_toBind_3648_);
lean_closure_set(v___f_3661_, 7, v_inst_3649_);
lean_closure_set(v___f_3661_, 8, v_inst_3650_);
lean_closure_set(v___f_3661_, 9, v_toMonadRef_3651_);
lean_closure_set(v___f_3661_, 10, v_inst_3652_);
lean_closure_set(v___f_3661_, 11, v_f_3653_);
lean_closure_set(v___f_3661_, 12, v___f_3654_);
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v_newHyps_3658_);
v___x_3663_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3661_, v___x_3659_, v___x_3662_, lean_box(0));
v___x_3664_ = lean_apply_4(v_toBind_3648_, lean_box(0), lean_box(0), v___x_3663_, v___f_3655_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3665_, lean_object* v_inst_3666_, lean_object* v_inst_3667_, lean_object* v_inst_3668_, lean_object* v_inst_3669_, lean_object* v_inst_3670_, lean_object* v_f_3671_){
_start:
{
lean_object* v_toApplicative_3672_; lean_object* v_toBind_3673_; lean_object* v_toPure_3674_; lean_object* v_toMonadRef_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___f_3678_; lean_object* v___f_3679_; lean_object* v___f_3680_; lean_object* v___f_3681_; lean_object* v___x_3682_; 
v_toApplicative_3672_ = lean_ctor_get(v_inst_3665_, 0);
v_toBind_3673_ = lean_ctor_get(v_inst_3665_, 1);
lean_inc_n(v_toBind_3673_, 3);
v_toPure_3674_ = lean_ctor_get(v_toApplicative_3672_, 1);
lean_inc_n(v_toPure_3674_, 4);
v_toMonadRef_3675_ = lean_ctor_get(v_inst_3667_, 1);
lean_inc_ref(v_toMonadRef_3675_);
lean_dec_ref(v_inst_3667_);
v___x_3676_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3666_, 2);
v___x_3677_ = lean_apply_2(v_inst_3666_, lean_box(0), v___x_3676_);
v___f_3678_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3678_, 0, v_toPure_3674_);
v___f_3679_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3679_, 0, v_inst_3666_);
lean_closure_set(v___f_3679_, 1, v_toBind_3673_);
lean_closure_set(v___f_3679_, 2, v___f_3678_);
lean_closure_set(v___f_3679_, 3, v_toPure_3674_);
v___f_3680_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3680_, 0, v_toPure_3674_);
v___f_3681_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3681_, 0, v_toPure_3674_);
lean_closure_set(v___f_3681_, 1, v_inst_3668_);
lean_closure_set(v___f_3681_, 2, v_inst_3666_);
lean_closure_set(v___f_3681_, 3, v_toBind_3673_);
lean_closure_set(v___f_3681_, 4, v_inst_3669_);
lean_closure_set(v___f_3681_, 5, v_inst_3665_);
lean_closure_set(v___f_3681_, 6, v_toMonadRef_3675_);
lean_closure_set(v___f_3681_, 7, v_inst_3670_);
lean_closure_set(v___f_3681_, 8, v_f_3671_);
lean_closure_set(v___f_3681_, 9, v___f_3680_);
lean_closure_set(v___f_3681_, 10, v___f_3679_);
v___x_3682_ = lean_apply_4(v_toBind_3673_, lean_box(0), lean_box(0), v___x_3677_, v___f_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3683_, lean_object* v_inst_3684_, lean_object* v_inst_3685_, lean_object* v_inst_3686_, lean_object* v_inst_3687_, lean_object* v_inst_3688_, lean_object* v_inst_3689_, lean_object* v_inst_3690_, lean_object* v_inst_3691_, lean_object* v_f_3692_){
_start:
{
lean_object* v_toApplicative_3693_; lean_object* v_toBind_3694_; lean_object* v_toPure_3695_; lean_object* v_toMonadRef_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___f_3699_; lean_object* v___f_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___x_3703_; 
v_toApplicative_3693_ = lean_ctor_get(v_inst_3684_, 0);
v_toBind_3694_ = lean_ctor_get(v_inst_3684_, 1);
lean_inc_n(v_toBind_3694_, 3);
v_toPure_3695_ = lean_ctor_get(v_toApplicative_3693_, 1);
lean_inc_n(v_toPure_3695_, 4);
v_toMonadRef_3696_ = lean_ctor_get(v_inst_3686_, 1);
lean_inc_ref(v_toMonadRef_3696_);
lean_dec_ref(v_inst_3686_);
v___x_3697_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3685_, 2);
v___x_3698_ = lean_apply_2(v_inst_3685_, lean_box(0), v___x_3697_);
v___f_3699_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3699_, 0, v_toPure_3695_);
v___f_3700_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3700_, 0, v_inst_3685_);
lean_closure_set(v___f_3700_, 1, v_toBind_3694_);
lean_closure_set(v___f_3700_, 2, v___f_3699_);
lean_closure_set(v___f_3700_, 3, v_toPure_3695_);
v___f_3701_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3701_, 0, v_toPure_3695_);
v___f_3702_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12), 12, 11);
lean_closure_set(v___f_3702_, 0, v_toPure_3695_);
lean_closure_set(v___f_3702_, 1, v_inst_3688_);
lean_closure_set(v___f_3702_, 2, v_inst_3685_);
lean_closure_set(v___f_3702_, 3, v_toBind_3694_);
lean_closure_set(v___f_3702_, 4, v_inst_3689_);
lean_closure_set(v___f_3702_, 5, v_inst_3684_);
lean_closure_set(v___f_3702_, 6, v_toMonadRef_3696_);
lean_closure_set(v___f_3702_, 7, v_inst_3690_);
lean_closure_set(v___f_3702_, 8, v_f_3692_);
lean_closure_set(v___f_3702_, 9, v___f_3701_);
lean_closure_set(v___f_3702_, 10, v___f_3700_);
v___x_3703_ = lean_apply_4(v_toBind_3694_, lean_box(0), lean_box(0), v___x_3698_, v___f_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3704_, lean_object* v_inst_3705_, lean_object* v_inst_3706_, lean_object* v_inst_3707_, lean_object* v_inst_3708_, lean_object* v_inst_3709_, lean_object* v_inst_3710_, lean_object* v_inst_3711_, lean_object* v_inst_3712_, lean_object* v_f_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3704_, v_inst_3705_, v_inst_3706_, v_inst_3707_, v_inst_3708_, v_inst_3709_, v_inst_3710_, v_inst_3711_, v_inst_3712_, v_f_3713_);
lean_dec_ref(v_inst_3712_);
lean_dec_ref(v_inst_3708_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13(lean_object* v___x_3715_, lean_object* v_snd_3716_, lean_object* v___x_3717_, lean_object* v_toPure_3718_, lean_object* v_inst_3719_, lean_object* v_inst_3720_, lean_object* v_toBind_3721_, lean_object* v_inst_3722_, lean_object* v_toMonadRef_3723_, lean_object* v_inst_3724_, lean_object* v_inst_3725_, lean_object* v___f_3726_, lean_object* v_newHyp_3727_){
_start:
{
lean_object* v_type_3728_; lean_object* v_value_3729_; uint8_t v___x_3730_; 
v_type_3728_ = lean_ctor_get(v_newHyp_3727_, 1);
v_value_3729_ = lean_ctor_get(v_newHyp_3727_, 2);
lean_inc_ref(v_type_3728_);
v___x_3730_ = l_Lean_Expr_isFalse(v_type_3728_);
if (v___x_3730_ == 0)
{
lean_object* v_type_3731_; lean_object* v___f_3732_; uint8_t v___x_3733_; 
lean_dec(v___f_3726_);
v_type_3731_ = lean_ctor_get(v___x_3715_, 1);
lean_inc_ref(v_type_3731_);
lean_dec_ref(v___x_3715_);
lean_inc(v_toPure_3718_);
lean_inc(v___x_3717_);
lean_inc_ref(v_newHyp_3727_);
lean_inc(v_snd_3716_);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3732_, 0, v_snd_3716_);
lean_closure_set(v___f_3732_, 1, v_newHyp_3727_);
lean_closure_set(v___f_3732_, 2, v___x_3717_);
lean_closure_set(v___f_3732_, 3, v_toPure_3718_);
v___x_3733_ = lean_expr_eqv(v_type_3731_, v_type_3728_);
if (v___x_3733_ == 0)
{
lean_object* v_getInheritedTraceOptions_3734_; lean_object* v___f_3735_; lean_object* v___f_3736_; lean_object* v___f_3737_; lean_object* v___x_3738_; lean_object* v___f_3739_; lean_object* v___f_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_inc_ref(v_type_3728_);
lean_dec_ref(v_newHyp_3727_);
lean_dec(v___x_3717_);
lean_dec(v_snd_3716_);
v_getInheritedTraceOptions_3734_ = lean_ctor_get(v_inst_3719_, 2);
lean_inc(v_getInheritedTraceOptions_3734_);
v___f_3735_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3735_, 0, v___f_3732_);
lean_inc_n(v_toBind_3721_, 4);
v___f_3736_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3736_, 0, v_inst_3720_);
lean_closure_set(v___f_3736_, 1, v_toBind_3721_);
lean_closure_set(v___f_3736_, 2, v___f_3735_);
lean_inc_ref(v___f_3736_);
v___f_3737_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3737_, 0, v___f_3736_);
v___x_3738_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___f_3739_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_3739_, 0, v___f_3736_);
lean_closure_set(v___f_3739_, 1, v_type_3731_);
lean_closure_set(v___f_3739_, 2, v_type_3728_);
lean_closure_set(v___f_3739_, 3, v_inst_3722_);
lean_closure_set(v___f_3739_, 4, v_inst_3719_);
lean_closure_set(v___f_3739_, 5, v_toMonadRef_3723_);
lean_closure_set(v___f_3739_, 6, v_inst_3724_);
lean_closure_set(v___f_3739_, 7, v___x_3738_);
lean_closure_set(v___f_3739_, 8, v_toBind_3721_);
lean_closure_set(v___f_3739_, 9, v___f_3737_);
v___f_3740_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7), 5, 4);
lean_closure_set(v___f_3740_, 0, v_inst_3725_);
lean_closure_set(v___f_3740_, 1, v_toPure_3718_);
lean_closure_set(v___f_3740_, 2, v___x_3738_);
lean_closure_set(v___f_3740_, 3, v_toBind_3721_);
v___x_3741_ = lean_apply_4(v_toBind_3721_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3734_, v___f_3740_);
v___x_3742_ = lean_apply_4(v_toBind_3721_, lean_box(0), lean_box(0), v___x_3741_, v___f_3739_);
return v___x_3742_;
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec_ref(v___f_3732_);
lean_dec_ref(v_type_3731_);
lean_dec_ref(v_inst_3725_);
lean_dec(v_inst_3724_);
lean_dec_ref(v_toMonadRef_3723_);
lean_dec_ref(v_inst_3722_);
lean_dec(v_toBind_3721_);
lean_dec(v_inst_3720_);
lean_dec_ref(v_inst_3719_);
v___x_3743_ = lean_box(0);
v___x_3744_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(v_snd_3716_, v_newHyp_3727_, v___x_3717_, v_toPure_3718_, v___x_3743_);
return v___x_3744_;
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
lean_inc_ref(v_value_3729_);
lean_dec_ref(v_newHyp_3727_);
lean_dec_ref(v_inst_3725_);
lean_dec(v_inst_3724_);
lean_dec_ref(v_toMonadRef_3723_);
lean_dec_ref(v_inst_3722_);
lean_dec_ref(v_inst_3719_);
lean_dec(v_toPure_3718_);
lean_dec(v___x_3717_);
lean_dec(v_snd_3716_);
lean_dec_ref(v___x_3715_);
v___x_3745_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___boxed), 13, 1);
lean_closure_set(v___x_3745_, 0, v_value_3729_);
v___x_3746_ = lean_apply_2(v_inst_3720_, lean_box(0), v___x_3745_);
v___x_3747_ = lean_apply_4(v_toBind_3721_, lean_box(0), lean_box(0), v___x_3746_, v___f_3726_);
return v___x_3747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3748_, lean_object* v_toPure_3749_, lean_object* v_hyps_3750_, lean_object* v___x_3751_, lean_object* v_inst_3752_, lean_object* v_inst_3753_, lean_object* v_toBind_3754_, lean_object* v_inst_3755_, lean_object* v_toMonadRef_3756_, lean_object* v_inst_3757_, lean_object* v_inst_3758_, lean_object* v_f_3759_, lean_object* v___f_3760_, lean_object* v_next_3761_, lean_object* v_acc_3762_, lean_object* v_h_3763_, lean_object* v_G_3764_){
_start:
{
uint8_t v___x_3765_; 
v___x_3765_ = lean_nat_dec_lt(v_next_3761_, v___x_3748_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; 
lean_dec(v_G_3764_);
lean_dec(v_next_3761_);
lean_dec(v___f_3760_);
lean_dec(v_f_3759_);
lean_dec_ref(v_inst_3758_);
lean_dec(v_inst_3757_);
lean_dec_ref(v_toMonadRef_3756_);
lean_dec_ref(v_inst_3755_);
lean_dec(v_toBind_3754_);
lean_dec(v_inst_3753_);
lean_dec_ref(v_inst_3752_);
lean_dec(v___x_3751_);
v___x_3766_ = lean_apply_2(v_toPure_3749_, lean_box(0), v_acc_3762_);
return v___x_3766_;
}
else
{
lean_object* v_snd_3767_; lean_object* v___f_3768_; lean_object* v___x_3769_; lean_object* v___f_3770_; lean_object* v___x_3771_; lean_object* v___f_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_snd_3767_ = lean_ctor_get(v_acc_3762_, 1);
lean_inc_n(v_snd_3767_, 2);
lean_dec_ref(v_acc_3762_);
lean_inc(v_next_3761_);
lean_inc_n(v_toPure_3749_, 2);
v___f_3768_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3768_, 0, v_toPure_3749_);
lean_closure_set(v___f_3768_, 1, v_next_3761_);
lean_closure_set(v___f_3768_, 2, v_G_3764_);
v___x_3769_ = lean_box(v___x_3765_);
v___f_3770_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_3770_, 0, v___x_3769_);
lean_closure_set(v___f_3770_, 1, v_snd_3767_);
lean_closure_set(v___f_3770_, 2, v_toPure_3749_);
v___x_3771_ = lean_array_fget_borrowed(v_hyps_3750_, v_next_3761_);
lean_dec(v_next_3761_);
lean_inc_n(v_toBind_3754_, 3);
lean_inc_n(v___x_3771_, 2);
v___f_3772_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3772_, 0, v___x_3771_);
lean_closure_set(v___f_3772_, 1, v_snd_3767_);
lean_closure_set(v___f_3772_, 2, v___x_3751_);
lean_closure_set(v___f_3772_, 3, v_toPure_3749_);
lean_closure_set(v___f_3772_, 4, v_inst_3752_);
lean_closure_set(v___f_3772_, 5, v_inst_3753_);
lean_closure_set(v___f_3772_, 6, v_toBind_3754_);
lean_closure_set(v___f_3772_, 7, v_inst_3755_);
lean_closure_set(v___f_3772_, 8, v_toMonadRef_3756_);
lean_closure_set(v___f_3772_, 9, v_inst_3757_);
lean_closure_set(v___f_3772_, 10, v_inst_3758_);
lean_closure_set(v___f_3772_, 11, v___f_3770_);
v___x_3773_ = lean_apply_1(v_f_3759_, v___x_3771_);
v___x_3774_ = lean_apply_4(v_toBind_3754_, lean_box(0), lean_box(0), v___x_3773_, v___f_3772_);
v___x_3775_ = lean_apply_4(v_toBind_3754_, lean_box(0), lean_box(0), v___x_3774_, v___f_3760_);
v___x_3776_ = lean_apply_4(v_toBind_3754_, lean_box(0), lean_box(0), v___x_3775_, v___f_3768_);
return v___x_3776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3777_ = _args[0];
lean_object* v_toPure_3778_ = _args[1];
lean_object* v_hyps_3779_ = _args[2];
lean_object* v___x_3780_ = _args[3];
lean_object* v_inst_3781_ = _args[4];
lean_object* v_inst_3782_ = _args[5];
lean_object* v_toBind_3783_ = _args[6];
lean_object* v_inst_3784_ = _args[7];
lean_object* v_toMonadRef_3785_ = _args[8];
lean_object* v_inst_3786_ = _args[9];
lean_object* v_inst_3787_ = _args[10];
lean_object* v_f_3788_ = _args[11];
lean_object* v___f_3789_ = _args[12];
lean_object* v_next_3790_ = _args[13];
lean_object* v_acc_3791_ = _args[14];
lean_object* v_h_3792_ = _args[15];
lean_object* v_G_3793_ = _args[16];
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3777_, v_toPure_3778_, v_hyps_3779_, v___x_3780_, v_inst_3781_, v_inst_3782_, v_toBind_3783_, v_inst_3784_, v_toMonadRef_3785_, v_inst_3786_, v_inst_3787_, v_f_3788_, v___f_3789_, v_next_3790_, v_acc_3791_, v_h_3792_, v_G_3793_);
lean_dec_ref(v_hyps_3779_);
lean_dec(v___x_3777_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3795_, lean_object* v_inst_3796_, lean_object* v_inst_3797_, lean_object* v_toBind_3798_, lean_object* v_inst_3799_, lean_object* v_toMonadRef_3800_, lean_object* v_inst_3801_, lean_object* v_inst_3802_, lean_object* v_f_3803_, lean_object* v___f_3804_, lean_object* v___f_3805_, lean_object* v_hyps_3806_){
_start:
{
lean_object* v___x_3807_; lean_object* v_newHyps_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___f_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3807_ = lean_array_get_size(v_hyps_3806_);
v_newHyps_3808_ = lean_mk_empty_array_with_capacity(v___x_3807_);
v___x_3809_ = lean_unsigned_to_nat(0u);
v___x_3810_ = lean_box(0);
lean_inc(v_toBind_3798_);
v___f_3811_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 17, 13);
lean_closure_set(v___f_3811_, 0, v___x_3807_);
lean_closure_set(v___f_3811_, 1, v_toPure_3795_);
lean_closure_set(v___f_3811_, 2, v_hyps_3806_);
lean_closure_set(v___f_3811_, 3, v___x_3810_);
lean_closure_set(v___f_3811_, 4, v_inst_3796_);
lean_closure_set(v___f_3811_, 5, v_inst_3797_);
lean_closure_set(v___f_3811_, 6, v_toBind_3798_);
lean_closure_set(v___f_3811_, 7, v_inst_3799_);
lean_closure_set(v___f_3811_, 8, v_toMonadRef_3800_);
lean_closure_set(v___f_3811_, 9, v_inst_3801_);
lean_closure_set(v___f_3811_, 10, v_inst_3802_);
lean_closure_set(v___f_3811_, 11, v_f_3803_);
lean_closure_set(v___f_3811_, 12, v___f_3804_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v_newHyps_3808_);
v___x_3813_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3811_, v___x_3809_, v___x_3812_, lean_box(0));
v___x_3814_ = lean_apply_4(v_toBind_3798_, lean_box(0), lean_box(0), v___x_3813_, v___f_3805_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3815_, lean_object* v_inst_3816_, lean_object* v_inst_3817_, lean_object* v_inst_3818_, lean_object* v_inst_3819_, lean_object* v_inst_3820_, lean_object* v_f_3821_){
_start:
{
lean_object* v_toApplicative_3822_; lean_object* v_toBind_3823_; lean_object* v_toPure_3824_; lean_object* v_toMonadRef_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___f_3828_; lean_object* v___f_3829_; lean_object* v___f_3830_; lean_object* v___f_3831_; lean_object* v___x_3832_; 
v_toApplicative_3822_ = lean_ctor_get(v_inst_3815_, 0);
v_toBind_3823_ = lean_ctor_get(v_inst_3815_, 1);
lean_inc_n(v_toBind_3823_, 3);
v_toPure_3824_ = lean_ctor_get(v_toApplicative_3822_, 1);
lean_inc_n(v_toPure_3824_, 4);
v_toMonadRef_3825_ = lean_ctor_get(v_inst_3817_, 1);
lean_inc_ref(v_toMonadRef_3825_);
lean_dec_ref(v_inst_3817_);
v___x_3826_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3816_, 2);
v___x_3827_ = lean_apply_2(v_inst_3816_, lean_box(0), v___x_3826_);
v___f_3828_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3828_, 0, v_toPure_3824_);
v___f_3829_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3829_, 0, v_inst_3816_);
lean_closure_set(v___f_3829_, 1, v_toBind_3823_);
lean_closure_set(v___f_3829_, 2, v___f_3828_);
lean_closure_set(v___f_3829_, 3, v_toPure_3824_);
v___f_3830_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3830_, 0, v_toPure_3824_);
v___f_3831_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3831_, 0, v_toPure_3824_);
lean_closure_set(v___f_3831_, 1, v_inst_3818_);
lean_closure_set(v___f_3831_, 2, v_inst_3816_);
lean_closure_set(v___f_3831_, 3, v_toBind_3823_);
lean_closure_set(v___f_3831_, 4, v_inst_3815_);
lean_closure_set(v___f_3831_, 5, v_toMonadRef_3825_);
lean_closure_set(v___f_3831_, 6, v_inst_3820_);
lean_closure_set(v___f_3831_, 7, v_inst_3819_);
lean_closure_set(v___f_3831_, 8, v_f_3821_);
lean_closure_set(v___f_3831_, 9, v___f_3830_);
lean_closure_set(v___f_3831_, 10, v___f_3829_);
v___x_3832_ = lean_apply_4(v_toBind_3823_, lean_box(0), lean_box(0), v___x_3827_, v___f_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3833_, lean_object* v_inst_3834_, lean_object* v_inst_3835_, lean_object* v_inst_3836_, lean_object* v_inst_3837_, lean_object* v_inst_3838_, lean_object* v_inst_3839_, lean_object* v_inst_3840_, lean_object* v_inst_3841_, lean_object* v_f_3842_){
_start:
{
lean_object* v_toApplicative_3843_; lean_object* v_toBind_3844_; lean_object* v_toPure_3845_; lean_object* v_toMonadRef_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___f_3849_; lean_object* v___f_3850_; lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___x_3853_; 
v_toApplicative_3843_ = lean_ctor_get(v_inst_3834_, 0);
v_toBind_3844_ = lean_ctor_get(v_inst_3834_, 1);
lean_inc_n(v_toBind_3844_, 3);
v_toPure_3845_ = lean_ctor_get(v_toApplicative_3843_, 1);
lean_inc_n(v_toPure_3845_, 4);
v_toMonadRef_3846_ = lean_ctor_get(v_inst_3836_, 1);
lean_inc_ref(v_toMonadRef_3846_);
lean_dec_ref(v_inst_3836_);
v___x_3847_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3835_, 2);
v___x_3848_ = lean_apply_2(v_inst_3835_, lean_box(0), v___x_3847_);
v___f_3849_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3849_, 0, v_toPure_3845_);
v___f_3850_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3850_, 0, v_inst_3835_);
lean_closure_set(v___f_3850_, 1, v_toBind_3844_);
lean_closure_set(v___f_3850_, 2, v___f_3849_);
lean_closure_set(v___f_3850_, 3, v_toPure_3845_);
v___f_3851_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3851_, 0, v_toPure_3845_);
v___f_3852_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3852_, 0, v_toPure_3845_);
lean_closure_set(v___f_3852_, 1, v_inst_3838_);
lean_closure_set(v___f_3852_, 2, v_inst_3835_);
lean_closure_set(v___f_3852_, 3, v_toBind_3844_);
lean_closure_set(v___f_3852_, 4, v_inst_3834_);
lean_closure_set(v___f_3852_, 5, v_toMonadRef_3846_);
lean_closure_set(v___f_3852_, 6, v_inst_3840_);
lean_closure_set(v___f_3852_, 7, v_inst_3839_);
lean_closure_set(v___f_3852_, 8, v_f_3842_);
lean_closure_set(v___f_3852_, 9, v___f_3851_);
lean_closure_set(v___f_3852_, 10, v___f_3850_);
v___x_3853_ = lean_apply_4(v_toBind_3844_, lean_box(0), lean_box(0), v___x_3848_, v___f_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3854_, lean_object* v_inst_3855_, lean_object* v_inst_3856_, lean_object* v_inst_3857_, lean_object* v_inst_3858_, lean_object* v_inst_3859_, lean_object* v_inst_3860_, lean_object* v_inst_3861_, lean_object* v_inst_3862_, lean_object* v_f_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3854_, v_inst_3855_, v_inst_3856_, v_inst_3857_, v_inst_3858_, v_inst_3859_, v_inst_3860_, v_inst_3861_, v_inst_3862_, v_f_3863_);
lean_dec_ref(v_inst_3862_);
lean_dec_ref(v_inst_3858_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3865_, lean_object* v_x_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_apply_1(v_f_3865_, v___y_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3869_, lean_object* v_inst_3870_, lean_object* v___f_3871_, lean_object* v_hyps_3872_){
_start:
{
lean_object* v_toPure_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v_toPure_3873_ = lean_ctor_get(v_toApplicative_3869_, 1);
lean_inc(v_toPure_3873_);
lean_dec_ref(v_toApplicative_3869_);
v___x_3874_ = lean_unsigned_to_nat(0u);
v___x_3875_ = lean_array_get_size(v_hyps_3872_);
v___x_3876_ = lean_box(0);
v___x_3877_ = lean_nat_dec_lt(v___x_3874_, v___x_3875_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_dec_ref(v_hyps_3872_);
lean_dec(v___f_3871_);
lean_dec_ref(v_inst_3870_);
v___x_3878_ = lean_apply_2(v_toPure_3873_, lean_box(0), v___x_3876_);
return v___x_3878_;
}
else
{
size_t v___x_3879_; size_t v___x_3880_; lean_object* v___x_3881_; 
lean_dec(v_toPure_3873_);
v___x_3879_ = ((size_t)0ULL);
v___x_3880_ = lean_usize_of_nat(v___x_3875_);
v___x_3881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3870_, v___f_3871_, v_hyps_3872_, v___x_3879_, v___x_3880_, v___x_3876_);
return v___x_3881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3882_, lean_object* v_inst_3883_, lean_object* v_f_3884_){
_start:
{
lean_object* v_toApplicative_3885_; lean_object* v_toBind_3886_; lean_object* v___f_3887_; lean_object* v___f_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_toApplicative_3885_ = lean_ctor_get(v_inst_3882_, 0);
lean_inc_ref(v_toApplicative_3885_);
v_toBind_3886_ = lean_ctor_get(v_inst_3882_, 1);
lean_inc(v_toBind_3886_);
v___f_3887_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3887_, 0, v_f_3884_);
v___f_3888_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3888_, 0, v_toApplicative_3885_);
lean_closure_set(v___f_3888_, 1, v_inst_3882_);
lean_closure_set(v___f_3888_, 2, v___f_3887_);
v___x_3889_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3890_ = lean_apply_2(v_inst_3883_, lean_box(0), v___x_3889_);
v___x_3891_ = lean_apply_4(v_toBind_3886_, lean_box(0), lean_box(0), v___x_3890_, v___f_3888_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3892_, lean_object* v_inst_3893_, lean_object* v_inst_3894_, lean_object* v_inst_3895_, lean_object* v_f_3896_){
_start:
{
lean_object* v_toApplicative_3897_; lean_object* v_toBind_3898_; lean_object* v___f_3899_; lean_object* v___f_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v_toApplicative_3897_ = lean_ctor_get(v_inst_3893_, 0);
lean_inc_ref(v_toApplicative_3897_);
v_toBind_3898_ = lean_ctor_get(v_inst_3893_, 1);
lean_inc(v_toBind_3898_);
v___f_3899_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3899_, 0, v_f_3896_);
v___f_3900_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3900_, 0, v_toApplicative_3897_);
lean_closure_set(v___f_3900_, 1, v_inst_3893_);
lean_closure_set(v___f_3900_, 2, v___f_3899_);
v___x_3901_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3902_ = lean_apply_2(v_inst_3894_, lean_box(0), v___x_3901_);
v___x_3903_ = lean_apply_4(v_toBind_3898_, lean_box(0), lean_box(0), v___x_3902_, v___f_3900_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3904_, lean_object* v_inst_3905_, lean_object* v_inst_3906_, lean_object* v_inst_3907_, lean_object* v_f_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3904_, v_inst_3905_, v_inst_3906_, v_inst_3907_, v_f_3908_);
lean_dec_ref(v_inst_3907_);
return v_res_3909_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__0);
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t v_cacheId_3912_, lean_object* v_methods_3913_, lean_object* v_config_3914_, lean_object* v_hyp_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v___x_3924_; lean_object* v_caches_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v_typeAnalysis_3932_; lean_object* v_target_3933_; lean_object* v_hypotheses_3934_; uint8_t v_didChange_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3976_; 
v___x_3924_ = lean_st_ref_get(v_a_3916_);
v_caches_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc_ref(v_caches_3925_);
lean_dec(v___x_3924_);
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_get(v_cacheId_3912_, v_caches_3925_);
v___x_3928_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_3929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3926_);
lean_ctor_set(v___x_3929_, 1, v___x_3927_);
lean_ctor_set(v___x_3929_, 2, v___x_3928_);
lean_ctor_set(v___x_3929_, 3, v___x_3928_);
v___x_3930_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3912_, v___x_3928_, v_caches_3925_);
v___x_3931_ = lean_st_ref_take(v_a_3916_);
v_typeAnalysis_3932_ = lean_ctor_get(v___x_3931_, 1);
v_target_3933_ = lean_ctor_get(v___x_3931_, 2);
v_hypotheses_3934_ = lean_ctor_get(v___x_3931_, 3);
v_didChange_3935_ = lean_ctor_get_uint8(v___x_3931_, sizeof(void*)*4);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3976_ == 0)
{
lean_object* v_unused_3977_; 
v_unused_3977_ = lean_ctor_get(v___x_3931_, 0);
lean_dec(v_unused_3977_);
v___x_3937_ = v___x_3931_;
v_isShared_3938_ = v_isSharedCheck_3976_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_hypotheses_3934_);
lean_inc(v_target_3933_);
lean_inc(v_typeAnalysis_3932_);
lean_dec(v___x_3931_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3976_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_3930_);
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_typeAnalysis_3932_);
lean_ctor_set(v_reuseFailAlloc_3975_, 2, v_target_3933_);
lean_ctor_set(v_reuseFailAlloc_3975_, 3, v_hypotheses_3934_);
lean_ctor_set_uint8(v_reuseFailAlloc_3975_, sizeof(void*)*4, v_didChange_3935_);
v___x_3940_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; lean_object* v_type_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3941_ = lean_st_ref_put(v_a_3916_, v___x_3940_);
v_type_3942_ = lean_ctor_get(v_hyp_3915_, 1);
lean_inc_ref(v_type_3942_);
v___x_3943_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3943_, 0, v_type_3942_);
v___x_3944_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3943_, v_methods_3913_, v_config_3914_, v___x_3929_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v_fst_3946_; lean_object* v_snd_3947_; lean_object* v___x_3948_; lean_object* v_caches_3949_; lean_object* v_persistentCache_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v_typeAnalysis_3953_; lean_object* v_target_3954_; lean_object* v_hypotheses_3955_; uint8_t v_didChange_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3965_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref_known(v___x_3944_, 1);
v_fst_3946_ = lean_ctor_get(v_a_3945_, 0);
lean_inc(v_fst_3946_);
v_snd_3947_ = lean_ctor_get(v_a_3945_, 1);
lean_inc(v_snd_3947_);
lean_dec(v_a_3945_);
v___x_3948_ = lean_st_ref_get(v_a_3916_);
v_caches_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc_ref(v_caches_3949_);
lean_dec(v___x_3948_);
v_persistentCache_3950_ = lean_ctor_get(v_snd_3947_, 1);
lean_inc_ref(v_persistentCache_3950_);
lean_dec(v_snd_3947_);
v___x_3951_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SimpCacheId_set(v_cacheId_3912_, v_persistentCache_3950_, v_caches_3949_);
v___x_3952_ = lean_st_ref_take(v_a_3916_);
v_typeAnalysis_3953_ = lean_ctor_get(v___x_3952_, 1);
v_target_3954_ = lean_ctor_get(v___x_3952_, 2);
v_hypotheses_3955_ = lean_ctor_get(v___x_3952_, 3);
v_didChange_3956_ = lean_ctor_get_uint8(v___x_3952_, sizeof(void*)*4);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3965_ == 0)
{
lean_object* v_unused_3966_; 
v_unused_3966_ = lean_ctor_get(v___x_3952_, 0);
lean_dec(v_unused_3966_);
v___x_3958_ = v___x_3952_;
v_isShared_3959_ = v_isSharedCheck_3965_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_hypotheses_3955_);
lean_inc(v_target_3954_);
lean_inc(v_typeAnalysis_3953_);
lean_dec(v___x_3952_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3965_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3951_);
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_typeAnalysis_3953_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_target_3954_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_hypotheses_3955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3964_, sizeof(void*)*4, v_didChange_3956_);
v___x_3961_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_st_ref_put(v_a_3916_, v___x_3961_);
v___x_3963_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_3915_, v_fst_3946_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_);
return v___x_3963_;
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec_ref(v_hyp_3915_);
v_a_3967_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3944_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3944_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___boxed(lean_object* v_cacheId_3978_, lean_object* v_methods_3979_, lean_object* v_config_3980_, lean_object* v_hyp_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
uint8_t v_cacheId_boxed_3990_; lean_object* v_res_3991_; 
v_cacheId_boxed_3990_ = lean_unbox(v_cacheId_3978_);
v_res_3991_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_boxed_3990_, v_methods_3979_, v_config_3980_, v_hyp_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(uint8_t v_cacheId_3992_, lean_object* v_methods_3993_, lean_object* v_config_3994_, lean_object* v_hyp_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_3992_, v_methods_3993_, v_config_3994_, v_hyp_3995_, v_a_3997_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___boxed(lean_object* v_cacheId_4009_, lean_object* v_methods_4010_, lean_object* v_config_4011_, lean_object* v_hyp_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
uint8_t v_cacheId_boxed_4025_; lean_object* v_res_4026_; 
v_cacheId_boxed_4025_ = lean_unbox(v_cacheId_4009_);
v_res_4026_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp(v_cacheId_boxed_4025_, v_methods_4010_, v_config_4011_, v_hyp_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t v_cacheId_4027_, lean_object* v_methods_4028_, lean_object* v_config_4029_, lean_object* v_hyp_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v___x_4039_; lean_object* v_caches_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v_typeAnalysis_4047_; lean_object* v_target_4048_; lean_object* v_hypotheses_4049_; uint8_t v_didChange_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4091_; 
v___x_4039_ = lean_st_ref_get(v_a_4031_);
v_caches_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc_ref(v_caches_4040_);
lean_dec(v___x_4039_);
v___x_4041_ = lean_unsigned_to_nat(0u);
v___x_4042_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_get(v_cacheId_4027_, v_caches_4040_);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4041_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_4045_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4027_, v___x_4044_, v_caches_4040_);
v___x_4046_ = lean_st_ref_take(v_a_4031_);
v_typeAnalysis_4047_ = lean_ctor_get(v___x_4046_, 1);
v_target_4048_ = lean_ctor_get(v___x_4046_, 2);
v_hypotheses_4049_ = lean_ctor_get(v___x_4046_, 3);
v_didChange_4050_ = lean_ctor_get_uint8(v___x_4046_, sizeof(void*)*4);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; 
v_unused_4092_ = lean_ctor_get(v___x_4046_, 0);
lean_dec(v_unused_4092_);
v___x_4052_ = v___x_4046_;
v_isShared_4053_ = v_isSharedCheck_4091_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_hypotheses_4049_);
lean_inc(v_target_4048_);
lean_inc(v_typeAnalysis_4047_);
lean_dec(v___x_4046_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4091_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4045_);
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4045_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_typeAnalysis_4047_);
lean_ctor_set(v_reuseFailAlloc_4090_, 2, v_target_4048_);
lean_ctor_set(v_reuseFailAlloc_4090_, 3, v_hypotheses_4049_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*4, v_didChange_4050_);
v___x_4055_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; lean_object* v_type_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4056_ = lean_st_ref_put(v_a_4031_, v___x_4055_);
v_type_4057_ = lean_ctor_get(v_hyp_4030_, 1);
lean_inc_ref(v_type_4057_);
v___x_4058_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4058_, 0, v_type_4057_);
v___x_4059_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4058_, v_methods_4028_, v_config_4029_, v___x_4043_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v_fst_4061_; lean_object* v_snd_4062_; lean_object* v___x_4063_; lean_object* v_caches_4064_; lean_object* v_cache_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v_typeAnalysis_4068_; lean_object* v_target_4069_; lean_object* v_hypotheses_4070_; uint8_t v_didChange_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4080_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___x_4059_, 1);
v_fst_4061_ = lean_ctor_get(v_a_4060_, 0);
lean_inc(v_fst_4061_);
v_snd_4062_ = lean_ctor_get(v_a_4060_, 1);
lean_inc(v_snd_4062_);
lean_dec(v_a_4060_);
v___x_4063_ = lean_st_ref_get(v_a_4031_);
v_caches_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc_ref(v_caches_4064_);
lean_dec(v___x_4063_);
v_cache_4065_ = lean_ctor_get(v_snd_4062_, 1);
lean_inc_ref(v_cache_4065_);
lean_dec(v_snd_4062_);
v___x_4066_ = l_Lean_Meta_Tactic_BVDecide_Normalize_DSimpCacheId_set(v_cacheId_4027_, v_cache_4065_, v_caches_4064_);
v___x_4067_ = lean_st_ref_take(v_a_4031_);
v_typeAnalysis_4068_ = lean_ctor_get(v___x_4067_, 1);
v_target_4069_ = lean_ctor_get(v___x_4067_, 2);
v_hypotheses_4070_ = lean_ctor_get(v___x_4067_, 3);
v_didChange_4071_ = lean_ctor_get_uint8(v___x_4067_, sizeof(void*)*4);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; 
v_unused_4081_ = lean_ctor_get(v___x_4067_, 0);
lean_dec(v_unused_4081_);
v___x_4073_ = v___x_4067_;
v_isShared_4074_ = v_isSharedCheck_4080_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_hypotheses_4070_);
lean_inc(v_target_4069_);
lean_inc(v_typeAnalysis_4068_);
lean_dec(v___x_4067_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4080_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 0, v___x_4066_);
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_typeAnalysis_4068_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_target_4069_);
lean_ctor_set(v_reuseFailAlloc_4079_, 3, v_hypotheses_4070_);
lean_ctor_set_uint8(v_reuseFailAlloc_4079_, sizeof(void*)*4, v_didChange_4071_);
v___x_4076_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_st_ref_put(v_a_4031_, v___x_4076_);
v___x_4078_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_4030_, v_fst_4061_);
lean_dec(v_fst_4061_);
return v___x_4078_;
}
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec_ref(v_hyp_4030_);
v_a_4082_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4059_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4059_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg___boxed(lean_object* v_cacheId_4093_, lean_object* v_methods_4094_, lean_object* v_config_4095_, lean_object* v_hyp_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
uint8_t v_cacheId_boxed_4105_; lean_object* v_res_4106_; 
v_cacheId_boxed_4105_ = lean_unbox(v_cacheId_4093_);
v_res_4106_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_boxed_4105_, v_methods_4094_, v_config_4095_, v_hyp_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
lean_dec(v_a_4097_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(uint8_t v_cacheId_4107_, lean_object* v_methods_4108_, lean_object* v_config_4109_, lean_object* v_hyp_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4107_, v_methods_4108_, v_config_4109_, v_hyp_4110_, v_a_4112_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___boxed(lean_object* v_cacheId_4124_, lean_object* v_methods_4125_, lean_object* v_config_4126_, lean_object* v_hyp_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
uint8_t v_cacheId_boxed_4140_; lean_object* v_res_4141_; 
v_cacheId_boxed_4140_ = lean_unbox(v_cacheId_4124_);
v_res_4141_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp(v_cacheId_boxed_4140_, v_methods_4125_, v_config_4126_, v_hyp_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
lean_dec(v_a_4130_);
lean_dec(v_a_4129_);
lean_dec_ref(v_a_4128_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(lean_object* v_snd_4142_, lean_object* v_a_4143_, lean_object* v___x_4144_, lean_object* v_____r_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4158_ = lean_array_push(v_snd_4142_, v_a_4143_);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4144_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed(lean_object* v_snd_4162_, lean_object* v_a_4163_, lean_object* v___x_4164_, lean_object* v_____r_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4162_, v_a_4163_, v___x_4164_, v_____r_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(uint8_t v___x_4179_, lean_object* v___f_4180_, lean_object* v_____r_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; lean_object* v_caches_4195_; lean_object* v_typeAnalysis_4196_; lean_object* v_target_4197_; lean_object* v_hypotheses_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4208_; 
v___x_4194_ = lean_st_ref_take(v___y_4183_);
v_caches_4195_ = lean_ctor_get(v___x_4194_, 0);
v_typeAnalysis_4196_ = lean_ctor_get(v___x_4194_, 1);
v_target_4197_ = lean_ctor_get(v___x_4194_, 2);
v_hypotheses_4198_ = lean_ctor_get(v___x_4194_, 3);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4200_ = v___x_4194_;
v_isShared_4201_ = v_isSharedCheck_4208_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_hypotheses_4198_);
lean_inc(v_target_4197_);
lean_inc(v_typeAnalysis_4196_);
lean_inc(v_caches_4195_);
lean_dec(v___x_4194_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4208_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v___x_4204_; 
v___x_4202_ = lean_box(0);
if (v_isShared_4201_ == 0)
{
v___x_4204_ = v___x_4200_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_caches_4195_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v_typeAnalysis_4196_);
lean_ctor_set(v_reuseFailAlloc_4207_, 2, v_target_4197_);
lean_ctor_set(v_reuseFailAlloc_4207_, 3, v_hypotheses_4198_);
v___x_4204_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_ctor_set_uint8(v___x_4204_, sizeof(void*)*4, v___x_4179_);
v___x_4205_ = lean_st_ref_put(v___y_4183_, v___x_4204_);
lean_inc(v___y_4192_);
lean_inc_ref(v___y_4191_);
lean_inc(v___y_4190_);
lean_inc_ref(v___y_4189_);
lean_inc(v___y_4188_);
lean_inc_ref(v___y_4187_);
lean_inc(v___y_4186_);
lean_inc_ref(v___y_4185_);
lean_inc(v___y_4184_);
lean_inc(v___y_4183_);
lean_inc_ref(v___y_4182_);
v___x_4206_ = lean_apply_13(v___f_4180_, v___x_4202_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, lean_box(0));
return v___x_4206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1___boxed(lean_object* v___x_4209_, lean_object* v___f_4210_, lean_object* v_____r_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
uint8_t v___x_22115__boxed_4224_; lean_object* v_res_4225_; 
v___x_22115__boxed_4224_ = lean_unbox(v___x_4209_);
v_res_4225_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_22115__boxed_4224_, v___f_4210_, v_____r_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(lean_object* v___x_4226_, lean_object* v_hypotheses_4227_, uint8_t v_cacheId_4228_, lean_object* v_methods_4229_, lean_object* v_config_4230_, lean_object* v___x_4231_, lean_object* v___x_4232_, lean_object* v___x_4233_, lean_object* v_toMonadRef_4234_, lean_object* v___f_4235_, lean_object* v_next_4236_, lean_object* v_acc_4237_, lean_object* v_h_4238_, lean_object* v_G_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___y_4253_; uint8_t v___x_4275_; 
v___x_4275_ = lean_nat_dec_lt(v_next_4236_, v___x_4226_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; 
lean_dec_ref(v_G_4239_);
lean_dec(v___f_4235_);
lean_dec_ref(v_toMonadRef_4234_);
lean_dec_ref(v___x_4233_);
lean_dec_ref(v___x_4232_);
lean_dec(v___x_4231_);
lean_dec_ref(v_config_4230_);
lean_dec_ref(v_methods_4229_);
v___x_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4276_, 0, v_acc_4237_);
return v___x_4276_;
}
else
{
lean_object* v_snd_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4349_; 
v_snd_4277_ = lean_ctor_get(v_acc_4237_, 1);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_acc_4237_);
if (v_isSharedCheck_4349_ == 0)
{
lean_object* v_unused_4350_; 
v_unused_4350_ = lean_ctor_get(v_acc_4237_, 0);
lean_dec(v_unused_4350_);
v___x_4279_ = v_acc_4237_;
v_isShared_4280_ = v_isSharedCheck_4349_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_snd_4277_);
lean_dec(v_acc_4237_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4349_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_array_fget_borrowed(v_hypotheses_4227_, v_next_4236_);
lean_inc(v___x_4281_);
v___x_4282_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v_cacheId_4228_, v_methods_4229_, v_config_4230_, v___x_4281_, v___y_4241_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v_type_4284_; lean_object* v_value_4285_; uint8_t v___x_4286_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v_type_4284_ = lean_ctor_get(v_a_4283_, 1);
v_value_4285_ = lean_ctor_get(v_a_4283_, 2);
lean_inc_ref(v_type_4284_);
v___x_4286_ = l_Lean_Expr_isFalse(v_type_4284_);
if (v___x_4286_ == 0)
{
lean_object* v_type_4287_; lean_object* v___f_4288_; uint8_t v___x_4289_; 
lean_del_object(v___x_4279_);
v_type_4287_ = lean_ctor_get(v___x_4281_, 1);
lean_inc(v___x_4231_);
lean_inc(v_a_4283_);
lean_inc(v_snd_4277_);
v___f_4288_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4288_, 0, v_snd_4277_);
lean_closure_set(v___f_4288_, 1, v_a_4283_);
lean_closure_set(v___f_4288_, 2, v___x_4231_);
v___x_4289_ = lean_expr_eqv(v_type_4287_, v_type_4284_);
if (v___x_4289_ == 0)
{
lean_object* v_toCold_4290_; lean_object* v_options_4291_; lean_object* v_inheritedTraceOptions_4292_; uint8_t v_hasTrace_4293_; 
lean_inc_ref(v_type_4284_);
lean_dec(v_a_4283_);
lean_dec(v_snd_4277_);
lean_dec(v___x_4231_);
v_toCold_4290_ = lean_ctor_get(v___y_4249_, 0);
v_options_4291_ = lean_ctor_get(v_toCold_4290_, 2);
v_inheritedTraceOptions_4292_ = lean_ctor_get(v_toCold_4290_, 11);
v_hasTrace_4293_ = lean_ctor_get_uint8(v_options_4291_, sizeof(void*)*1);
if (v_hasTrace_4293_ == 0)
{
lean_dec_ref(v_type_4284_);
lean_dec(v___f_4235_);
lean_dec_ref(v_toMonadRef_4234_);
lean_dec_ref(v___x_4233_);
lean_dec_ref(v___x_4232_);
goto v___jp_4294_;
}
else
{
lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4298_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4299_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4292_, v_options_4291_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_dec_ref(v_type_4284_);
lean_dec(v___f_4235_);
lean_dec_ref(v_toMonadRef_4234_);
lean_dec_ref(v___x_4233_);
lean_dec_ref(v___x_4232_);
goto v___jp_4294_;
}
else
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_22041__overap_4305_; lean_object* v___x_4306_; 
lean_inc_ref(v_type_4287_);
v___x_4300_ = l_Lean_MessageData_ofExpr(v_type_4287_);
v___x_4301_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = l_Lean_MessageData_ofExpr(v_type_4284_);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_22041__overap_4305_ = l_Lean_addTrace___redArg(v___x_4232_, v___x_4233_, v_toMonadRef_4234_, v___f_4235_, v___x_4297_, v___x_4304_);
lean_inc(v___y_4250_);
lean_inc_ref(v___y_4249_);
lean_inc(v___y_4248_);
lean_inc_ref(v___y_4247_);
lean_inc(v___y_4246_);
lean_inc_ref(v___y_4245_);
lean_inc(v___y_4244_);
lean_inc_ref(v___y_4243_);
lean_inc(v___y_4242_);
lean_inc(v___y_4241_);
lean_inc_ref(v___y_4240_);
v___x_4306_ = lean_apply_12(v___x_22041__overap_4305_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, lean_box(0));
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4308_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4275_, v___f_4288_, v_a_4307_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
v___y_4253_ = v___x_4308_;
goto v___jp_4252_;
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref(v___f_4288_);
lean_dec_ref(v_G_4239_);
v_a_4309_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4306_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4306_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
v___jp_4294_:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_box(0);
v___x_4296_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4275_, v___f_4288_, v___x_4295_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
v___y_4253_ = v___x_4296_;
goto v___jp_4252_;
}
}
else
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
lean_dec_ref(v___f_4288_);
lean_dec(v___f_4235_);
lean_dec_ref(v_toMonadRef_4234_);
lean_dec_ref(v___x_4233_);
lean_dec_ref(v___x_4232_);
v___x_4317_ = lean_box(0);
v___x_4318_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4277_, v_a_4283_, v___x_4231_, v___x_4317_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
v___y_4253_ = v___x_4318_;
goto v___jp_4252_;
}
}
else
{
lean_object* v___x_4319_; 
lean_inc_ref(v_value_4285_);
lean_dec(v_a_4283_);
lean_dec_ref(v_G_4239_);
lean_dec(v___f_4235_);
lean_dec_ref(v_toMonadRef_4234_);
lean_dec_ref(v___x_4233_);
lean_dec_ref(v___x_4232_);
lean_dec(v___x_4231_);
v___x_4319_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4285_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4331_; 
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4331_ == 0)
{
lean_object* v_unused_4332_; 
v_unused_4332_ = lean_ctor_get(v___x_4319_, 0);
lean_dec(v_unused_4332_);
v___x_4321_ = v___x_4319_;
v_isShared_4322_ = v_isSharedCheck_4331_;
goto v_resetjp_4320_;
}
else
{
lean_dec(v___x_4319_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4331_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4326_; 
v___x_4323_ = lean_box(v___x_4275_);
v___x_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 0, v___x_4324_);
v___x_4326_ = v___x_4279_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4324_);
lean_ctor_set(v_reuseFailAlloc_4330_, 1, v_snd_4277_);
v___x_4326_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
lean_object* v___x_4328_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 0, v___x_4326_);
v___x_4328_ = v___x_4321_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4326_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_del_object(v___x_4279_);
lean_dec(v_snd_4277_);
v_a_4333_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4319_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4319_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_del_object(v___x_4279_);
lean_dec(v_snd_4277_);
lean_dec_ref(v_G_4239_);
lean_dec(v___f_4235_);
lean_dec_ref(v_toMonadRef_4234_);
lean_dec_ref(v___x_4233_);
lean_dec_ref(v___x_4232_);
lean_dec(v___x_4231_);
v_a_4341_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4282_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4282_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
}
v___jp_4252_:
{
if (lean_obj_tag(v___y_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4266_; 
v_a_4254_ = lean_ctor_get(v___y_4253_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___y_4253_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4256_ = v___y_4253_;
v_isShared_4257_ = v_isSharedCheck_4266_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___y_4253_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4266_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
if (lean_obj_tag(v_a_4254_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; 
lean_dec_ref(v_G_4239_);
v_a_4258_ = lean_ctor_get(v_a_4254_, 0);
lean_inc(v_a_4258_);
lean_dec_ref_known(v_a_4254_, 1);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v_a_4258_);
v___x_4260_ = v___x_4256_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4258_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_del_object(v___x_4256_);
v_a_4262_ = lean_ctor_get(v_a_4254_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v_a_4254_, 1);
v___x_4263_ = lean_unsigned_to_nat(1u);
v___x_4264_ = lean_nat_add(v_next_4236_, v___x_4263_);
lean_inc(v___y_4250_);
lean_inc_ref(v___y_4249_);
lean_inc(v___y_4248_);
lean_inc_ref(v___y_4247_);
lean_inc(v___y_4246_);
lean_inc_ref(v___y_4245_);
lean_inc(v___y_4244_);
lean_inc_ref(v___y_4243_);
lean_inc(v___y_4242_);
lean_inc(v___y_4241_);
lean_inc_ref(v___y_4240_);
v___x_4265_ = lean_apply_16(v_G_4239_, v___x_4264_, v_a_4262_, lean_box(0), lean_box(0), v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, lean_box(0));
return v___x_4265_;
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec_ref(v_G_4239_);
v_a_4267_ = lean_ctor_get(v___y_4253_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___y_4253_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___y_4253_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___y_4253_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4351_ = _args[0];
lean_object* v_hypotheses_4352_ = _args[1];
lean_object* v_cacheId_4353_ = _args[2];
lean_object* v_methods_4354_ = _args[3];
lean_object* v_config_4355_ = _args[4];
lean_object* v___x_4356_ = _args[5];
lean_object* v___x_4357_ = _args[6];
lean_object* v___x_4358_ = _args[7];
lean_object* v_toMonadRef_4359_ = _args[8];
lean_object* v___f_4360_ = _args[9];
lean_object* v_next_4361_ = _args[10];
lean_object* v_acc_4362_ = _args[11];
lean_object* v_h_4363_ = _args[12];
lean_object* v_G_4364_ = _args[13];
lean_object* v___y_4365_ = _args[14];
lean_object* v___y_4366_ = _args[15];
lean_object* v___y_4367_ = _args[16];
lean_object* v___y_4368_ = _args[17];
lean_object* v___y_4369_ = _args[18];
lean_object* v___y_4370_ = _args[19];
lean_object* v___y_4371_ = _args[20];
lean_object* v___y_4372_ = _args[21];
lean_object* v___y_4373_ = _args[22];
lean_object* v___y_4374_ = _args[23];
lean_object* v___y_4375_ = _args[24];
lean_object* v___y_4376_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4377_; lean_object* v_res_4378_; 
v_cacheId_boxed_4377_ = lean_unbox(v_cacheId_4353_);
v_res_4378_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2(v___x_4351_, v_hypotheses_4352_, v_cacheId_boxed_4377_, v_methods_4354_, v_config_4355_, v___x_4356_, v___x_4357_, v___x_4358_, v_toMonadRef_4359_, v___f_4360_, v_next_4361_, v_acc_4362_, v_h_4363_, v_G_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v_next_4361_);
lean_dec_ref(v_hypotheses_4352_);
lean_dec(v___x_4351_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(uint8_t v_cacheId_4379_, lean_object* v_methods_4380_, lean_object* v_config_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v___x_4394_; lean_object* v_toApplicative_4395_; lean_object* v_toFunctor_4396_; lean_object* v_toSeq_4397_; lean_object* v_toSeqLeft_4398_; lean_object* v_toSeqRight_4399_; lean_object* v___f_4400_; lean_object* v___f_4401_; lean_object* v___f_4402_; lean_object* v___f_4403_; lean_object* v___x_4404_; lean_object* v___f_4405_; lean_object* v___f_4406_; lean_object* v___f_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v_toApplicative_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4498_; 
v___x_4394_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4395_ = lean_ctor_get(v___x_4394_, 0);
v_toFunctor_4396_ = lean_ctor_get(v_toApplicative_4395_, 0);
v_toSeq_4397_ = lean_ctor_get(v_toApplicative_4395_, 2);
v_toSeqLeft_4398_ = lean_ctor_get(v_toApplicative_4395_, 3);
v_toSeqRight_4399_ = lean_ctor_get(v_toApplicative_4395_, 4);
v___f_4400_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4401_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4396_, 2);
v___f_4402_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4402_, 0, v_toFunctor_4396_);
v___f_4403_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4403_, 0, v_toFunctor_4396_);
v___x_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___f_4402_);
lean_ctor_set(v___x_4404_, 1, v___f_4403_);
lean_inc(v_toSeqRight_4399_);
v___f_4405_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4405_, 0, v_toSeqRight_4399_);
lean_inc(v_toSeqLeft_4398_);
v___f_4406_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4406_, 0, v_toSeqLeft_4398_);
lean_inc(v_toSeq_4397_);
v___f_4407_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4407_, 0, v_toSeq_4397_);
v___x_4408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4404_);
lean_ctor_set(v___x_4408_, 1, v___f_4400_);
lean_ctor_set(v___x_4408_, 2, v___f_4407_);
lean_ctor_set(v___x_4408_, 3, v___f_4406_);
lean_ctor_set(v___x_4408_, 4, v___f_4405_);
v___x_4409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
lean_ctor_set(v___x_4409_, 1, v___f_4401_);
v___x_4410_ = l_StateRefT_x27_instMonad___redArg(v___x_4409_);
v_toApplicative_4411_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v___x_4410_, 1);
lean_dec(v_unused_4499_);
v___x_4413_ = v___x_4410_;
v_isShared_4414_ = v_isSharedCheck_4498_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_toApplicative_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4498_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v_toFunctor_4415_; lean_object* v_toSeq_4416_; lean_object* v_toSeqLeft_4417_; lean_object* v_toSeqRight_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4496_; 
v_toFunctor_4415_ = lean_ctor_get(v_toApplicative_4411_, 0);
v_toSeq_4416_ = lean_ctor_get(v_toApplicative_4411_, 2);
v_toSeqLeft_4417_ = lean_ctor_get(v_toApplicative_4411_, 3);
v_toSeqRight_4418_ = lean_ctor_get(v_toApplicative_4411_, 4);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_toApplicative_4411_);
if (v_isSharedCheck_4496_ == 0)
{
lean_object* v_unused_4497_; 
v_unused_4497_ = lean_ctor_get(v_toApplicative_4411_, 1);
lean_dec(v_unused_4497_);
v___x_4420_ = v_toApplicative_4411_;
v_isShared_4421_ = v_isSharedCheck_4496_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_toSeqRight_4418_);
lean_inc(v_toSeqLeft_4417_);
lean_inc(v_toSeq_4416_);
lean_inc(v_toFunctor_4415_);
lean_dec(v_toApplicative_4411_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4496_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___f_4422_; lean_object* v___f_4423_; lean_object* v___f_4424_; lean_object* v___f_4425_; lean_object* v___x_4426_; lean_object* v___f_4427_; lean_object* v___f_4428_; lean_object* v___f_4429_; lean_object* v___x_4431_; 
v___f_4422_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4423_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4415_);
v___f_4424_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4424_, 0, v_toFunctor_4415_);
v___f_4425_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4425_, 0, v_toFunctor_4415_);
v___x_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4426_, 0, v___f_4424_);
lean_ctor_set(v___x_4426_, 1, v___f_4425_);
v___f_4427_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4427_, 0, v_toSeqRight_4418_);
v___f_4428_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4428_, 0, v_toSeqLeft_4417_);
v___f_4429_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4429_, 0, v_toSeq_4416_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 4, v___f_4427_);
lean_ctor_set(v___x_4420_, 3, v___f_4428_);
lean_ctor_set(v___x_4420_, 2, v___f_4429_);
lean_ctor_set(v___x_4420_, 1, v___f_4422_);
lean_ctor_set(v___x_4420_, 0, v___x_4426_);
v___x_4431_ = v___x_4420_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4426_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v___f_4422_);
lean_ctor_set(v_reuseFailAlloc_4495_, 2, v___f_4429_);
lean_ctor_set(v_reuseFailAlloc_4495_, 3, v___f_4428_);
lean_ctor_set(v_reuseFailAlloc_4495_, 4, v___f_4427_);
v___x_4431_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4433_; 
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 1, v___f_4423_);
lean_ctor_set(v___x_4413_, 0, v___x_4431_);
v___x_4433_ = v___x_4413_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v___f_4423_);
v___x_4433_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v_toMonadRef_4442_; lean_object* v___f_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v_hypotheses_4446_; lean_object* v___x_4447_; lean_object* v_newHyps_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___f_4452_; lean_object* v___x_4453_; lean_object* v___x_21939__overap_4454_; lean_object* v___x_4455_; 
v___x_4434_ = l_StateRefT_x27_instMonad___redArg(v___x_4433_);
v___x_4435_ = l_ReaderT_instMonad___redArg(v___x_4434_);
v___x_4436_ = l_StateRefT_x27_instMonad___redArg(v___x_4435_);
v___x_4437_ = l_ReaderT_instMonad___redArg(v___x_4436_);
v___x_4438_ = l_ReaderT_instMonad___redArg(v___x_4437_);
v___x_4439_ = l_StateRefT_x27_instMonad___redArg(v___x_4438_);
v___x_4440_ = l_ReaderT_instMonad___redArg(v___x_4439_);
v___x_4441_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4442_ = lean_ctor_get(v___x_4441_, 0);
v___f_4443_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4444_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4445_ = lean_st_ref_get(v_a_4383_);
v_hypotheses_4446_ = lean_ctor_get(v___x_4445_, 3);
lean_inc_ref(v_hypotheses_4446_);
lean_dec(v___x_4445_);
v___x_4447_ = lean_array_get_size(v_hypotheses_4446_);
v_newHyps_4448_ = lean_mk_empty_array_with_capacity(v___x_4447_);
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = lean_box(0);
v___x_4451_ = lean_box(v_cacheId_4379_);
lean_inc_ref(v_toMonadRef_4442_);
v___f_4452_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4452_, 0, v___x_4447_);
lean_closure_set(v___f_4452_, 1, v_hypotheses_4446_);
lean_closure_set(v___f_4452_, 2, v___x_4451_);
lean_closure_set(v___f_4452_, 3, v_methods_4380_);
lean_closure_set(v___f_4452_, 4, v_config_4381_);
lean_closure_set(v___f_4452_, 5, v___x_4450_);
lean_closure_set(v___f_4452_, 6, v___x_4440_);
lean_closure_set(v___f_4452_, 7, v___x_4444_);
lean_closure_set(v___f_4452_, 8, v_toMonadRef_4442_);
lean_closure_set(v___f_4452_, 9, v___f_4443_);
v___x_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4450_);
lean_ctor_set(v___x_4453_, 1, v_newHyps_4448_);
v___x_21939__overap_4454_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4452_, v___x_4449_, v___x_4453_, lean_box(0));
lean_inc(v_a_4392_);
lean_inc_ref(v_a_4391_);
lean_inc(v_a_4390_);
lean_inc_ref(v_a_4389_);
lean_inc(v_a_4388_);
lean_inc_ref(v_a_4387_);
lean_inc(v_a_4386_);
lean_inc_ref(v_a_4385_);
lean_inc(v_a_4384_);
lean_inc(v_a_4383_);
lean_inc_ref(v_a_4382_);
v___x_4455_ = lean_apply_12(v___x_21939__overap_4454_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, lean_box(0));
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4485_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4458_ = v___x_4455_;
v_isShared_4459_ = v_isSharedCheck_4485_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4455_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4485_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v_fst_4460_; 
v_fst_4460_ = lean_ctor_get(v_a_4456_, 0);
if (lean_obj_tag(v_fst_4460_) == 0)
{
lean_object* v_snd_4461_; lean_object* v___x_4462_; lean_object* v_caches_4463_; lean_object* v_typeAnalysis_4464_; lean_object* v_target_4465_; uint8_t v_didChange_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4479_; 
v_snd_4461_ = lean_ctor_get(v_a_4456_, 1);
lean_inc(v_snd_4461_);
lean_dec(v_a_4456_);
v___x_4462_ = lean_st_ref_take(v_a_4383_);
v_caches_4463_ = lean_ctor_get(v___x_4462_, 0);
v_typeAnalysis_4464_ = lean_ctor_get(v___x_4462_, 1);
v_target_4465_ = lean_ctor_get(v___x_4462_, 2);
v_didChange_4466_ = lean_ctor_get_uint8(v___x_4462_, sizeof(void*)*4);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4479_ == 0)
{
lean_object* v_unused_4480_; 
v_unused_4480_ = lean_ctor_get(v___x_4462_, 3);
lean_dec(v_unused_4480_);
v___x_4468_ = v___x_4462_;
v_isShared_4469_ = v_isSharedCheck_4479_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_target_4465_);
lean_inc(v_typeAnalysis_4464_);
lean_inc(v_caches_4463_);
lean_dec(v___x_4462_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4479_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 3, v_snd_4461_);
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_caches_4463_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v_typeAnalysis_4464_);
lean_ctor_set(v_reuseFailAlloc_4478_, 2, v_target_4465_);
lean_ctor_set(v_reuseFailAlloc_4478_, 3, v_snd_4461_);
lean_ctor_set_uint8(v_reuseFailAlloc_4478_, sizeof(void*)*4, v_didChange_4466_);
v___x_4471_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4472_; uint8_t v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4472_ = lean_st_ref_put(v_a_4383_, v___x_4471_);
v___x_4473_ = 0;
v___x_4474_ = lean_box(v___x_4473_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4474_);
v___x_4476_ = v___x_4458_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
else
{
lean_object* v_val_4481_; lean_object* v___x_4483_; 
lean_inc_ref(v_fst_4460_);
lean_dec(v_a_4456_);
v_val_4481_ = lean_ctor_get(v_fst_4460_, 0);
lean_inc(v_val_4481_);
lean_dec_ref_known(v_fst_4460_, 1);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v_val_4481_);
v___x_4483_ = v___x_4458_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_val_4481_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
v_a_4486_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4455_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4455_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___boxed(lean_object* v_cacheId_4500_, lean_object* v_methods_4501_, lean_object* v_config_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
uint8_t v_cacheId_boxed_4515_; lean_object* v_res_4516_; 
v_cacheId_boxed_4515_ = lean_unbox(v_cacheId_4500_);
v_res_4516_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps(v_cacheId_boxed_4515_, v_methods_4501_, v_config_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(lean_object* v___x_4517_, lean_object* v_hypotheses_4518_, uint8_t v_cacheId_4519_, lean_object* v_methods_4520_, lean_object* v_config_4521_, lean_object* v___x_4522_, lean_object* v___x_4523_, lean_object* v___x_4524_, lean_object* v_toMonadRef_4525_, lean_object* v___f_4526_, lean_object* v_next_4527_, lean_object* v_acc_4528_, lean_object* v_h_4529_, lean_object* v_G_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v___y_4544_; uint8_t v___x_4566_; 
v___x_4566_ = lean_nat_dec_lt(v_next_4527_, v___x_4517_);
if (v___x_4566_ == 0)
{
lean_object* v___x_4567_; 
lean_dec_ref(v_G_4530_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec(v___x_4522_);
lean_dec_ref(v_config_4521_);
lean_dec_ref(v_methods_4520_);
v___x_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4567_, 0, v_acc_4528_);
return v___x_4567_;
}
else
{
lean_object* v_snd_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4640_; 
v_snd_4568_ = lean_ctor_get(v_acc_4528_, 1);
v_isSharedCheck_4640_ = !lean_is_exclusive(v_acc_4528_);
if (v_isSharedCheck_4640_ == 0)
{
lean_object* v_unused_4641_; 
v_unused_4641_ = lean_ctor_get(v_acc_4528_, 0);
lean_dec(v_unused_4641_);
v___x_4570_ = v_acc_4528_;
v_isShared_4571_ = v_isSharedCheck_4640_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_snd_4568_);
lean_dec(v_acc_4528_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4640_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = lean_array_fget_borrowed(v_hypotheses_4518_, v_next_4527_);
lean_inc(v___x_4572_);
v___x_4573_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v_cacheId_4519_, v_methods_4520_, v_config_4521_, v___x_4572_, v___y_4532_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v_type_4575_; lean_object* v_value_4576_; uint8_t v___x_4577_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_a_4574_);
lean_dec_ref_known(v___x_4573_, 1);
v_type_4575_ = lean_ctor_get(v_a_4574_, 1);
v_value_4576_ = lean_ctor_get(v_a_4574_, 2);
lean_inc_ref(v_type_4575_);
v___x_4577_ = l_Lean_Expr_isFalse(v_type_4575_);
if (v___x_4577_ == 0)
{
lean_object* v_type_4578_; lean_object* v___f_4579_; uint8_t v___x_4580_; 
lean_del_object(v___x_4570_);
v_type_4578_ = lean_ctor_get(v___x_4572_, 1);
lean_inc(v___x_4522_);
lean_inc(v_a_4574_);
lean_inc(v_snd_4568_);
v___f_4579_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4579_, 0, v_snd_4568_);
lean_closure_set(v___f_4579_, 1, v_a_4574_);
lean_closure_set(v___f_4579_, 2, v___x_4522_);
v___x_4580_ = lean_expr_eqv(v_type_4578_, v_type_4575_);
if (v___x_4580_ == 0)
{
lean_object* v_toCold_4581_; lean_object* v_options_4582_; lean_object* v_inheritedTraceOptions_4583_; uint8_t v_hasTrace_4584_; 
lean_inc_ref(v_type_4575_);
lean_dec(v_a_4574_);
lean_dec(v_snd_4568_);
lean_dec(v___x_4522_);
v_toCold_4581_ = lean_ctor_get(v___y_4540_, 0);
v_options_4582_ = lean_ctor_get(v_toCold_4581_, 2);
v_inheritedTraceOptions_4583_ = lean_ctor_get(v_toCold_4581_, 11);
v_hasTrace_4584_ = lean_ctor_get_uint8(v_options_4582_, sizeof(void*)*1);
if (v_hasTrace_4584_ == 0)
{
lean_dec_ref(v_type_4575_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
goto v___jp_4585_;
}
else
{
lean_object* v___x_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
v___x_4588_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_4589_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_4590_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4583_, v_options_4582_, v___x_4589_);
if (v___x_4590_ == 0)
{
lean_dec_ref(v_type_4575_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
goto v___jp_4585_;
}
else
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_22041__overap_4596_; lean_object* v___x_4597_; 
lean_inc_ref(v_type_4578_);
v___x_4591_ = l_Lean_MessageData_ofExpr(v_type_4578_);
v___x_4592_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = l_Lean_MessageData_ofExpr(v_type_4575_);
v___x_4595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4593_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
v___x_22041__overap_4596_ = l_Lean_addTrace___redArg(v___x_4523_, v___x_4524_, v_toMonadRef_4525_, v___f_4526_, v___x_4588_, v___x_4595_);
lean_inc(v___y_4541_);
lean_inc_ref(v___y_4540_);
lean_inc(v___y_4539_);
lean_inc_ref(v___y_4538_);
lean_inc(v___y_4537_);
lean_inc_ref(v___y_4536_);
lean_inc(v___y_4535_);
lean_inc_ref(v___y_4534_);
lean_inc(v___y_4533_);
lean_inc(v___y_4532_);
lean_inc_ref(v___y_4531_);
v___x_4597_ = lean_apply_12(v___x_22041__overap_4596_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, lean_box(0));
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4599_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref_known(v___x_4597_, 1);
v___x_4599_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4566_, v___f_4579_, v_a_4598_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
v___y_4544_ = v___x_4599_;
goto v___jp_4543_;
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec_ref(v___f_4579_);
lean_dec_ref(v_G_4530_);
v_a_4600_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4597_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4597_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
}
v___jp_4585_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4586_ = lean_box(0);
v___x_4587_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__1(v___x_4566_, v___f_4579_, v___x_4586_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
v___y_4544_ = v___x_4587_;
goto v___jp_4543_;
}
}
else
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
lean_dec_ref(v___f_4579_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
v___x_4608_ = lean_box(0);
v___x_4609_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyps___lam__0(v_snd_4568_, v_a_4574_, v___x_4522_, v___x_4608_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
v___y_4544_ = v___x_4609_;
goto v___jp_4543_;
}
}
else
{
lean_object* v___x_4610_; 
lean_inc_ref(v_value_4576_);
lean_dec(v_a_4574_);
lean_dec_ref(v_G_4530_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec(v___x_4522_);
v___x_4610_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4576_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4622_; 
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4622_ == 0)
{
lean_object* v_unused_4623_; 
v_unused_4623_ = lean_ctor_get(v___x_4610_, 0);
lean_dec(v_unused_4623_);
v___x_4612_ = v___x_4610_;
v_isShared_4613_ = v_isSharedCheck_4622_;
goto v_resetjp_4611_;
}
else
{
lean_dec(v___x_4610_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4622_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4617_; 
v___x_4614_ = lean_box(v___x_4566_);
v___x_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 0, v___x_4615_);
v___x_4617_ = v___x_4570_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_snd_4568_);
v___x_4617_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
lean_object* v___x_4619_; 
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4617_);
v___x_4619_ = v___x_4612_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_del_object(v___x_4570_);
lean_dec(v_snd_4568_);
v_a_4624_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4610_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4610_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
lean_del_object(v___x_4570_);
lean_dec(v_snd_4568_);
lean_dec_ref(v_G_4530_);
lean_dec(v___f_4526_);
lean_dec_ref(v_toMonadRef_4525_);
lean_dec_ref(v___x_4524_);
lean_dec_ref(v___x_4523_);
lean_dec(v___x_4522_);
v_a_4632_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4573_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4573_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
v___jp_4543_:
{
if (lean_obj_tag(v___y_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4557_; 
v_a_4545_ = lean_ctor_get(v___y_4544_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___y_4544_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4547_ = v___y_4544_;
v_isShared_4548_ = v_isSharedCheck_4557_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___y_4544_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4557_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
if (lean_obj_tag(v_a_4545_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; 
lean_dec_ref(v_G_4530_);
v_a_4549_ = lean_ctor_get(v_a_4545_, 0);
lean_inc(v_a_4549_);
lean_dec_ref_known(v_a_4545_, 1);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 0, v_a_4549_);
v___x_4551_ = v___x_4547_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
lean_del_object(v___x_4547_);
v_a_4553_ = lean_ctor_get(v_a_4545_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v_a_4545_, 1);
v___x_4554_ = lean_unsigned_to_nat(1u);
v___x_4555_ = lean_nat_add(v_next_4527_, v___x_4554_);
lean_inc(v___y_4541_);
lean_inc_ref(v___y_4540_);
lean_inc(v___y_4539_);
lean_inc_ref(v___y_4538_);
lean_inc(v___y_4537_);
lean_inc_ref(v___y_4536_);
lean_inc(v___y_4535_);
lean_inc_ref(v___y_4534_);
lean_inc(v___y_4533_);
lean_inc(v___y_4532_);
lean_inc_ref(v___y_4531_);
v___x_4556_ = lean_apply_16(v_G_4530_, v___x_4555_, v_a_4553_, lean_box(0), lean_box(0), v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, lean_box(0));
return v___x_4556_;
}
}
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
lean_dec_ref(v_G_4530_);
v_a_4558_ = lean_ctor_get(v___y_4544_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___y_4544_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___y_4544_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___y_4544_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed(lean_object** _args){
lean_object* v___x_4642_ = _args[0];
lean_object* v_hypotheses_4643_ = _args[1];
lean_object* v_cacheId_4644_ = _args[2];
lean_object* v_methods_4645_ = _args[3];
lean_object* v_config_4646_ = _args[4];
lean_object* v___x_4647_ = _args[5];
lean_object* v___x_4648_ = _args[6];
lean_object* v___x_4649_ = _args[7];
lean_object* v_toMonadRef_4650_ = _args[8];
lean_object* v___f_4651_ = _args[9];
lean_object* v_next_4652_ = _args[10];
lean_object* v_acc_4653_ = _args[11];
lean_object* v_h_4654_ = _args[12];
lean_object* v_G_4655_ = _args[13];
lean_object* v___y_4656_ = _args[14];
lean_object* v___y_4657_ = _args[15];
lean_object* v___y_4658_ = _args[16];
lean_object* v___y_4659_ = _args[17];
lean_object* v___y_4660_ = _args[18];
lean_object* v___y_4661_ = _args[19];
lean_object* v___y_4662_ = _args[20];
lean_object* v___y_4663_ = _args[21];
lean_object* v___y_4664_ = _args[22];
lean_object* v___y_4665_ = _args[23];
lean_object* v___y_4666_ = _args[24];
lean_object* v___y_4667_ = _args[25];
_start:
{
uint8_t v_cacheId_boxed_4668_; lean_object* v_res_4669_; 
v_cacheId_boxed_4668_ = lean_unbox(v_cacheId_4644_);
v_res_4669_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2(v___x_4642_, v_hypotheses_4643_, v_cacheId_boxed_4668_, v_methods_4645_, v_config_4646_, v___x_4647_, v___x_4648_, v___x_4649_, v_toMonadRef_4650_, v___f_4651_, v_next_4652_, v_acc_4653_, v_h_4654_, v_G_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec(v_next_4652_);
lean_dec_ref(v_hypotheses_4643_);
lean_dec(v___x_4642_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(uint8_t v_cacheId_4670_, lean_object* v_methods_4671_, lean_object* v_config_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v___x_4685_; lean_object* v_toApplicative_4686_; lean_object* v_toFunctor_4687_; lean_object* v_toSeq_4688_; lean_object* v_toSeqLeft_4689_; lean_object* v_toSeqRight_4690_; lean_object* v___f_4691_; lean_object* v___f_4692_; lean_object* v___f_4693_; lean_object* v___f_4694_; lean_object* v___x_4695_; lean_object* v___f_4696_; lean_object* v___f_4697_; lean_object* v___f_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v_toApplicative_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4789_; 
v___x_4685_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_4686_ = lean_ctor_get(v___x_4685_, 0);
v_toFunctor_4687_ = lean_ctor_get(v_toApplicative_4686_, 0);
v_toSeq_4688_ = lean_ctor_get(v_toApplicative_4686_, 2);
v_toSeqLeft_4689_ = lean_ctor_get(v_toApplicative_4686_, 3);
v_toSeqRight_4690_ = lean_ctor_get(v_toApplicative_4686_, 4);
v___f_4691_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_4692_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_4687_, 2);
v___f_4693_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4693_, 0, v_toFunctor_4687_);
v___f_4694_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4694_, 0, v_toFunctor_4687_);
v___x_4695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4695_, 0, v___f_4693_);
lean_ctor_set(v___x_4695_, 1, v___f_4694_);
lean_inc(v_toSeqRight_4690_);
v___f_4696_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4696_, 0, v_toSeqRight_4690_);
lean_inc(v_toSeqLeft_4689_);
v___f_4697_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4697_, 0, v_toSeqLeft_4689_);
lean_inc(v_toSeq_4688_);
v___f_4698_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4698_, 0, v_toSeq_4688_);
v___x_4699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4695_);
lean_ctor_set(v___x_4699_, 1, v___f_4691_);
lean_ctor_set(v___x_4699_, 2, v___f_4698_);
lean_ctor_set(v___x_4699_, 3, v___f_4697_);
lean_ctor_set(v___x_4699_, 4, v___f_4696_);
v___x_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4699_);
lean_ctor_set(v___x_4700_, 1, v___f_4692_);
v___x_4701_ = l_StateRefT_x27_instMonad___redArg(v___x_4700_);
v_toApplicative_4702_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4789_ == 0)
{
lean_object* v_unused_4790_; 
v_unused_4790_ = lean_ctor_get(v___x_4701_, 1);
lean_dec(v_unused_4790_);
v___x_4704_ = v___x_4701_;
v_isShared_4705_ = v_isSharedCheck_4789_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_toApplicative_4702_);
lean_dec(v___x_4701_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4789_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v_toFunctor_4706_; lean_object* v_toSeq_4707_; lean_object* v_toSeqLeft_4708_; lean_object* v_toSeqRight_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4787_; 
v_toFunctor_4706_ = lean_ctor_get(v_toApplicative_4702_, 0);
v_toSeq_4707_ = lean_ctor_get(v_toApplicative_4702_, 2);
v_toSeqLeft_4708_ = lean_ctor_get(v_toApplicative_4702_, 3);
v_toSeqRight_4709_ = lean_ctor_get(v_toApplicative_4702_, 4);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_toApplicative_4702_);
if (v_isSharedCheck_4787_ == 0)
{
lean_object* v_unused_4788_; 
v_unused_4788_ = lean_ctor_get(v_toApplicative_4702_, 1);
lean_dec(v_unused_4788_);
v___x_4711_ = v_toApplicative_4702_;
v_isShared_4712_ = v_isSharedCheck_4787_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_toSeqRight_4709_);
lean_inc(v_toSeqLeft_4708_);
lean_inc(v_toSeq_4707_);
lean_inc(v_toFunctor_4706_);
lean_dec(v_toApplicative_4702_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4787_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___f_4713_; lean_object* v___f_4714_; lean_object* v___f_4715_; lean_object* v___f_4716_; lean_object* v___x_4717_; lean_object* v___f_4718_; lean_object* v___f_4719_; lean_object* v___f_4720_; lean_object* v___x_4722_; 
v___f_4713_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_4714_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_4706_);
v___f_4715_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4715_, 0, v_toFunctor_4706_);
v___f_4716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4716_, 0, v_toFunctor_4706_);
v___x_4717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___f_4715_);
lean_ctor_set(v___x_4717_, 1, v___f_4716_);
v___f_4718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4718_, 0, v_toSeqRight_4709_);
v___f_4719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4719_, 0, v_toSeqLeft_4708_);
v___f_4720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4720_, 0, v_toSeq_4707_);
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 4, v___f_4718_);
lean_ctor_set(v___x_4711_, 3, v___f_4719_);
lean_ctor_set(v___x_4711_, 2, v___f_4720_);
lean_ctor_set(v___x_4711_, 1, v___f_4713_);
lean_ctor_set(v___x_4711_, 0, v___x_4717_);
v___x_4722_ = v___x_4711_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v___f_4713_);
lean_ctor_set(v_reuseFailAlloc_4786_, 2, v___f_4720_);
lean_ctor_set(v_reuseFailAlloc_4786_, 3, v___f_4719_);
lean_ctor_set(v_reuseFailAlloc_4786_, 4, v___f_4718_);
v___x_4722_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
lean_object* v___x_4724_; 
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 1, v___f_4714_);
lean_ctor_set(v___x_4704_, 0, v___x_4722_);
v___x_4724_ = v___x_4704_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v___f_4714_);
v___x_4724_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v_toMonadRef_4733_; lean_object* v___f_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v_hypotheses_4737_; lean_object* v___x_4738_; lean_object* v_newHyps_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___f_4743_; lean_object* v___x_4744_; lean_object* v___x_21939__overap_4745_; lean_object* v___x_4746_; 
v___x_4725_ = l_StateRefT_x27_instMonad___redArg(v___x_4724_);
v___x_4726_ = l_ReaderT_instMonad___redArg(v___x_4725_);
v___x_4727_ = l_StateRefT_x27_instMonad___redArg(v___x_4726_);
v___x_4728_ = l_ReaderT_instMonad___redArg(v___x_4727_);
v___x_4729_ = l_ReaderT_instMonad___redArg(v___x_4728_);
v___x_4730_ = l_StateRefT_x27_instMonad___redArg(v___x_4729_);
v___x_4731_ = l_ReaderT_instMonad___redArg(v___x_4730_);
v___x_4732_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_4733_ = lean_ctor_get(v___x_4732_, 0);
v___f_4734_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___x_4735_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_4736_ = lean_st_ref_get(v_a_4674_);
v_hypotheses_4737_ = lean_ctor_get(v___x_4736_, 3);
lean_inc_ref(v_hypotheses_4737_);
lean_dec(v___x_4736_);
v___x_4738_ = lean_array_get_size(v_hypotheses_4737_);
v_newHyps_4739_ = lean_mk_empty_array_with_capacity(v___x_4738_);
v___x_4740_ = lean_unsigned_to_nat(0u);
v___x_4741_ = lean_box(0);
v___x_4742_ = lean_box(v_cacheId_4670_);
lean_inc_ref(v_toMonadRef_4733_);
v___f_4743_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___lam__2___boxed), 26, 10);
lean_closure_set(v___f_4743_, 0, v___x_4738_);
lean_closure_set(v___f_4743_, 1, v_hypotheses_4737_);
lean_closure_set(v___f_4743_, 2, v___x_4742_);
lean_closure_set(v___f_4743_, 3, v_methods_4671_);
lean_closure_set(v___f_4743_, 4, v_config_4672_);
lean_closure_set(v___f_4743_, 5, v___x_4741_);
lean_closure_set(v___f_4743_, 6, v___x_4731_);
lean_closure_set(v___f_4743_, 7, v___x_4735_);
lean_closure_set(v___f_4743_, 8, v_toMonadRef_4733_);
lean_closure_set(v___f_4743_, 9, v___f_4734_);
v___x_4744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4741_);
lean_ctor_set(v___x_4744_, 1, v_newHyps_4739_);
v___x_21939__overap_4745_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_4743_, v___x_4740_, v___x_4744_, lean_box(0));
lean_inc(v_a_4683_);
lean_inc_ref(v_a_4682_);
lean_inc(v_a_4681_);
lean_inc_ref(v_a_4680_);
lean_inc(v_a_4679_);
lean_inc_ref(v_a_4678_);
lean_inc(v_a_4677_);
lean_inc_ref(v_a_4676_);
lean_inc(v_a_4675_);
lean_inc(v_a_4674_);
lean_inc_ref(v_a_4673_);
v___x_4746_ = lean_apply_12(v___x_21939__overap_4745_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, lean_box(0));
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4776_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4749_ = v___x_4746_;
v_isShared_4750_ = v_isSharedCheck_4776_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4746_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4776_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v_fst_4751_; 
v_fst_4751_ = lean_ctor_get(v_a_4747_, 0);
if (lean_obj_tag(v_fst_4751_) == 0)
{
lean_object* v_snd_4752_; lean_object* v___x_4753_; lean_object* v_caches_4754_; lean_object* v_typeAnalysis_4755_; lean_object* v_target_4756_; uint8_t v_didChange_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4770_; 
v_snd_4752_ = lean_ctor_get(v_a_4747_, 1);
lean_inc(v_snd_4752_);
lean_dec(v_a_4747_);
v___x_4753_ = lean_st_ref_take(v_a_4674_);
v_caches_4754_ = lean_ctor_get(v___x_4753_, 0);
v_typeAnalysis_4755_ = lean_ctor_get(v___x_4753_, 1);
v_target_4756_ = lean_ctor_get(v___x_4753_, 2);
v_didChange_4757_ = lean_ctor_get_uint8(v___x_4753_, sizeof(void*)*4);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4770_ == 0)
{
lean_object* v_unused_4771_; 
v_unused_4771_ = lean_ctor_get(v___x_4753_, 3);
lean_dec(v_unused_4771_);
v___x_4759_ = v___x_4753_;
v_isShared_4760_ = v_isSharedCheck_4770_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_target_4756_);
lean_inc(v_typeAnalysis_4755_);
lean_inc(v_caches_4754_);
lean_dec(v___x_4753_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4770_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 3, v_snd_4752_);
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_caches_4754_);
lean_ctor_set(v_reuseFailAlloc_4769_, 1, v_typeAnalysis_4755_);
lean_ctor_set(v_reuseFailAlloc_4769_, 2, v_target_4756_);
lean_ctor_set(v_reuseFailAlloc_4769_, 3, v_snd_4752_);
lean_ctor_set_uint8(v_reuseFailAlloc_4769_, sizeof(void*)*4, v_didChange_4757_);
v___x_4762_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4763_; uint8_t v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4767_; 
v___x_4763_ = lean_st_ref_put(v_a_4674_, v___x_4762_);
v___x_4764_ = 0;
v___x_4765_ = lean_box(v___x_4764_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 0, v___x_4765_);
v___x_4767_ = v___x_4749_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4765_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
else
{
lean_object* v_val_4772_; lean_object* v___x_4774_; 
lean_inc_ref(v_fst_4751_);
lean_dec(v_a_4747_);
v_val_4772_ = lean_ctor_get(v_fst_4751_, 0);
lean_inc(v_val_4772_);
lean_dec_ref_known(v_fst_4751_, 1);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 0, v_val_4772_);
v___x_4774_ = v___x_4749_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_val_4772_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
else
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4784_; 
v_a_4777_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4779_ = v___x_4746_;
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4746_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4782_; 
if (v_isShared_4780_ == 0)
{
v___x_4782_ = v___x_4779_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps___boxed(lean_object* v_cacheId_4791_, lean_object* v_methods_4792_, lean_object* v_config_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
uint8_t v_cacheId_boxed_4806_; lean_object* v_res_4807_; 
v_cacheId_boxed_4806_ = lean_unbox(v_cacheId_4791_);
v_res_4807_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyps(v_cacheId_boxed_4806_, v_methods_4792_, v_config_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec(v_a_4795_);
lean_dec_ref(v_a_4794_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
lean_object* v___x_4814_; lean_object* v_env_4815_; uint8_t v___x_4816_; lean_object* v_env_4817_; lean_object* v___x_4818_; lean_object* v_toCold_4819_; lean_object* v_mctx_4820_; lean_object* v_lctx_4821_; lean_object* v_options_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4814_ = lean_st_ref_get(v___y_4812_);
v_env_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc_ref(v_env_4815_);
lean_dec(v___x_4814_);
v___x_4816_ = 0;
v_env_4817_ = l_Lean_Environment_setRecordingDeps(v_env_4815_, v___x_4816_);
v___x_4818_ = lean_st_ref_get(v___y_4810_);
v_toCold_4819_ = lean_ctor_get(v___y_4811_, 0);
v_mctx_4820_ = lean_ctor_get(v___x_4818_, 0);
lean_inc_ref(v_mctx_4820_);
lean_dec(v___x_4818_);
v_lctx_4821_ = lean_ctor_get(v___y_4809_, 2);
v_options_4822_ = lean_ctor_get(v_toCold_4819_, 2);
lean_inc_ref(v_options_4822_);
lean_inc_ref(v_lctx_4821_);
v___x_4823_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4823_, 0, v_env_4817_);
lean_ctor_set(v___x_4823_, 1, v_mctx_4820_);
lean_ctor_set(v___x_4823_, 2, v_lctx_4821_);
lean_ctor_set(v___x_4823_, 3, v_options_4822_);
v___x_4824_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4823_);
lean_ctor_set(v___x_4824_, 1, v_msgData_4808_);
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
return v_res_4832_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4833_; double v___x_4834_; 
v___x_4833_ = lean_unsigned_to_nat(0u);
v___x_4834_ = lean_float_of_nat(v___x_4833_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_4838_, lean_object* v_msg_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v_ref_4845_; lean_object* v___x_4846_; lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4892_; 
v_ref_4845_ = lean_ctor_get(v___y_4842_, 2);
v___x_4846_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4849_ = v___x_4846_;
v_isShared_4850_ = v_isSharedCheck_4892_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4846_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4892_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; lean_object* v_traceState_4852_; lean_object* v_env_4853_; lean_object* v_nextMacroScope_4854_; lean_object* v_ngen_4855_; lean_object* v_auxDeclNGen_4856_; lean_object* v_cache_4857_; lean_object* v_recordedDeps_4858_; lean_object* v_messages_4859_; lean_object* v_infoState_4860_; lean_object* v_snapshotTasks_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4891_; 
v___x_4851_ = lean_st_ref_take(v___y_4843_);
v_traceState_4852_ = lean_ctor_get(v___x_4851_, 4);
v_env_4853_ = lean_ctor_get(v___x_4851_, 0);
v_nextMacroScope_4854_ = lean_ctor_get(v___x_4851_, 1);
v_ngen_4855_ = lean_ctor_get(v___x_4851_, 2);
v_auxDeclNGen_4856_ = lean_ctor_get(v___x_4851_, 3);
v_cache_4857_ = lean_ctor_get(v___x_4851_, 5);
v_recordedDeps_4858_ = lean_ctor_get(v___x_4851_, 6);
v_messages_4859_ = lean_ctor_get(v___x_4851_, 7);
v_infoState_4860_ = lean_ctor_get(v___x_4851_, 8);
v_snapshotTasks_4861_ = lean_ctor_get(v___x_4851_, 9);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4863_ = v___x_4851_;
v_isShared_4864_ = v_isSharedCheck_4891_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_snapshotTasks_4861_);
lean_inc(v_infoState_4860_);
lean_inc(v_messages_4859_);
lean_inc(v_recordedDeps_4858_);
lean_inc(v_cache_4857_);
lean_inc(v_traceState_4852_);
lean_inc(v_auxDeclNGen_4856_);
lean_inc(v_ngen_4855_);
lean_inc(v_nextMacroScope_4854_);
lean_inc(v_env_4853_);
lean_dec(v___x_4851_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4891_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
uint64_t v_tid_4865_; lean_object* v_traces_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4890_; 
v_tid_4865_ = lean_ctor_get_uint64(v_traceState_4852_, sizeof(void*)*1);
v_traces_4866_ = lean_ctor_get(v_traceState_4852_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_traceState_4852_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4868_ = v_traceState_4852_;
v_isShared_4869_ = v_isSharedCheck_4890_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_traces_4866_);
lean_dec(v_traceState_4852_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4890_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; double v___x_4872_; uint8_t v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4870_ = lean_box(0);
v___x_4871_ = lean_box(0);
v___x_4872_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4873_ = 0;
v___x_4874_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4875_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4875_, 0, v_cls_4838_);
lean_ctor_set(v___x_4875_, 1, v___x_4871_);
lean_ctor_set(v___x_4875_, 2, v___x_4874_);
lean_ctor_set_float(v___x_4875_, sizeof(void*)*3, v___x_4872_);
lean_ctor_set_float(v___x_4875_, sizeof(void*)*3 + 8, v___x_4872_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*3 + 16, v___x_4873_);
v___x_4876_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4877_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4875_);
lean_ctor_set(v___x_4877_, 1, v_a_4847_);
lean_ctor_set(v___x_4877_, 2, v___x_4876_);
lean_inc(v_ref_4845_);
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v_ref_4845_);
lean_ctor_set(v___x_4878_, 1, v___x_4877_);
v___x_4879_ = l_Lean_PersistentArray_push___redArg(v_traces_4866_, v___x_4878_);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v___x_4879_);
v___x_4881_ = v___x_4868_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4879_);
lean_ctor_set_uint64(v_reuseFailAlloc_4889_, sizeof(void*)*1, v_tid_4865_);
v___x_4881_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
lean_object* v___x_4883_; 
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 4, v___x_4881_);
v___x_4883_ = v___x_4863_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_env_4853_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v_nextMacroScope_4854_);
lean_ctor_set(v_reuseFailAlloc_4888_, 2, v_ngen_4855_);
lean_ctor_set(v_reuseFailAlloc_4888_, 3, v_auxDeclNGen_4856_);
lean_ctor_set(v_reuseFailAlloc_4888_, 4, v___x_4881_);
lean_ctor_set(v_reuseFailAlloc_4888_, 5, v_cache_4857_);
lean_ctor_set(v_reuseFailAlloc_4888_, 6, v_recordedDeps_4858_);
lean_ctor_set(v_reuseFailAlloc_4888_, 7, v_messages_4859_);
lean_ctor_set(v_reuseFailAlloc_4888_, 8, v_infoState_4860_);
lean_ctor_set(v_reuseFailAlloc_4888_, 9, v_snapshotTasks_4861_);
v___x_4883_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4884_ = lean_st_ref_put(v___y_4843_, v___x_4883_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4870_);
v___x_4886_ = v___x_4849_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4870_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4893_, lean_object* v_msg_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4893_, v_msg_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(uint8_t v___x_4901_, lean_object* v___f_4902_, lean_object* v_____r_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v___x_4917_; lean_object* v_caches_4918_; lean_object* v_typeAnalysis_4919_; lean_object* v_target_4920_; lean_object* v_hypotheses_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4931_; 
v___x_4917_ = lean_st_ref_take(v___y_4906_);
v_caches_4918_ = lean_ctor_get(v___x_4917_, 0);
v_typeAnalysis_4919_ = lean_ctor_get(v___x_4917_, 1);
v_target_4920_ = lean_ctor_get(v___x_4917_, 2);
v_hypotheses_4921_ = lean_ctor_get(v___x_4917_, 3);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4923_ = v___x_4917_;
v_isShared_4924_ = v_isSharedCheck_4931_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_hypotheses_4921_);
lean_inc(v_target_4920_);
lean_inc(v_typeAnalysis_4919_);
lean_inc(v_caches_4918_);
lean_dec(v___x_4917_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4931_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4925_; lean_object* v___x_4927_; 
v___x_4925_ = lean_box(0);
if (v_isShared_4924_ == 0)
{
v___x_4927_ = v___x_4923_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_caches_4918_);
lean_ctor_set(v_reuseFailAlloc_4930_, 1, v_typeAnalysis_4919_);
lean_ctor_set(v_reuseFailAlloc_4930_, 2, v_target_4920_);
lean_ctor_set(v_reuseFailAlloc_4930_, 3, v_hypotheses_4921_);
v___x_4927_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
lean_ctor_set_uint8(v___x_4927_, sizeof(void*)*4, v___x_4901_);
v___x_4928_ = lean_st_ref_put(v___y_4906_, v___x_4927_);
lean_inc(v___y_4915_);
lean_inc_ref(v___y_4914_);
lean_inc(v___y_4913_);
lean_inc_ref(v___y_4912_);
lean_inc(v___y_4911_);
lean_inc_ref(v___y_4910_);
lean_inc(v___y_4909_);
lean_inc_ref(v___y_4908_);
lean_inc(v___y_4907_);
lean_inc(v___y_4906_);
lean_inc_ref(v___y_4905_);
lean_inc(v___y_4904_);
v___x_4929_ = lean_apply_14(v___f_4902_, v___x_4925_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, lean_box(0));
return v___x_4929_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1___boxed(lean_object* v___x_4932_, lean_object* v___f_4933_, lean_object* v_____r_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
uint8_t v___x_35736__boxed_4948_; lean_object* v_res_4949_; 
v___x_35736__boxed_4948_ = lean_unbox(v___x_4932_);
v_res_4949_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_35736__boxed_4948_, v___f_4933_, v_____r_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec(v___y_4940_);
lean_dec_ref(v___y_4939_);
lean_dec(v___y_4938_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(lean_object* v_snd_4950_, lean_object* v_a_4951_, lean_object* v___x_4952_, lean_object* v_____r_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4967_ = lean_array_push(v_snd_4950_, v_a_4951_);
v___x_4968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4952_);
lean_ctor_set(v___x_4968_, 1, v___x_4967_);
v___x_4969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
v___x_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_4971_ = _args[0];
lean_object* v_a_4972_ = _args[1];
lean_object* v___x_4973_ = _args[2];
lean_object* v_____r_4974_ = _args[3];
lean_object* v___y_4975_ = _args[4];
lean_object* v___y_4976_ = _args[5];
lean_object* v___y_4977_ = _args[6];
lean_object* v___y_4978_ = _args[7];
lean_object* v___y_4979_ = _args[8];
lean_object* v___y_4980_ = _args[9];
lean_object* v___y_4981_ = _args[10];
lean_object* v___y_4982_ = _args[11];
lean_object* v___y_4983_ = _args[12];
lean_object* v___y_4984_ = _args[13];
lean_object* v___y_4985_ = _args[14];
lean_object* v___y_4986_ = _args[15];
lean_object* v___y_4987_ = _args[16];
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_4971_, v_a_4972_, v___x_4973_, v_____r_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_);
lean_dec(v___y_4986_);
lean_dec_ref(v___y_4985_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec(v___y_4978_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_4989_, lean_object* v___x_4990_, lean_object* v_methods_4991_, lean_object* v_config_4992_, lean_object* v_a_4993_, lean_object* v_b_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v___y_5009_; uint8_t v___x_5031_; 
v___x_5031_ = lean_nat_dec_lt(v_a_4993_, v_upperBound_4989_);
if (v___x_5031_ == 0)
{
lean_object* v___x_5032_; 
lean_dec(v_a_4993_);
lean_dec_ref(v_config_4992_);
lean_dec_ref(v_methods_4991_);
v___x_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5032_, 0, v_b_4994_);
return v___x_5032_;
}
else
{
lean_object* v_snd_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5131_; 
v_snd_5033_ = lean_ctor_get(v_b_4994_, 1);
v_isSharedCheck_5131_ = !lean_is_exclusive(v_b_4994_);
if (v_isSharedCheck_5131_ == 0)
{
lean_object* v_unused_5132_; 
v_unused_5132_ = lean_ctor_get(v_b_4994_, 0);
lean_dec(v_unused_5132_);
v___x_5035_ = v_b_4994_;
v_isShared_5036_ = v_isSharedCheck_5131_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_snd_5033_);
lean_dec(v_b_4994_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5131_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v_type_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5037_ = lean_box(0);
v___x_5038_ = lean_array_fget_borrowed(v___x_4990_, v_a_4993_);
v___x_5039_ = lean_st_ref_take(v___y_4995_);
v___x_5040_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5041_ = lean_st_ref_put(v___y_4995_, v___x_5040_);
v_type_5042_ = lean_ctor_get(v___x_5038_, 1);
v___x_5043_ = lean_unsigned_to_nat(0u);
v___x_5044_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
lean_ctor_set(v___x_5044_, 1, v___x_5039_);
lean_ctor_set(v___x_5044_, 2, v___x_5040_);
lean_ctor_set(v___x_5044_, 3, v___x_5040_);
lean_inc_ref(v_type_5042_);
v___x_5045_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_5045_, 0, v_type_5042_);
lean_inc_ref(v_config_4992_);
lean_inc_ref(v_methods_4991_);
v___x_5046_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_5045_, v_methods_4991_, v_config_4992_, v___x_5044_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5046_) == 0)
{
lean_object* v_a_5047_; lean_object* v_snd_5048_; lean_object* v_fst_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5122_; 
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc(v_a_5047_);
lean_dec_ref_known(v___x_5046_, 1);
v_snd_5048_ = lean_ctor_get(v_a_5047_, 1);
v_fst_5049_ = lean_ctor_get(v_a_5047_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v_a_5047_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5051_ = v_a_5047_;
v_isShared_5052_ = v_isSharedCheck_5122_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_snd_5048_);
lean_inc(v_fst_5049_);
lean_dec(v_a_5047_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5122_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v_persistentCache_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v_persistentCache_5053_ = lean_ctor_get(v_snd_5048_, 1);
lean_inc_ref(v_persistentCache_5053_);
lean_dec(v_snd_5048_);
v___x_5054_ = lean_st_ref_swap(v___y_4995_, v_persistentCache_5053_);
lean_dec(v___x_5054_);
lean_inc(v___x_5038_);
v___x_5055_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_5038_, v_fst_5049_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v_type_5057_; lean_object* v_value_5058_; uint8_t v___x_5059_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc(v_a_5056_);
lean_dec_ref_known(v___x_5055_, 1);
v_type_5057_ = lean_ctor_get(v_a_5056_, 1);
v_value_5058_ = lean_ctor_get(v_a_5056_, 2);
lean_inc_ref(v_type_5057_);
v___x_5059_ = l_Lean_Expr_isFalse(v_type_5057_);
if (v___x_5059_ == 0)
{
lean_object* v___f_5060_; uint8_t v___x_5061_; 
lean_del_object(v___x_5051_);
lean_inc(v_a_5056_);
lean_inc(v_snd_5033_);
v___f_5060_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5060_, 0, v_snd_5033_);
lean_closure_set(v___f_5060_, 1, v_a_5056_);
lean_closure_set(v___f_5060_, 2, v___x_5037_);
v___x_5061_ = lean_expr_eqv(v_type_5042_, v_type_5057_);
if (v___x_5061_ == 0)
{
lean_object* v_toCold_5062_; lean_object* v_options_5063_; lean_object* v_inheritedTraceOptions_5064_; uint8_t v_hasTrace_5065_; 
lean_inc_ref(v_type_5057_);
lean_dec(v_a_5056_);
lean_dec(v_snd_5033_);
v_toCold_5062_ = lean_ctor_get(v___y_5005_, 0);
v_options_5063_ = lean_ctor_get(v_toCold_5062_, 2);
v_inheritedTraceOptions_5064_ = lean_ctor_get(v_toCold_5062_, 11);
v_hasTrace_5065_ = lean_ctor_get_uint8(v_options_5063_, sizeof(void*)*1);
if (v_hasTrace_5065_ == 0)
{
lean_dec_ref(v_type_5057_);
lean_del_object(v___x_5035_);
goto v___jp_5066_;
}
else
{
lean_object* v___x_5069_; lean_object* v___x_5070_; uint8_t v___x_5071_; 
v___x_5069_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5070_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5071_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5064_, v_options_5063_, v___x_5070_);
if (v___x_5071_ == 0)
{
lean_dec_ref(v_type_5057_);
lean_del_object(v___x_5035_);
goto v___jp_5066_;
}
else
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5075_; 
lean_inc_ref(v_type_5042_);
v___x_5072_ = l_Lean_MessageData_ofExpr(v_type_5042_);
v___x_5073_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5036_ == 0)
{
lean_ctor_set_tag(v___x_5035_, 7);
lean_ctor_set(v___x_5035_, 1, v___x_5073_);
lean_ctor_set(v___x_5035_, 0, v___x_5072_);
v___x_5075_ = v___x_5035_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5072_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v___x_5073_);
v___x_5075_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5076_ = l_Lean_MessageData_ofExpr(v_type_5057_);
v___x_5077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5075_);
lean_ctor_set(v___x_5077_, 1, v___x_5076_);
v___x_5078_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_5069_, v___x_5077_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v_a_5079_; lean_object* v___x_5080_; 
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
lean_inc(v_a_5079_);
lean_dec_ref_known(v___x_5078_, 1);
v___x_5080_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5031_, v___f_5060_, v_a_5079_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5009_ = v___x_5080_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
lean_dec_ref(v___f_5060_);
lean_dec(v_a_4993_);
lean_dec_ref(v_config_4992_);
lean_dec_ref(v_methods_4991_);
v_a_5081_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5078_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5078_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
}
v___jp_5066_:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = lean_box(0);
v___x_5068_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5031_, v___f_5060_, v___x_5067_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5009_ = v___x_5068_;
goto v___jp_5008_;
}
}
else
{
lean_object* v___x_5090_; lean_object* v___x_5091_; 
lean_dec_ref(v___f_5060_);
lean_del_object(v___x_5035_);
v___x_5090_ = lean_box(0);
v___x_5091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5033_, v_a_5056_, v___x_5037_, v___x_5090_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5009_ = v___x_5091_;
goto v___jp_5008_;
}
}
else
{
lean_object* v___x_5092_; 
lean_inc_ref(v_value_5058_);
lean_dec(v_a_5056_);
lean_del_object(v___x_5035_);
lean_dec(v_a_4993_);
lean_dec_ref(v_config_4992_);
lean_dec_ref(v_methods_4991_);
v___x_5092_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5058_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5104_; 
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5104_ == 0)
{
lean_object* v_unused_5105_; 
v_unused_5105_ = lean_ctor_get(v___x_5092_, 0);
lean_dec(v_unused_5105_);
v___x_5094_ = v___x_5092_;
v_isShared_5095_ = v_isSharedCheck_5104_;
goto v_resetjp_5093_;
}
else
{
lean_dec(v___x_5092_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5104_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5099_; 
v___x_5096_ = lean_box(v___x_5031_);
v___x_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5096_);
if (v_isShared_5052_ == 0)
{
lean_ctor_set(v___x_5051_, 1, v_snd_5033_);
lean_ctor_set(v___x_5051_, 0, v___x_5097_);
v___x_5099_ = v___x_5051_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5097_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_snd_5033_);
v___x_5099_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
lean_object* v___x_5101_; 
if (v_isShared_5095_ == 0)
{
lean_ctor_set(v___x_5094_, 0, v___x_5099_);
v___x_5101_ = v___x_5094_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5099_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5113_; 
lean_del_object(v___x_5051_);
lean_dec(v_snd_5033_);
v_a_5106_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5108_ = v___x_5092_;
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5092_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
if (v_isShared_5109_ == 0)
{
v___x_5111_ = v___x_5108_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
}
}
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_del_object(v___x_5051_);
lean_del_object(v___x_5035_);
lean_dec(v_snd_5033_);
lean_dec(v_a_4993_);
lean_dec_ref(v_config_4992_);
lean_dec_ref(v_methods_4991_);
v_a_5114_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5055_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5055_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
}
}
else
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5130_; 
lean_del_object(v___x_5035_);
lean_dec(v_snd_5033_);
lean_dec(v_a_4993_);
lean_dec_ref(v_config_4992_);
lean_dec_ref(v_methods_4991_);
v_a_5123_ = lean_ctor_get(v___x_5046_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5125_ = v___x_5046_;
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5046_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
}
v___jp_5008_:
{
if (lean_obj_tag(v___y_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5022_; 
v_a_5010_ = lean_ctor_get(v___y_5009_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___y_5009_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5012_ = v___y_5009_;
v_isShared_5013_ = v_isSharedCheck_5022_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___y_5009_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5022_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
if (lean_obj_tag(v_a_5010_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5016_; 
lean_dec(v_a_4993_);
lean_dec_ref(v_config_4992_);
lean_dec_ref(v_methods_4991_);
v_a_5014_ = lean_ctor_get(v_a_5010_, 0);
lean_inc(v_a_5014_);
lean_dec_ref_known(v_a_5010_, 1);
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 0, v_a_5014_);
v___x_5016_ = v___x_5012_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_a_5014_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
lean_del_object(v___x_5012_);
v_a_5018_ = lean_ctor_get(v_a_5010_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v_a_5010_, 1);
v___x_5019_ = lean_unsigned_to_nat(1u);
v___x_5020_ = lean_nat_add(v_a_4993_, v___x_5019_);
lean_dec(v_a_4993_);
v_a_4993_ = v___x_5020_;
v_b_4994_ = v_a_5018_;
goto _start;
}
}
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5030_; 
lean_dec(v_a_4993_);
lean_dec_ref(v_config_4992_);
lean_dec_ref(v_methods_4991_);
v_a_5023_ = lean_ctor_get(v___y_5009_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___y_5009_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5025_ = v___y_5009_;
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___y_5009_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5028_; 
if (v_isShared_5026_ == 0)
{
v___x_5028_ = v___x_5025_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_a_5023_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5133_ = _args[0];
lean_object* v___x_5134_ = _args[1];
lean_object* v_methods_5135_ = _args[2];
lean_object* v_config_5136_ = _args[3];
lean_object* v_a_5137_ = _args[4];
lean_object* v_b_5138_ = _args[5];
lean_object* v___y_5139_ = _args[6];
lean_object* v___y_5140_ = _args[7];
lean_object* v___y_5141_ = _args[8];
lean_object* v___y_5142_ = _args[9];
lean_object* v___y_5143_ = _args[10];
lean_object* v___y_5144_ = _args[11];
lean_object* v___y_5145_ = _args[12];
lean_object* v___y_5146_ = _args[13];
lean_object* v___y_5147_ = _args[14];
lean_object* v___y_5148_ = _args[15];
lean_object* v___y_5149_ = _args[16];
lean_object* v___y_5150_ = _args[17];
lean_object* v___y_5151_ = _args[18];
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5133_, v___x_5134_, v_methods_5135_, v_config_5136_, v_a_5137_, v_b_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
lean_dec(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___x_5134_);
lean_dec(v_upperBound_5133_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_5153_, lean_object* v_config_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v___x_5168_; lean_object* v_hypotheses_5169_; lean_object* v___x_5170_; lean_object* v_newHyps_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; 
v___x_5168_ = lean_st_ref_get(v_a_5157_);
v_hypotheses_5169_ = lean_ctor_get(v___x_5168_, 3);
lean_inc_ref(v_hypotheses_5169_);
lean_dec(v___x_5168_);
v___x_5170_ = lean_array_get_size(v_hypotheses_5169_);
v_newHyps_5171_ = lean_mk_empty_array_with_capacity(v___x_5170_);
v___x_5172_ = lean_unsigned_to_nat(0u);
v___x_5173_ = lean_box(0);
v___x_5174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5174_, 0, v___x_5173_);
lean_ctor_set(v___x_5174_, 1, v_newHyps_5171_);
v___x_5175_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_5170_, v_hypotheses_5169_, v_methods_5153_, v_config_5154_, v___x_5172_, v___x_5174_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec_ref(v_hypotheses_5169_);
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5205_; 
v_a_5176_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5178_ = v___x_5175_;
v_isShared_5179_ = v_isSharedCheck_5205_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5175_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5205_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v_fst_5180_; 
v_fst_5180_ = lean_ctor_get(v_a_5176_, 0);
if (lean_obj_tag(v_fst_5180_) == 0)
{
lean_object* v_snd_5181_; lean_object* v___x_5182_; lean_object* v_caches_5183_; lean_object* v_typeAnalysis_5184_; lean_object* v_target_5185_; uint8_t v_didChange_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5199_; 
v_snd_5181_ = lean_ctor_get(v_a_5176_, 1);
lean_inc(v_snd_5181_);
lean_dec(v_a_5176_);
v___x_5182_ = lean_st_ref_take(v_a_5157_);
v_caches_5183_ = lean_ctor_get(v___x_5182_, 0);
v_typeAnalysis_5184_ = lean_ctor_get(v___x_5182_, 1);
v_target_5185_ = lean_ctor_get(v___x_5182_, 2);
v_didChange_5186_ = lean_ctor_get_uint8(v___x_5182_, sizeof(void*)*4);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5199_ == 0)
{
lean_object* v_unused_5200_; 
v_unused_5200_ = lean_ctor_get(v___x_5182_, 3);
lean_dec(v_unused_5200_);
v___x_5188_ = v___x_5182_;
v_isShared_5189_ = v_isSharedCheck_5199_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_target_5185_);
lean_inc(v_typeAnalysis_5184_);
lean_inc(v_caches_5183_);
lean_dec(v___x_5182_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5199_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
lean_ctor_set(v___x_5188_, 3, v_snd_5181_);
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_caches_5183_);
lean_ctor_set(v_reuseFailAlloc_5198_, 1, v_typeAnalysis_5184_);
lean_ctor_set(v_reuseFailAlloc_5198_, 2, v_target_5185_);
lean_ctor_set(v_reuseFailAlloc_5198_, 3, v_snd_5181_);
lean_ctor_set_uint8(v_reuseFailAlloc_5198_, sizeof(void*)*4, v_didChange_5186_);
v___x_5191_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
lean_object* v___x_5192_; uint8_t v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5196_; 
v___x_5192_ = lean_st_ref_put(v_a_5157_, v___x_5191_);
v___x_5193_ = 0;
v___x_5194_ = lean_box(v___x_5193_);
if (v_isShared_5179_ == 0)
{
lean_ctor_set(v___x_5178_, 0, v___x_5194_);
v___x_5196_ = v___x_5178_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v___x_5194_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
else
{
lean_object* v_val_5201_; lean_object* v___x_5203_; 
lean_inc_ref(v_fst_5180_);
lean_dec(v_a_5176_);
v_val_5201_ = lean_ctor_get(v_fst_5180_, 0);
lean_inc(v_val_5201_);
lean_dec_ref_known(v_fst_5180_, 1);
if (v_isShared_5179_ == 0)
{
lean_ctor_set(v___x_5178_, 0, v_val_5201_);
v___x_5203_ = v___x_5178_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_val_5201_);
v___x_5203_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
return v___x_5203_;
}
}
}
}
else
{
lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
v_a_5206_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5175_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5175_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5211_; 
if (v_isShared_5209_ == 0)
{
v___x_5211_ = v___x_5208_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
return v___x_5211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_5214_, lean_object* v_config_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5214_, v_config_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec(v_a_5218_);
lean_dec_ref(v_a_5217_);
lean_dec(v_a_5216_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_5230_, lean_object* v_msg_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_5230_, v_msg_5231_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_5246_, lean_object* v_msg_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_5246_, v_msg_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_upperBound_5262_, lean_object* v___x_5263_, lean_object* v_methods_5264_, lean_object* v_config_5265_, lean_object* v_inst_5266_, lean_object* v_R_5267_, lean_object* v_a_5268_, lean_object* v_b_5269_, lean_object* v_c_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v___x_5284_; 
v___x_5284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_upperBound_5262_, v___x_5263_, v_methods_5264_, v_config_5265_, v_a_5268_, v_b_5269_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5285_ = _args[0];
lean_object* v___x_5286_ = _args[1];
lean_object* v_methods_5287_ = _args[2];
lean_object* v_config_5288_ = _args[3];
lean_object* v_inst_5289_ = _args[4];
lean_object* v_R_5290_ = _args[5];
lean_object* v_a_5291_ = _args[6];
lean_object* v_b_5292_ = _args[7];
lean_object* v_c_5293_ = _args[8];
lean_object* v___y_5294_ = _args[9];
lean_object* v___y_5295_ = _args[10];
lean_object* v___y_5296_ = _args[11];
lean_object* v___y_5297_ = _args[12];
lean_object* v___y_5298_ = _args[13];
lean_object* v___y_5299_ = _args[14];
lean_object* v___y_5300_ = _args[15];
lean_object* v___y_5301_ = _args[16];
lean_object* v___y_5302_ = _args[17];
lean_object* v___y_5303_ = _args[18];
lean_object* v___y_5304_ = _args[19];
lean_object* v___y_5305_ = _args[20];
lean_object* v___y_5306_ = _args[21];
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_upperBound_5285_, v___x_5286_, v_methods_5287_, v_config_5288_, v_inst_5289_, v_R_5290_, v_a_5291_, v_b_5292_, v_c_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec(v___y_5297_);
lean_dec(v___y_5296_);
lean_dec_ref(v___y_5295_);
lean_dec(v___y_5294_);
lean_dec_ref(v___x_5286_);
lean_dec(v_upperBound_5285_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_5308_, lean_object* v_config_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_){
_start:
{
lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___x_5322_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg___closed__0);
v___x_5323_ = lean_st_mk_ref(v___x_5322_);
v___x_5324_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_5308_, v_config_5309_, v___x_5323_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5333_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5327_ = v___x_5324_;
v_isShared_5328_ = v_isSharedCheck_5333_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5324_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5333_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5329_; lean_object* v___x_5331_; 
v___x_5329_ = lean_st_ref_get(v___x_5323_);
lean_dec(v___x_5323_);
lean_dec(v___x_5329_);
if (v_isShared_5328_ == 0)
{
v___x_5331_ = v___x_5327_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5325_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
else
{
lean_dec(v___x_5323_);
return v___x_5324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_5334_, lean_object* v_config_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_){
_start:
{
lean_object* v_res_5348_; 
v_res_5348_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_5334_, v_config_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_);
lean_dec(v_a_5346_);
lean_dec_ref(v_a_5345_);
lean_dec(v_a_5344_);
lean_dec_ref(v_a_5343_);
lean_dec(v_a_5342_);
lean_dec_ref(v_a_5341_);
lean_dec(v_a_5340_);
lean_dec_ref(v_a_5339_);
lean_dec(v_a_5338_);
lean_dec(v_a_5337_);
lean_dec_ref(v_a_5336_);
return v_res_5348_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_5349_, lean_object* v_msg_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_){
_start:
{
lean_object* v_ref_5356_; lean_object* v___x_5357_; lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5403_; 
v_ref_5356_ = lean_ctor_get(v___y_5353_, 2);
v___x_5357_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
v_a_5358_ = lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5360_ = v___x_5357_;
v_isShared_5361_ = v_isSharedCheck_5403_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5357_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5403_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5362_; lean_object* v_traceState_5363_; lean_object* v_env_5364_; lean_object* v_nextMacroScope_5365_; lean_object* v_ngen_5366_; lean_object* v_auxDeclNGen_5367_; lean_object* v_cache_5368_; lean_object* v_recordedDeps_5369_; lean_object* v_messages_5370_; lean_object* v_infoState_5371_; lean_object* v_snapshotTasks_5372_; lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5402_; 
v___x_5362_ = lean_st_ref_take(v___y_5354_);
v_traceState_5363_ = lean_ctor_get(v___x_5362_, 4);
v_env_5364_ = lean_ctor_get(v___x_5362_, 0);
v_nextMacroScope_5365_ = lean_ctor_get(v___x_5362_, 1);
v_ngen_5366_ = lean_ctor_get(v___x_5362_, 2);
v_auxDeclNGen_5367_ = lean_ctor_get(v___x_5362_, 3);
v_cache_5368_ = lean_ctor_get(v___x_5362_, 5);
v_recordedDeps_5369_ = lean_ctor_get(v___x_5362_, 6);
v_messages_5370_ = lean_ctor_get(v___x_5362_, 7);
v_infoState_5371_ = lean_ctor_get(v___x_5362_, 8);
v_snapshotTasks_5372_ = lean_ctor_get(v___x_5362_, 9);
v_isSharedCheck_5402_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5374_ = v___x_5362_;
v_isShared_5375_ = v_isSharedCheck_5402_;
goto v_resetjp_5373_;
}
else
{
lean_inc(v_snapshotTasks_5372_);
lean_inc(v_infoState_5371_);
lean_inc(v_messages_5370_);
lean_inc(v_recordedDeps_5369_);
lean_inc(v_cache_5368_);
lean_inc(v_traceState_5363_);
lean_inc(v_auxDeclNGen_5367_);
lean_inc(v_ngen_5366_);
lean_inc(v_nextMacroScope_5365_);
lean_inc(v_env_5364_);
lean_dec(v___x_5362_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5402_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
uint64_t v_tid_5376_; lean_object* v_traces_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5401_; 
v_tid_5376_ = lean_ctor_get_uint64(v_traceState_5363_, sizeof(void*)*1);
v_traces_5377_ = lean_ctor_get(v_traceState_5363_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v_traceState_5363_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5379_ = v_traceState_5363_;
v_isShared_5380_ = v_isSharedCheck_5401_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_traces_5377_);
lean_dec(v_traceState_5363_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5401_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5381_; lean_object* v___x_5382_; double v___x_5383_; uint8_t v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5392_; 
v___x_5381_ = lean_box(0);
v___x_5382_ = lean_box(0);
v___x_5383_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5384_ = 0;
v___x_5385_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5386_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5386_, 0, v_cls_5349_);
lean_ctor_set(v___x_5386_, 1, v___x_5382_);
lean_ctor_set(v___x_5386_, 2, v___x_5385_);
lean_ctor_set_float(v___x_5386_, sizeof(void*)*3, v___x_5383_);
lean_ctor_set_float(v___x_5386_, sizeof(void*)*3 + 8, v___x_5383_);
lean_ctor_set_uint8(v___x_5386_, sizeof(void*)*3 + 16, v___x_5384_);
v___x_5387_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5388_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5386_);
lean_ctor_set(v___x_5388_, 1, v_a_5358_);
lean_ctor_set(v___x_5388_, 2, v___x_5387_);
lean_inc(v_ref_5356_);
v___x_5389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5389_, 0, v_ref_5356_);
lean_ctor_set(v___x_5389_, 1, v___x_5388_);
v___x_5390_ = l_Lean_PersistentArray_push___redArg(v_traces_5377_, v___x_5389_);
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 0, v___x_5390_);
v___x_5392_ = v___x_5379_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5390_);
lean_ctor_set_uint64(v_reuseFailAlloc_5400_, sizeof(void*)*1, v_tid_5376_);
v___x_5392_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
lean_object* v___x_5394_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v___x_5392_);
v___x_5394_ = v___x_5374_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_env_5364_);
lean_ctor_set(v_reuseFailAlloc_5399_, 1, v_nextMacroScope_5365_);
lean_ctor_set(v_reuseFailAlloc_5399_, 2, v_ngen_5366_);
lean_ctor_set(v_reuseFailAlloc_5399_, 3, v_auxDeclNGen_5367_);
lean_ctor_set(v_reuseFailAlloc_5399_, 4, v___x_5392_);
lean_ctor_set(v_reuseFailAlloc_5399_, 5, v_cache_5368_);
lean_ctor_set(v_reuseFailAlloc_5399_, 6, v_recordedDeps_5369_);
lean_ctor_set(v_reuseFailAlloc_5399_, 7, v_messages_5370_);
lean_ctor_set(v_reuseFailAlloc_5399_, 8, v_infoState_5371_);
lean_ctor_set(v_reuseFailAlloc_5399_, 9, v_snapshotTasks_5372_);
v___x_5394_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5395_; lean_object* v___x_5397_; 
v___x_5395_ = lean_st_ref_put(v___y_5354_, v___x_5394_);
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 0, v___x_5381_);
v___x_5397_ = v___x_5360_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v___x_5381_);
v___x_5397_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
return v___x_5397_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_5404_, lean_object* v_msg_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5404_, v_msg_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_);
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5406_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_upperBound_5412_, lean_object* v___x_5413_, lean_object* v_methods_5414_, lean_object* v_config_5415_, lean_object* v_a_5416_, lean_object* v_b_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_){
_start:
{
lean_object* v___y_5432_; uint8_t v___x_5454_; 
v___x_5454_ = lean_nat_dec_lt(v_a_5416_, v_upperBound_5412_);
if (v___x_5454_ == 0)
{
lean_object* v___x_5455_; 
lean_dec(v_a_5416_);
lean_dec_ref(v_config_5415_);
lean_dec_ref(v_methods_5414_);
v___x_5455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5455_, 0, v_b_5417_);
return v___x_5455_;
}
else
{
lean_object* v_snd_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5561_; 
v_snd_5456_ = lean_ctor_get(v_b_5417_, 1);
v_isSharedCheck_5561_ = !lean_is_exclusive(v_b_5417_);
if (v_isSharedCheck_5561_ == 0)
{
lean_object* v_unused_5562_; 
v_unused_5562_ = lean_ctor_get(v_b_5417_, 0);
lean_dec(v_unused_5562_);
v___x_5458_ = v_b_5417_;
v_isShared_5459_ = v_isSharedCheck_5561_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_snd_5456_);
lean_dec(v_b_5417_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5561_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v_type_5465_; lean_object* v___x_5466_; lean_object* v___x_5468_; 
v___x_5460_ = lean_box(0);
v___x_5461_ = lean_array_fget_borrowed(v___x_5413_, v_a_5416_);
v___x_5462_ = lean_st_ref_take(v___y_5418_);
v___x_5463_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5464_ = lean_st_ref_put(v___y_5418_, v___x_5463_);
v_type_5465_ = lean_ctor_get(v___x_5461_, 1);
v___x_5466_ = lean_unsigned_to_nat(0u);
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 1, v___x_5462_);
lean_ctor_set(v___x_5458_, 0, v___x_5466_);
v___x_5468_ = v___x_5458_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5466_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v___x_5462_);
v___x_5468_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; 
lean_inc_ref(v_type_5465_);
v___x_5469_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_5469_, 0, v_type_5465_);
lean_inc_ref(v_config_5415_);
lean_inc_ref(v_methods_5414_);
v___x_5470_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_5469_, v_methods_5414_, v_config_5415_, v___x_5468_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_object* v_a_5471_; lean_object* v_snd_5472_; lean_object* v_fst_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5551_; 
v_a_5471_ = lean_ctor_get(v___x_5470_, 0);
lean_inc(v_a_5471_);
lean_dec_ref_known(v___x_5470_, 1);
v_snd_5472_ = lean_ctor_get(v_a_5471_, 1);
v_fst_5473_ = lean_ctor_get(v_a_5471_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v_a_5471_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5475_ = v_a_5471_;
v_isShared_5476_ = v_isSharedCheck_5551_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_snd_5472_);
lean_inc(v_fst_5473_);
lean_dec(v_a_5471_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5551_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v_cache_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5549_; 
v_cache_5477_ = lean_ctor_get(v_snd_5472_, 1);
v_isSharedCheck_5549_ = !lean_is_exclusive(v_snd_5472_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; 
v_unused_5550_ = lean_ctor_get(v_snd_5472_, 0);
lean_dec(v_unused_5550_);
v___x_5479_ = v_snd_5472_;
v_isShared_5480_ = v_isSharedCheck_5549_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_cache_5477_);
lean_dec(v_snd_5472_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5549_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5481_ = lean_st_ref_swap(v___y_5418_, v_cache_5477_);
lean_dec(v___x_5481_);
lean_inc(v___x_5461_);
v___x_5482_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_5461_, v_fst_5473_);
lean_dec(v_fst_5473_);
if (lean_obj_tag(v___x_5482_) == 0)
{
lean_object* v_a_5483_; lean_object* v_type_5484_; lean_object* v_value_5485_; uint8_t v___x_5486_; 
v_a_5483_ = lean_ctor_get(v___x_5482_, 0);
lean_inc(v_a_5483_);
lean_dec_ref_known(v___x_5482_, 1);
v_type_5484_ = lean_ctor_get(v_a_5483_, 1);
v_value_5485_ = lean_ctor_get(v_a_5483_, 2);
lean_inc_ref(v_type_5484_);
v___x_5486_ = l_Lean_Expr_isFalse(v_type_5484_);
if (v___x_5486_ == 0)
{
lean_object* v___f_5487_; uint8_t v___x_5488_; 
lean_del_object(v___x_5475_);
lean_inc(v_a_5483_);
lean_inc(v_snd_5456_);
v___f_5487_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_5487_, 0, v_snd_5456_);
lean_closure_set(v___f_5487_, 1, v_a_5483_);
lean_closure_set(v___f_5487_, 2, v___x_5460_);
v___x_5488_ = lean_expr_eqv(v_type_5465_, v_type_5484_);
if (v___x_5488_ == 0)
{
lean_object* v_toCold_5489_; lean_object* v_options_5490_; lean_object* v_inheritedTraceOptions_5491_; uint8_t v_hasTrace_5492_; 
lean_inc_ref(v_type_5484_);
lean_dec(v_a_5483_);
lean_dec(v_snd_5456_);
v_toCold_5489_ = lean_ctor_get(v___y_5428_, 0);
v_options_5490_ = lean_ctor_get(v_toCold_5489_, 2);
v_inheritedTraceOptions_5491_ = lean_ctor_get(v_toCold_5489_, 11);
v_hasTrace_5492_ = lean_ctor_get_uint8(v_options_5490_, sizeof(void*)*1);
if (v_hasTrace_5492_ == 0)
{
lean_dec_ref(v_type_5484_);
lean_del_object(v___x_5479_);
goto v___jp_5493_;
}
else
{
lean_object* v___x_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; 
v___x_5496_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5497_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5498_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5491_, v_options_5490_, v___x_5497_);
if (v___x_5498_ == 0)
{
lean_dec_ref(v_type_5484_);
lean_del_object(v___x_5479_);
goto v___jp_5493_;
}
else
{
lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5502_; 
lean_inc_ref(v_type_5465_);
v___x_5499_ = l_Lean_MessageData_ofExpr(v_type_5465_);
v___x_5500_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_5480_ == 0)
{
lean_ctor_set_tag(v___x_5479_, 7);
lean_ctor_set(v___x_5479_, 1, v___x_5500_);
lean_ctor_set(v___x_5479_, 0, v___x_5499_);
v___x_5502_ = v___x_5479_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; 
v___x_5503_ = l_Lean_MessageData_ofExpr(v_type_5484_);
v___x_5504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5504_, 0, v___x_5502_);
lean_ctor_set(v___x_5504_, 1, v___x_5503_);
v___x_5505_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_5496_, v___x_5504_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v_a_5506_; lean_object* v___x_5507_; 
v_a_5506_ = lean_ctor_get(v___x_5505_, 0);
lean_inc(v_a_5506_);
lean_dec_ref_known(v___x_5505_, 1);
v___x_5507_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5454_, v___f_5487_, v_a_5506_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
v___y_5432_ = v___x_5507_;
goto v___jp_5431_;
}
else
{
lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5515_; 
lean_dec_ref(v___f_5487_);
lean_dec(v_a_5416_);
lean_dec_ref(v_config_5415_);
lean_dec_ref(v_methods_5414_);
v_a_5508_ = lean_ctor_get(v___x_5505_, 0);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5505_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5510_ = v___x_5505_;
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_dec(v___x_5505_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5513_; 
if (v_isShared_5511_ == 0)
{
v___x_5513_ = v___x_5510_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_a_5508_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
}
}
v___jp_5493_:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = lean_box(0);
v___x_5495_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__1(v___x_5454_, v___f_5487_, v___x_5494_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
v___y_5432_ = v___x_5495_;
goto v___jp_5431_;
}
}
else
{
lean_object* v___x_5517_; lean_object* v___x_5518_; 
lean_dec_ref(v___f_5487_);
lean_del_object(v___x_5479_);
v___x_5517_ = lean_box(0);
v___x_5518_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___lam__0(v_snd_5456_, v_a_5483_, v___x_5460_, v___x_5517_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
v___y_5432_ = v___x_5518_;
goto v___jp_5431_;
}
}
else
{
lean_object* v___x_5519_; 
lean_inc_ref(v_value_5485_);
lean_dec(v_a_5483_);
lean_del_object(v___x_5479_);
lean_dec(v_a_5416_);
lean_dec_ref(v_config_5415_);
lean_dec_ref(v_methods_5414_);
v___x_5519_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_5485_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
if (lean_obj_tag(v___x_5519_) == 0)
{
lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5531_; 
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5531_ == 0)
{
lean_object* v_unused_5532_; 
v_unused_5532_ = lean_ctor_get(v___x_5519_, 0);
lean_dec(v_unused_5532_);
v___x_5521_ = v___x_5519_;
v_isShared_5522_ = v_isSharedCheck_5531_;
goto v_resetjp_5520_;
}
else
{
lean_dec(v___x_5519_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5531_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5526_; 
v___x_5523_ = lean_box(v___x_5454_);
v___x_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5523_);
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 1, v_snd_5456_);
lean_ctor_set(v___x_5475_, 0, v___x_5524_);
v___x_5526_ = v___x_5475_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5524_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_snd_5456_);
v___x_5526_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5528_; 
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 0, v___x_5526_);
v___x_5528_ = v___x_5521_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5526_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
else
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5540_; 
lean_del_object(v___x_5475_);
lean_dec(v_snd_5456_);
v_a_5533_ = lean_ctor_get(v___x_5519_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5535_ = v___x_5519_;
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5519_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5538_; 
if (v_isShared_5536_ == 0)
{
v___x_5538_ = v___x_5535_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_a_5533_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
}
}
}
else
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
lean_del_object(v___x_5479_);
lean_del_object(v___x_5475_);
lean_dec(v_snd_5456_);
lean_dec(v_a_5416_);
lean_dec_ref(v_config_5415_);
lean_dec_ref(v_methods_5414_);
v_a_5541_ = lean_ctor_get(v___x_5482_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5482_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5482_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5482_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5546_; 
if (v_isShared_5544_ == 0)
{
v___x_5546_ = v___x_5543_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
}
}
}
else
{
lean_object* v_a_5552_; lean_object* v___x_5554_; uint8_t v_isShared_5555_; uint8_t v_isSharedCheck_5559_; 
lean_dec(v_snd_5456_);
lean_dec(v_a_5416_);
lean_dec_ref(v_config_5415_);
lean_dec_ref(v_methods_5414_);
v_a_5552_ = lean_ctor_get(v___x_5470_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5554_ = v___x_5470_;
v_isShared_5555_ = v_isSharedCheck_5559_;
goto v_resetjp_5553_;
}
else
{
lean_inc(v_a_5552_);
lean_dec(v___x_5470_);
v___x_5554_ = lean_box(0);
v_isShared_5555_ = v_isSharedCheck_5559_;
goto v_resetjp_5553_;
}
v_resetjp_5553_:
{
lean_object* v___x_5557_; 
if (v_isShared_5555_ == 0)
{
v___x_5557_ = v___x_5554_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_a_5552_);
v___x_5557_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
return v___x_5557_;
}
}
}
}
}
}
v___jp_5431_:
{
if (lean_obj_tag(v___y_5432_) == 0)
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5445_; 
v_a_5433_ = lean_ctor_get(v___y_5432_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v___y_5432_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5435_ = v___y_5432_;
v_isShared_5436_ = v_isSharedCheck_5445_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___y_5432_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5445_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
if (lean_obj_tag(v_a_5433_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5439_; 
lean_dec(v_a_5416_);
lean_dec_ref(v_config_5415_);
lean_dec_ref(v_methods_5414_);
v_a_5437_ = lean_ctor_get(v_a_5433_, 0);
lean_inc(v_a_5437_);
lean_dec_ref_known(v_a_5433_, 1);
if (v_isShared_5436_ == 0)
{
lean_ctor_set(v___x_5435_, 0, v_a_5437_);
v___x_5439_ = v___x_5435_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_a_5437_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
else
{
lean_object* v_a_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; 
lean_del_object(v___x_5435_);
v_a_5441_ = lean_ctor_get(v_a_5433_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v_a_5433_, 1);
v___x_5442_ = lean_unsigned_to_nat(1u);
v___x_5443_ = lean_nat_add(v_a_5416_, v___x_5442_);
lean_dec(v_a_5416_);
v_a_5416_ = v___x_5443_;
v_b_5417_ = v_a_5441_;
goto _start;
}
}
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5453_; 
lean_dec(v_a_5416_);
lean_dec_ref(v_config_5415_);
lean_dec_ref(v_methods_5414_);
v_a_5446_ = lean_ctor_get(v___y_5432_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___y_5432_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5448_ = v___y_5432_;
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_a_5446_);
lean_dec(v___y_5432_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v___x_5451_; 
if (v_isShared_5449_ == 0)
{
v___x_5451_ = v___x_5448_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5563_ = _args[0];
lean_object* v___x_5564_ = _args[1];
lean_object* v_methods_5565_ = _args[2];
lean_object* v_config_5566_ = _args[3];
lean_object* v_a_5567_ = _args[4];
lean_object* v_b_5568_ = _args[5];
lean_object* v___y_5569_ = _args[6];
lean_object* v___y_5570_ = _args[7];
lean_object* v___y_5571_ = _args[8];
lean_object* v___y_5572_ = _args[9];
lean_object* v___y_5573_ = _args[10];
lean_object* v___y_5574_ = _args[11];
lean_object* v___y_5575_ = _args[12];
lean_object* v___y_5576_ = _args[13];
lean_object* v___y_5577_ = _args[14];
lean_object* v___y_5578_ = _args[15];
lean_object* v___y_5579_ = _args[16];
lean_object* v___y_5580_ = _args[17];
lean_object* v___y_5581_ = _args[18];
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5563_, v___x_5564_, v_methods_5565_, v_config_5566_, v_a_5567_, v_b_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_);
lean_dec(v___y_5580_);
lean_dec_ref(v___y_5579_);
lean_dec(v___y_5578_);
lean_dec_ref(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec_ref(v___y_5575_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec(v___y_5572_);
lean_dec(v___y_5571_);
lean_dec_ref(v___y_5570_);
lean_dec(v___y_5569_);
lean_dec_ref(v___x_5564_);
lean_dec(v_upperBound_5563_);
return v_res_5582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_5583_, lean_object* v_config_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_){
_start:
{
lean_object* v___x_5598_; lean_object* v_hypotheses_5599_; lean_object* v___x_5600_; lean_object* v_newHyps_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5598_ = lean_st_ref_get(v_a_5587_);
v_hypotheses_5599_ = lean_ctor_get(v___x_5598_, 3);
lean_inc_ref(v_hypotheses_5599_);
lean_dec(v___x_5598_);
v___x_5600_ = lean_array_get_size(v_hypotheses_5599_);
v_newHyps_5601_ = lean_mk_empty_array_with_capacity(v___x_5600_);
v___x_5602_ = lean_unsigned_to_nat(0u);
v___x_5603_ = lean_box(0);
v___x_5604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5603_);
lean_ctor_set(v___x_5604_, 1, v_newHyps_5601_);
v___x_5605_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_5600_, v_hypotheses_5599_, v_methods_5583_, v_config_5584_, v___x_5602_, v___x_5604_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_);
lean_dec_ref(v_hypotheses_5599_);
if (lean_obj_tag(v___x_5605_) == 0)
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5635_; 
v_a_5606_ = lean_ctor_get(v___x_5605_, 0);
v_isSharedCheck_5635_ = !lean_is_exclusive(v___x_5605_);
if (v_isSharedCheck_5635_ == 0)
{
v___x_5608_ = v___x_5605_;
v_isShared_5609_ = v_isSharedCheck_5635_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5605_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5635_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v_fst_5610_; 
v_fst_5610_ = lean_ctor_get(v_a_5606_, 0);
if (lean_obj_tag(v_fst_5610_) == 0)
{
lean_object* v_snd_5611_; lean_object* v___x_5612_; lean_object* v_caches_5613_; lean_object* v_typeAnalysis_5614_; lean_object* v_target_5615_; uint8_t v_didChange_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5629_; 
v_snd_5611_ = lean_ctor_get(v_a_5606_, 1);
lean_inc(v_snd_5611_);
lean_dec(v_a_5606_);
v___x_5612_ = lean_st_ref_take(v_a_5587_);
v_caches_5613_ = lean_ctor_get(v___x_5612_, 0);
v_typeAnalysis_5614_ = lean_ctor_get(v___x_5612_, 1);
v_target_5615_ = lean_ctor_get(v___x_5612_, 2);
v_didChange_5616_ = lean_ctor_get_uint8(v___x_5612_, sizeof(void*)*4);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5612_);
if (v_isSharedCheck_5629_ == 0)
{
lean_object* v_unused_5630_; 
v_unused_5630_ = lean_ctor_get(v___x_5612_, 3);
lean_dec(v_unused_5630_);
v___x_5618_ = v___x_5612_;
v_isShared_5619_ = v_isSharedCheck_5629_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_target_5615_);
lean_inc(v_typeAnalysis_5614_);
lean_inc(v_caches_5613_);
lean_dec(v___x_5612_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5629_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
lean_ctor_set(v___x_5618_, 3, v_snd_5611_);
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_caches_5613_);
lean_ctor_set(v_reuseFailAlloc_5628_, 1, v_typeAnalysis_5614_);
lean_ctor_set(v_reuseFailAlloc_5628_, 2, v_target_5615_);
lean_ctor_set(v_reuseFailAlloc_5628_, 3, v_snd_5611_);
lean_ctor_set_uint8(v_reuseFailAlloc_5628_, sizeof(void*)*4, v_didChange_5616_);
v___x_5621_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
lean_object* v___x_5622_; uint8_t v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5626_; 
v___x_5622_ = lean_st_ref_put(v_a_5587_, v___x_5621_);
v___x_5623_ = 0;
v___x_5624_ = lean_box(v___x_5623_);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 0, v___x_5624_);
v___x_5626_ = v___x_5608_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v___x_5624_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
else
{
lean_object* v_val_5631_; lean_object* v___x_5633_; 
lean_inc_ref(v_fst_5610_);
lean_dec(v_a_5606_);
v_val_5631_ = lean_ctor_get(v_fst_5610_, 0);
lean_inc(v_val_5631_);
lean_dec_ref_known(v_fst_5610_, 1);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 0, v_val_5631_);
v___x_5633_ = v___x_5608_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_val_5631_);
v___x_5633_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
return v___x_5633_;
}
}
}
}
else
{
lean_object* v_a_5636_; lean_object* v___x_5638_; uint8_t v_isShared_5639_; uint8_t v_isSharedCheck_5643_; 
v_a_5636_ = lean_ctor_get(v___x_5605_, 0);
v_isSharedCheck_5643_ = !lean_is_exclusive(v___x_5605_);
if (v_isSharedCheck_5643_ == 0)
{
v___x_5638_ = v___x_5605_;
v_isShared_5639_ = v_isSharedCheck_5643_;
goto v_resetjp_5637_;
}
else
{
lean_inc(v_a_5636_);
lean_dec(v___x_5605_);
v___x_5638_ = lean_box(0);
v_isShared_5639_ = v_isSharedCheck_5643_;
goto v_resetjp_5637_;
}
v_resetjp_5637_:
{
lean_object* v___x_5641_; 
if (v_isShared_5639_ == 0)
{
v___x_5641_ = v___x_5638_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_a_5636_);
v___x_5641_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
return v___x_5641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_5644_, lean_object* v_config_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_){
_start:
{
lean_object* v_res_5659_; 
v_res_5659_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5644_, v_config_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
lean_dec(v_a_5655_);
lean_dec_ref(v_a_5654_);
lean_dec(v_a_5653_);
lean_dec_ref(v_a_5652_);
lean_dec(v_a_5651_);
lean_dec_ref(v_a_5650_);
lean_dec(v_a_5649_);
lean_dec(v_a_5648_);
lean_dec_ref(v_a_5647_);
lean_dec(v_a_5646_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_5660_, lean_object* v_msg_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
lean_object* v___x_5675_; 
v___x_5675_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_5660_, v_msg_5661_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_5676_, lean_object* v_msg_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
lean_object* v_res_5691_; 
v_res_5691_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_5676_, v_msg_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_);
lean_dec(v___y_5689_);
lean_dec_ref(v___y_5688_);
lean_dec(v___y_5687_);
lean_dec_ref(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec(v___y_5680_);
lean_dec_ref(v___y_5679_);
lean_dec(v___y_5678_);
return v_res_5691_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_upperBound_5692_, lean_object* v___x_5693_, lean_object* v_methods_5694_, lean_object* v_config_5695_, lean_object* v_inst_5696_, lean_object* v_R_5697_, lean_object* v_a_5698_, lean_object* v_b_5699_, lean_object* v_c_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_){
_start:
{
lean_object* v___x_5714_; 
v___x_5714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_upperBound_5692_, v___x_5693_, v_methods_5694_, v_config_5695_, v_a_5698_, v_b_5699_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_);
return v___x_5714_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_5715_ = _args[0];
lean_object* v___x_5716_ = _args[1];
lean_object* v_methods_5717_ = _args[2];
lean_object* v_config_5718_ = _args[3];
lean_object* v_inst_5719_ = _args[4];
lean_object* v_R_5720_ = _args[5];
lean_object* v_a_5721_ = _args[6];
lean_object* v_b_5722_ = _args[7];
lean_object* v_c_5723_ = _args[8];
lean_object* v___y_5724_ = _args[9];
lean_object* v___y_5725_ = _args[10];
lean_object* v___y_5726_ = _args[11];
lean_object* v___y_5727_ = _args[12];
lean_object* v___y_5728_ = _args[13];
lean_object* v___y_5729_ = _args[14];
lean_object* v___y_5730_ = _args[15];
lean_object* v___y_5731_ = _args[16];
lean_object* v___y_5732_ = _args[17];
lean_object* v___y_5733_ = _args[18];
lean_object* v___y_5734_ = _args[19];
lean_object* v___y_5735_ = _args[20];
lean_object* v___y_5736_ = _args[21];
_start:
{
lean_object* v_res_5737_; 
v_res_5737_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_upperBound_5715_, v___x_5716_, v_methods_5717_, v_config_5718_, v_inst_5719_, v_R_5720_, v_a_5721_, v_b_5722_, v_c_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_);
lean_dec(v___y_5735_);
lean_dec_ref(v___y_5734_);
lean_dec(v___y_5733_);
lean_dec_ref(v___y_5732_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v___y_5725_);
lean_dec(v___y_5724_);
lean_dec_ref(v___x_5716_);
lean_dec(v_upperBound_5715_);
return v_res_5737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_5738_, lean_object* v_config_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_){
_start:
{
lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; 
v___x_5752_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg___closed__1);
v___x_5753_ = lean_st_mk_ref(v___x_5752_);
v___x_5754_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_5738_, v_config_5739_, v___x_5753_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_);
if (lean_obj_tag(v___x_5754_) == 0)
{
lean_object* v_a_5755_; lean_object* v___x_5757_; uint8_t v_isShared_5758_; uint8_t v_isSharedCheck_5763_; 
v_a_5755_ = lean_ctor_get(v___x_5754_, 0);
v_isSharedCheck_5763_ = !lean_is_exclusive(v___x_5754_);
if (v_isSharedCheck_5763_ == 0)
{
v___x_5757_ = v___x_5754_;
v_isShared_5758_ = v_isSharedCheck_5763_;
goto v_resetjp_5756_;
}
else
{
lean_inc(v_a_5755_);
lean_dec(v___x_5754_);
v___x_5757_ = lean_box(0);
v_isShared_5758_ = v_isSharedCheck_5763_;
goto v_resetjp_5756_;
}
v_resetjp_5756_:
{
lean_object* v___x_5759_; lean_object* v___x_5761_; 
v___x_5759_ = lean_st_ref_get(v___x_5753_);
lean_dec(v___x_5753_);
lean_dec(v___x_5759_);
if (v_isShared_5758_ == 0)
{
v___x_5761_ = v___x_5757_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v_a_5755_);
v___x_5761_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
return v___x_5761_;
}
}
}
else
{
lean_dec(v___x_5753_);
return v___x_5754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_5764_, lean_object* v_config_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_){
_start:
{
lean_object* v_res_5778_; 
v_res_5778_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_5764_, v_config_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_);
lean_dec(v_a_5776_);
lean_dec_ref(v_a_5775_);
lean_dec(v_a_5774_);
lean_dec_ref(v_a_5773_);
lean_dec(v_a_5772_);
lean_dec_ref(v_a_5771_);
lean_dec(v_a_5770_);
lean_dec_ref(v_a_5769_);
lean_dec(v_a_5768_);
lean_dec(v_a_5767_);
lean_dec_ref(v_a_5766_);
return v_res_5778_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; 
v___x_5780_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5781_ = l_Lean_stringToMessageData(v___x_5780_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5782_, lean_object* v_x_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_){
_start:
{
lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; 
v___x_5796_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5797_ = l_Lean_MessageData_ofName(v_name_5782_);
v___x_5798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5798_, 0, v___x_5796_);
lean_ctor_set(v___x_5798_, 1, v___x_5797_);
v___x_5799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5799_, 0, v___x_5798_);
return v___x_5799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5800_, lean_object* v_x_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5800_, v_x_5801_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_);
lean_dec(v___y_5812_);
lean_dec_ref(v___y_5811_);
lean_dec(v___y_5810_);
lean_dec_ref(v___y_5809_);
lean_dec(v___y_5808_);
lean_dec_ref(v___y_5807_);
lean_dec(v___y_5806_);
lean_dec_ref(v___y_5805_);
lean_dec(v___y_5804_);
lean_dec(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec_ref(v_x_5801_);
return v_res_5814_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5815_; 
v___x_5815_ = l_instMonadExceptOfEIO___redArg();
return v___x_5815_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5816_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5817_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5816_);
return v___x_5817_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; 
v___x_5818_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5819_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5818_);
return v___x_5819_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5821_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5820_);
return v___x_5821_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5823_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5822_);
return v___x_5823_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5824_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5825_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5824_);
return v___x_5825_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5826_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5827_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5826_);
return v___x_5827_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5828_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5829_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5828_);
return v___x_5829_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; 
v___x_5830_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5831_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5830_);
return v___x_5831_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5833_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5832_);
return v___x_5833_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; 
v___x_5834_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5835_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5834_);
return v___x_5835_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5836_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5837_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5836_);
return v___x_5837_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5839_; double v___x_5840_; 
v___x_5839_ = lean_unsigned_to_nat(1000000000u);
v___x_5840_ = lean_float_of_nat(v___x_5839_);
return v___x_5840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_){
_start:
{
lean_object* v___x_5854_; lean_object* v_toApplicative_5855_; lean_object* v_toFunctor_5856_; lean_object* v_toSeq_5857_; lean_object* v_toSeqLeft_5858_; lean_object* v_toSeqRight_5859_; lean_object* v___f_5860_; lean_object* v___f_5861_; lean_object* v___f_5862_; lean_object* v___f_5863_; lean_object* v___x_5864_; lean_object* v___f_5865_; lean_object* v___f_5866_; lean_object* v___f_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v_toApplicative_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_6014_; 
v___x_5854_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__3);
v_toApplicative_5855_ = lean_ctor_get(v___x_5854_, 0);
v_toFunctor_5856_ = lean_ctor_get(v_toApplicative_5855_, 0);
v_toSeq_5857_ = lean_ctor_get(v_toApplicative_5855_, 2);
v_toSeqLeft_5858_ = lean_ctor_get(v_toApplicative_5855_, 3);
v_toSeqRight_5859_ = lean_ctor_get(v_toApplicative_5855_, 4);
v___f_5860_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__4));
v___f_5861_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__5));
lean_inc_ref_n(v_toFunctor_5856_, 2);
v___f_5862_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5862_, 0, v_toFunctor_5856_);
v___f_5863_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5863_, 0, v_toFunctor_5856_);
v___x_5864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5864_, 0, v___f_5862_);
lean_ctor_set(v___x_5864_, 1, v___f_5863_);
lean_inc(v_toSeqRight_5859_);
v___f_5865_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5865_, 0, v_toSeqRight_5859_);
lean_inc(v_toSeqLeft_5858_);
v___f_5866_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5866_, 0, v_toSeqLeft_5858_);
lean_inc(v_toSeq_5857_);
v___f_5867_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5867_, 0, v_toSeq_5857_);
v___x_5868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5864_);
lean_ctor_set(v___x_5868_, 1, v___f_5860_);
lean_ctor_set(v___x_5868_, 2, v___f_5867_);
lean_ctor_set(v___x_5868_, 3, v___f_5866_);
lean_ctor_set(v___x_5868_, 4, v___f_5865_);
v___x_5869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5869_, 0, v___x_5868_);
lean_ctor_set(v___x_5869_, 1, v___f_5861_);
v___x_5870_ = l_StateRefT_x27_instMonad___redArg(v___x_5869_);
v_toApplicative_5871_ = lean_ctor_get(v___x_5870_, 0);
v_isSharedCheck_6014_ = !lean_is_exclusive(v___x_5870_);
if (v_isSharedCheck_6014_ == 0)
{
lean_object* v_unused_6015_; 
v_unused_6015_ = lean_ctor_get(v___x_5870_, 1);
lean_dec(v_unused_6015_);
v___x_5873_ = v___x_5870_;
v_isShared_5874_ = v_isSharedCheck_6014_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_toApplicative_5871_);
lean_dec(v___x_5870_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_6014_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v_toFunctor_5875_; lean_object* v_toSeq_5876_; lean_object* v_toSeqLeft_5877_; lean_object* v_toSeqRight_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_6012_; 
v_toFunctor_5875_ = lean_ctor_get(v_toApplicative_5871_, 0);
v_toSeq_5876_ = lean_ctor_get(v_toApplicative_5871_, 2);
v_toSeqLeft_5877_ = lean_ctor_get(v_toApplicative_5871_, 3);
v_toSeqRight_5878_ = lean_ctor_get(v_toApplicative_5871_, 4);
v_isSharedCheck_6012_ = !lean_is_exclusive(v_toApplicative_5871_);
if (v_isSharedCheck_6012_ == 0)
{
lean_object* v_unused_6013_; 
v_unused_6013_ = lean_ctor_get(v_toApplicative_5871_, 1);
lean_dec(v_unused_6013_);
v___x_5880_ = v_toApplicative_5871_;
v_isShared_5881_ = v_isSharedCheck_6012_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_toSeqRight_5878_);
lean_inc(v_toSeqLeft_5877_);
lean_inc(v_toSeq_5876_);
lean_inc(v_toFunctor_5875_);
lean_dec(v_toApplicative_5871_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_6012_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
lean_object* v___f_5882_; lean_object* v___f_5883_; lean_object* v___f_5884_; lean_object* v___f_5885_; lean_object* v___x_5886_; lean_object* v___f_5887_; lean_object* v___f_5888_; lean_object* v___f_5889_; lean_object* v___x_5891_; 
v___f_5882_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__6));
v___f_5883_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_withGrindGoal___redArg___closed__7));
lean_inc_ref(v_toFunctor_5875_);
v___f_5884_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5884_, 0, v_toFunctor_5875_);
v___f_5885_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5885_, 0, v_toFunctor_5875_);
v___x_5886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5886_, 0, v___f_5884_);
lean_ctor_set(v___x_5886_, 1, v___f_5885_);
v___f_5887_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5887_, 0, v_toSeqRight_5878_);
v___f_5888_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5888_, 0, v_toSeqLeft_5877_);
v___f_5889_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5889_, 0, v_toSeq_5876_);
if (v_isShared_5881_ == 0)
{
lean_ctor_set(v___x_5880_, 4, v___f_5887_);
lean_ctor_set(v___x_5880_, 3, v___f_5888_);
lean_ctor_set(v___x_5880_, 2, v___f_5889_);
lean_ctor_set(v___x_5880_, 1, v___f_5882_);
lean_ctor_set(v___x_5880_, 0, v___x_5886_);
v___x_5891_ = v___x_5880_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v___x_5886_);
lean_ctor_set(v_reuseFailAlloc_6011_, 1, v___f_5882_);
lean_ctor_set(v_reuseFailAlloc_6011_, 2, v___f_5889_);
lean_ctor_set(v_reuseFailAlloc_6011_, 3, v___f_5888_);
lean_ctor_set(v_reuseFailAlloc_6011_, 4, v___f_5887_);
v___x_5891_ = v_reuseFailAlloc_6011_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
lean_object* v___x_5893_; 
if (v_isShared_5874_ == 0)
{
lean_ctor_set(v___x_5873_, 1, v___f_5883_);
lean_ctor_set(v___x_5873_, 0, v___x_5891_);
v___x_5893_ = v___x_5873_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v___x_5891_);
lean_ctor_set(v_reuseFailAlloc_6010_, 1, v___f_5883_);
v___x_5893_ = v_reuseFailAlloc_6010_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v_toMonadRef_5903_; lean_object* v___x_5904_; lean_object* v_name_5905_; lean_object* v_run_x27_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_6009_; 
v___x_5894_ = l_StateRefT_x27_instMonad___redArg(v___x_5893_);
v___x_5895_ = l_ReaderT_instMonad___redArg(v___x_5894_);
v___x_5896_ = l_StateRefT_x27_instMonad___redArg(v___x_5895_);
v___x_5897_ = l_ReaderT_instMonad___redArg(v___x_5896_);
v___x_5898_ = l_ReaderT_instMonad___redArg(v___x_5897_);
v___x_5899_ = l_StateRefT_x27_instMonad___redArg(v___x_5898_);
v___x_5900_ = l_ReaderT_instMonad___redArg(v___x_5899_);
v___x_5901_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___x_5902_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21);
v_toMonadRef_5903_ = lean_ctor_get(v___x_5902_, 0);
v___x_5904_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_name_5905_ = lean_ctor_get(v_pass_5841_, 0);
v_run_x27_5906_ = lean_ctor_get(v_pass_5841_, 1);
v_isSharedCheck_6009_ = !lean_is_exclusive(v_pass_5841_);
if (v_isSharedCheck_6009_ == 0)
{
v___x_5908_ = v_pass_5841_;
v_isShared_5909_ = v_isSharedCheck_6009_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_run_x27_5906_);
lean_inc(v_name_5905_);
lean_dec(v_pass_5841_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_6009_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
lean_object* v___x_5910_; lean_object* v_toCold_5911_; lean_object* v_options_5912_; uint8_t v_hasTrace_5913_; 
v___x_5910_ = l_Lean_KVMap_instValueBool;
v_toCold_5911_ = lean_ctor_get(v_a_5851_, 0);
v_options_5912_ = lean_ctor_get(v_toCold_5911_, 2);
v_hasTrace_5913_ = lean_ctor_get_uint8(v_options_5912_, sizeof(void*)*1);
if (v_hasTrace_5913_ == 0)
{
lean_object* v___x_5914_; 
lean_del_object(v___x_5908_);
lean_dec(v_name_5905_);
lean_dec_ref(v___x_5900_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc(v_a_5843_);
lean_inc_ref(v_a_5842_);
v___x_5914_ = lean_apply_12(v_run_x27_5906_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, lean_box(0));
return v___x_5914_;
}
else
{
lean_object* v_inheritedTraceOptions_5915_; lean_object* v___f_5916_; lean_object* v___f_5917_; lean_object* v___f_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; uint8_t v___x_5922_; lean_object* v___y_5924_; lean_object* v___y_5925_; lean_object* v_a_5926_; lean_object* v___y_5942_; lean_object* v___y_5943_; lean_object* v_a_5944_; 
v_inheritedTraceOptions_5915_ = lean_ctor_get(v_toCold_5911_, 11);
v___f_5916_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5916_, 0, v_name_5905_);
v___f_5917_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_5918_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5919_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_5920_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5921_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_5922_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5915_, v_options_5912_, v___x_5921_);
if (v___x_5922_ == 0)
{
lean_object* v___x_6005_; lean_object* v___x_6006_; uint8_t v___x_6007_; 
v___x_6005_ = l_Lean_trace_profiler;
v___x_6006_ = l_Lean_Option_get___redArg(v___x_5910_, v_options_5912_, v___x_6005_);
v___x_6007_ = lean_unbox(v___x_6006_);
lean_dec(v___x_6006_);
if (v___x_6007_ == 0)
{
lean_object* v___x_6008_; 
lean_dec_ref(v___f_5916_);
lean_del_object(v___x_5908_);
lean_dec_ref(v___x_5900_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc(v_a_5843_);
lean_inc_ref(v_a_5842_);
v___x_6008_ = lean_apply_12(v_run_x27_5906_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, lean_box(0));
return v___x_6008_;
}
else
{
goto v___jp_5954_;
}
}
else
{
goto v___jp_5954_;
}
v___jp_5923_:
{
lean_object* v___x_5927_; double v___x_5928_; double v___x_5929_; double v___x_5930_; double v___x_5931_; double v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5936_; 
v___x_5927_ = lean_io_mono_nanos_now();
v___x_5928_ = lean_float_of_nat(v___y_5924_);
v___x_5929_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5930_ = lean_float_div(v___x_5928_, v___x_5929_);
v___x_5931_ = lean_float_of_nat(v___x_5927_);
v___x_5932_ = lean_float_div(v___x_5931_, v___x_5929_);
v___x_5933_ = lean_box_float(v___x_5930_);
v___x_5934_ = lean_box_float(v___x_5932_);
if (v_isShared_5909_ == 0)
{
lean_ctor_set(v___x_5908_, 1, v___x_5934_);
lean_ctor_set(v___x_5908_, 0, v___x_5933_);
v___x_5936_ = v___x_5908_;
goto v_reusejp_5935_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v___x_5933_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v___x_5934_);
v___x_5936_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5935_;
}
v_reusejp_5935_:
{
lean_object* v___x_5937_; lean_object* v___x_28875__overap_5938_; lean_object* v___x_5939_; 
v___x_5937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5937_, 0, v_a_5926_);
lean_ctor_set(v___x_5937_, 1, v___x_5936_);
lean_inc_ref(v_toMonadRef_5903_);
v___x_28875__overap_5938_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5900_, v___x_5901_, v_toMonadRef_5903_, v___f_5917_, lean_box(0), v___x_5904_, v___f_5918_, v___x_5919_, v_hasTrace_5913_, v___x_5920_, v_options_5912_, v___x_5922_, v___y_5925_, v___f_5916_, v___x_5937_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc(v_a_5843_);
lean_inc_ref(v_a_5842_);
v___x_5939_ = lean_apply_12(v___x_28875__overap_5938_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, lean_box(0));
return v___x_5939_;
}
}
v___jp_5941_:
{
lean_object* v___x_5945_; double v___x_5946_; double v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_28896__overap_5952_; lean_object* v___x_5953_; 
v___x_5945_ = lean_io_get_num_heartbeats();
v___x_5946_ = lean_float_of_nat(v___y_5942_);
v___x_5947_ = lean_float_of_nat(v___x_5945_);
v___x_5948_ = lean_box_float(v___x_5946_);
v___x_5949_ = lean_box_float(v___x_5947_);
v___x_5950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5948_);
lean_ctor_set(v___x_5950_, 1, v___x_5949_);
v___x_5951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5951_, 0, v_a_5944_);
lean_ctor_set(v___x_5951_, 1, v___x_5950_);
lean_inc_ref(v_toMonadRef_5903_);
v___x_28896__overap_5952_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5900_, v___x_5901_, v_toMonadRef_5903_, v___f_5917_, lean_box(0), v___x_5904_, v___f_5918_, v___x_5919_, v_hasTrace_5913_, v___x_5920_, v_options_5912_, v___x_5922_, v___y_5943_, v___f_5916_, v___x_5951_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc(v_a_5843_);
lean_inc_ref(v_a_5842_);
v___x_5953_ = lean_apply_12(v___x_28896__overap_5952_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, lean_box(0));
return v___x_5953_;
}
v___jp_5954_:
{
lean_object* v___x_28853__overap_5955_; lean_object* v___x_5956_; 
lean_inc_ref(v___x_5900_);
v___x_28853__overap_5955_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5900_, v___x_5901_);
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc(v_a_5843_);
lean_inc_ref(v_a_5842_);
v___x_5956_ = lean_apply_12(v___x_28853__overap_5955_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, lean_box(0));
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v_a_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; uint8_t v___x_5960_; 
v_a_5957_ = lean_ctor_get(v___x_5956_, 0);
lean_inc(v_a_5957_);
lean_dec_ref_known(v___x_5956_, 1);
v___x_5958_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5959_ = l_Lean_Option_get___redArg(v___x_5910_, v_options_5912_, v___x_5958_);
v___x_5960_ = lean_unbox(v___x_5959_);
lean_dec(v___x_5959_);
if (v___x_5960_ == 0)
{
lean_object* v___x_5961_; lean_object* v___x_5962_; 
v___x_5961_ = lean_io_mono_nanos_now();
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc(v_a_5843_);
lean_inc_ref(v_a_5842_);
v___x_5962_ = lean_apply_12(v_run_x27_5906_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, lean_box(0));
if (lean_obj_tag(v___x_5962_) == 0)
{
lean_object* v_a_5963_; lean_object* v___x_5965_; uint8_t v_isShared_5966_; uint8_t v_isSharedCheck_5970_; 
v_a_5963_ = lean_ctor_get(v___x_5962_, 0);
v_isSharedCheck_5970_ = !lean_is_exclusive(v___x_5962_);
if (v_isSharedCheck_5970_ == 0)
{
v___x_5965_ = v___x_5962_;
v_isShared_5966_ = v_isSharedCheck_5970_;
goto v_resetjp_5964_;
}
else
{
lean_inc(v_a_5963_);
lean_dec(v___x_5962_);
v___x_5965_ = lean_box(0);
v_isShared_5966_ = v_isSharedCheck_5970_;
goto v_resetjp_5964_;
}
v_resetjp_5964_:
{
lean_object* v___x_5968_; 
if (v_isShared_5966_ == 0)
{
lean_ctor_set_tag(v___x_5965_, 1);
v___x_5968_ = v___x_5965_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5963_);
v___x_5968_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
v___y_5924_ = v___x_5961_;
v___y_5925_ = v_a_5957_;
v_a_5926_ = v___x_5968_;
goto v___jp_5923_;
}
}
}
else
{
lean_object* v_a_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5978_; 
v_a_5971_ = lean_ctor_get(v___x_5962_, 0);
v_isSharedCheck_5978_ = !lean_is_exclusive(v___x_5962_);
if (v_isSharedCheck_5978_ == 0)
{
v___x_5973_ = v___x_5962_;
v_isShared_5974_ = v_isSharedCheck_5978_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_a_5971_);
lean_dec(v___x_5962_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5978_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5976_; 
if (v_isShared_5974_ == 0)
{
lean_ctor_set_tag(v___x_5973_, 0);
v___x_5976_ = v___x_5973_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_a_5971_);
v___x_5976_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
v___y_5924_ = v___x_5961_;
v___y_5925_ = v_a_5957_;
v_a_5926_ = v___x_5976_;
goto v___jp_5923_;
}
}
}
}
else
{
lean_object* v___x_5979_; lean_object* v___x_5980_; 
lean_del_object(v___x_5908_);
v___x_5979_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5852_);
lean_inc_ref(v_a_5851_);
lean_inc(v_a_5850_);
lean_inc_ref(v_a_5849_);
lean_inc(v_a_5848_);
lean_inc_ref(v_a_5847_);
lean_inc(v_a_5846_);
lean_inc_ref(v_a_5845_);
lean_inc(v_a_5844_);
lean_inc(v_a_5843_);
lean_inc_ref(v_a_5842_);
v___x_5980_ = lean_apply_12(v_run_x27_5906_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, lean_box(0));
if (lean_obj_tag(v___x_5980_) == 0)
{
lean_object* v_a_5981_; lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_5988_; 
v_a_5981_ = lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_5988_ = !lean_is_exclusive(v___x_5980_);
if (v_isSharedCheck_5988_ == 0)
{
v___x_5983_ = v___x_5980_;
v_isShared_5984_ = v_isSharedCheck_5988_;
goto v_resetjp_5982_;
}
else
{
lean_inc(v_a_5981_);
lean_dec(v___x_5980_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_5988_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
lean_object* v___x_5986_; 
if (v_isShared_5984_ == 0)
{
lean_ctor_set_tag(v___x_5983_, 1);
v___x_5986_ = v___x_5983_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_a_5981_);
v___x_5986_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
v___y_5942_ = v___x_5979_;
v___y_5943_ = v_a_5957_;
v_a_5944_ = v___x_5986_;
goto v___jp_5941_;
}
}
}
else
{
lean_object* v_a_5989_; lean_object* v___x_5991_; uint8_t v_isShared_5992_; uint8_t v_isSharedCheck_5996_; 
v_a_5989_ = lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_5996_ = !lean_is_exclusive(v___x_5980_);
if (v_isSharedCheck_5996_ == 0)
{
v___x_5991_ = v___x_5980_;
v_isShared_5992_ = v_isSharedCheck_5996_;
goto v_resetjp_5990_;
}
else
{
lean_inc(v_a_5989_);
lean_dec(v___x_5980_);
v___x_5991_ = lean_box(0);
v_isShared_5992_ = v_isSharedCheck_5996_;
goto v_resetjp_5990_;
}
v_resetjp_5990_:
{
lean_object* v___x_5994_; 
if (v_isShared_5992_ == 0)
{
lean_ctor_set_tag(v___x_5991_, 0);
v___x_5994_ = v___x_5991_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v_a_5989_);
v___x_5994_ = v_reuseFailAlloc_5995_;
goto v_reusejp_5993_;
}
v_reusejp_5993_:
{
v___y_5942_ = v___x_5979_;
v___y_5943_ = v_a_5957_;
v_a_5944_ = v___x_5994_;
goto v___jp_5941_;
}
}
}
}
}
else
{
lean_object* v_a_5997_; lean_object* v___x_5999_; uint8_t v_isShared_6000_; uint8_t v_isSharedCheck_6004_; 
lean_dec_ref(v___f_5916_);
lean_del_object(v___x_5908_);
lean_dec_ref(v_run_x27_5906_);
lean_dec_ref(v___x_5900_);
v_a_5997_ = lean_ctor_get(v___x_5956_, 0);
v_isSharedCheck_6004_ = !lean_is_exclusive(v___x_5956_);
if (v_isSharedCheck_6004_ == 0)
{
v___x_5999_ = v___x_5956_;
v_isShared_6000_ = v_isSharedCheck_6004_;
goto v_resetjp_5998_;
}
else
{
lean_inc(v_a_5997_);
lean_dec(v___x_5956_);
v___x_5999_ = lean_box(0);
v_isShared_6000_ = v_isSharedCheck_6004_;
goto v_resetjp_5998_;
}
v_resetjp_5998_:
{
lean_object* v___x_6002_; 
if (v_isShared_6000_ == 0)
{
v___x_6002_ = v___x_5999_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v_a_5997_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
return v___x_6002_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_){
_start:
{
lean_object* v_res_6029_; 
v_res_6029_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_, v_a_6027_);
lean_dec(v_a_6027_);
lean_dec_ref(v_a_6026_);
lean_dec(v_a_6025_);
lean_dec_ref(v_a_6024_);
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec_ref(v_a_6020_);
lean_dec(v_a_6019_);
lean_dec(v_a_6018_);
lean_dec_ref(v_a_6017_);
return v_res_6029_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; 
v___x_6030_ = lean_unsigned_to_nat(32u);
v___x_6031_ = lean_mk_empty_array_with_capacity(v___x_6030_);
v___x_6032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6031_);
return v___x_6032_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; 
v___x_6033_ = ((size_t)5ULL);
v___x_6034_ = lean_unsigned_to_nat(0u);
v___x_6035_ = lean_unsigned_to_nat(32u);
v___x_6036_ = lean_mk_empty_array_with_capacity(v___x_6035_);
v___x_6037_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_6038_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
lean_ctor_set(v___x_6038_, 1, v___x_6036_);
lean_ctor_set(v___x_6038_, 2, v___x_6034_);
lean_ctor_set(v___x_6038_, 3, v___x_6034_);
lean_ctor_set_usize(v___x_6038_, 4, v___x_6033_);
return v___x_6038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_6039_){
_start:
{
lean_object* v___x_6041_; lean_object* v_traceState_6042_; lean_object* v_traces_6043_; lean_object* v___x_6044_; lean_object* v_traceState_6045_; lean_object* v_env_6046_; lean_object* v_nextMacroScope_6047_; lean_object* v_ngen_6048_; lean_object* v_auxDeclNGen_6049_; lean_object* v_cache_6050_; lean_object* v_recordedDeps_6051_; lean_object* v_messages_6052_; lean_object* v_infoState_6053_; lean_object* v_snapshotTasks_6054_; lean_object* v___x_6056_; uint8_t v_isShared_6057_; uint8_t v_isSharedCheck_6073_; 
v___x_6041_ = lean_st_ref_get(v___y_6039_);
v_traceState_6042_ = lean_ctor_get(v___x_6041_, 4);
lean_inc_ref(v_traceState_6042_);
lean_dec(v___x_6041_);
v_traces_6043_ = lean_ctor_get(v_traceState_6042_, 0);
lean_inc_ref(v_traces_6043_);
lean_dec_ref(v_traceState_6042_);
v___x_6044_ = lean_st_ref_take(v___y_6039_);
v_traceState_6045_ = lean_ctor_get(v___x_6044_, 4);
v_env_6046_ = lean_ctor_get(v___x_6044_, 0);
v_nextMacroScope_6047_ = lean_ctor_get(v___x_6044_, 1);
v_ngen_6048_ = lean_ctor_get(v___x_6044_, 2);
v_auxDeclNGen_6049_ = lean_ctor_get(v___x_6044_, 3);
v_cache_6050_ = lean_ctor_get(v___x_6044_, 5);
v_recordedDeps_6051_ = lean_ctor_get(v___x_6044_, 6);
v_messages_6052_ = lean_ctor_get(v___x_6044_, 7);
v_infoState_6053_ = lean_ctor_get(v___x_6044_, 8);
v_snapshotTasks_6054_ = lean_ctor_get(v___x_6044_, 9);
v_isSharedCheck_6073_ = !lean_is_exclusive(v___x_6044_);
if (v_isSharedCheck_6073_ == 0)
{
v___x_6056_ = v___x_6044_;
v_isShared_6057_ = v_isSharedCheck_6073_;
goto v_resetjp_6055_;
}
else
{
lean_inc(v_snapshotTasks_6054_);
lean_inc(v_infoState_6053_);
lean_inc(v_messages_6052_);
lean_inc(v_recordedDeps_6051_);
lean_inc(v_cache_6050_);
lean_inc(v_traceState_6045_);
lean_inc(v_auxDeclNGen_6049_);
lean_inc(v_ngen_6048_);
lean_inc(v_nextMacroScope_6047_);
lean_inc(v_env_6046_);
lean_dec(v___x_6044_);
v___x_6056_ = lean_box(0);
v_isShared_6057_ = v_isSharedCheck_6073_;
goto v_resetjp_6055_;
}
v_resetjp_6055_:
{
uint64_t v_tid_6058_; lean_object* v___x_6060_; uint8_t v_isShared_6061_; uint8_t v_isSharedCheck_6071_; 
v_tid_6058_ = lean_ctor_get_uint64(v_traceState_6045_, sizeof(void*)*1);
v_isSharedCheck_6071_ = !lean_is_exclusive(v_traceState_6045_);
if (v_isSharedCheck_6071_ == 0)
{
lean_object* v_unused_6072_; 
v_unused_6072_ = lean_ctor_get(v_traceState_6045_, 0);
lean_dec(v_unused_6072_);
v___x_6060_ = v_traceState_6045_;
v_isShared_6061_ = v_isSharedCheck_6071_;
goto v_resetjp_6059_;
}
else
{
lean_dec(v_traceState_6045_);
v___x_6060_ = lean_box(0);
v_isShared_6061_ = v_isSharedCheck_6071_;
goto v_resetjp_6059_;
}
v_resetjp_6059_:
{
lean_object* v___x_6062_; lean_object* v___x_6064_; 
v___x_6062_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_6061_ == 0)
{
lean_ctor_set(v___x_6060_, 0, v___x_6062_);
v___x_6064_ = v___x_6060_;
goto v_reusejp_6063_;
}
else
{
lean_object* v_reuseFailAlloc_6070_; 
v_reuseFailAlloc_6070_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6070_, 0, v___x_6062_);
lean_ctor_set_uint64(v_reuseFailAlloc_6070_, sizeof(void*)*1, v_tid_6058_);
v___x_6064_ = v_reuseFailAlloc_6070_;
goto v_reusejp_6063_;
}
v_reusejp_6063_:
{
lean_object* v___x_6066_; 
if (v_isShared_6057_ == 0)
{
lean_ctor_set(v___x_6056_, 4, v___x_6064_);
v___x_6066_ = v___x_6056_;
goto v_reusejp_6065_;
}
else
{
lean_object* v_reuseFailAlloc_6069_; 
v_reuseFailAlloc_6069_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6069_, 0, v_env_6046_);
lean_ctor_set(v_reuseFailAlloc_6069_, 1, v_nextMacroScope_6047_);
lean_ctor_set(v_reuseFailAlloc_6069_, 2, v_ngen_6048_);
lean_ctor_set(v_reuseFailAlloc_6069_, 3, v_auxDeclNGen_6049_);
lean_ctor_set(v_reuseFailAlloc_6069_, 4, v___x_6064_);
lean_ctor_set(v_reuseFailAlloc_6069_, 5, v_cache_6050_);
lean_ctor_set(v_reuseFailAlloc_6069_, 6, v_recordedDeps_6051_);
lean_ctor_set(v_reuseFailAlloc_6069_, 7, v_messages_6052_);
lean_ctor_set(v_reuseFailAlloc_6069_, 8, v_infoState_6053_);
lean_ctor_set(v_reuseFailAlloc_6069_, 9, v_snapshotTasks_6054_);
v___x_6066_ = v_reuseFailAlloc_6069_;
goto v_reusejp_6065_;
}
v_reusejp_6065_:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; 
v___x_6067_ = lean_st_ref_put(v___y_6039_, v___x_6066_);
v___x_6068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6068_, 0, v_traces_6043_);
return v___x_6068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_6074_, lean_object* v___y_6075_){
_start:
{
lean_object* v_res_6076_; 
v_res_6076_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6074_);
lean_dec(v___y_6074_);
return v_res_6076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_){
_start:
{
lean_object* v___x_6089_; 
v___x_6089_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6087_);
return v___x_6089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_){
_start:
{
lean_object* v_res_6102_; 
v_res_6102_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_);
lean_dec(v___y_6100_);
lean_dec_ref(v___y_6099_);
lean_dec(v___y_6098_);
lean_dec_ref(v___y_6097_);
lean_dec(v___y_6096_);
lean_dec_ref(v___y_6095_);
lean_dec(v___y_6094_);
lean_dec_ref(v___y_6093_);
lean_dec(v___y_6092_);
lean_dec(v___y_6091_);
lean_dec_ref(v___y_6090_);
return v_res_6102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_6103_, lean_object* v_opt_6104_){
_start:
{
lean_object* v_name_6105_; lean_object* v_defValue_6106_; lean_object* v_map_6107_; lean_object* v___x_6108_; 
v_name_6105_ = lean_ctor_get(v_opt_6104_, 0);
v_defValue_6106_ = lean_ctor_get(v_opt_6104_, 1);
v_map_6107_ = lean_ctor_get(v_opts_6103_, 0);
v___x_6108_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6107_, v_name_6105_);
if (lean_obj_tag(v___x_6108_) == 0)
{
uint8_t v___x_6109_; 
v___x_6109_ = lean_unbox(v_defValue_6106_);
return v___x_6109_;
}
else
{
lean_object* v_val_6110_; 
v_val_6110_ = lean_ctor_get(v___x_6108_, 0);
lean_inc(v_val_6110_);
lean_dec_ref_known(v___x_6108_, 1);
if (lean_obj_tag(v_val_6110_) == 1)
{
uint8_t v_v_6111_; 
v_v_6111_ = lean_ctor_get_uint8(v_val_6110_, 0);
lean_dec_ref_known(v_val_6110_, 0);
return v_v_6111_;
}
else
{
uint8_t v___x_6112_; 
lean_dec(v_val_6110_);
v___x_6112_ = lean_unbox(v_defValue_6106_);
return v___x_6112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_6113_, lean_object* v_opt_6114_){
_start:
{
uint8_t v_res_6115_; lean_object* v_r_6116_; 
v_res_6115_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6113_, v_opt_6114_);
lean_dec_ref(v_opt_6114_);
lean_dec_ref(v_opts_6113_);
v_r_6116_ = lean_box(v_res_6115_);
return v_r_6116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_6117_, lean_object* v_msg_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_){
_start:
{
lean_object* v_ref_6124_; lean_object* v___x_6125_; lean_object* v_a_6126_; lean_object* v___x_6128_; uint8_t v_isShared_6129_; uint8_t v_isSharedCheck_6171_; 
v_ref_6124_ = lean_ctor_get(v___y_6121_, 2);
v___x_6125_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
v_a_6126_ = lean_ctor_get(v___x_6125_, 0);
v_isSharedCheck_6171_ = !lean_is_exclusive(v___x_6125_);
if (v_isSharedCheck_6171_ == 0)
{
v___x_6128_ = v___x_6125_;
v_isShared_6129_ = v_isSharedCheck_6171_;
goto v_resetjp_6127_;
}
else
{
lean_inc(v_a_6126_);
lean_dec(v___x_6125_);
v___x_6128_ = lean_box(0);
v_isShared_6129_ = v_isSharedCheck_6171_;
goto v_resetjp_6127_;
}
v_resetjp_6127_:
{
lean_object* v___x_6130_; lean_object* v_traceState_6131_; lean_object* v_env_6132_; lean_object* v_nextMacroScope_6133_; lean_object* v_ngen_6134_; lean_object* v_auxDeclNGen_6135_; lean_object* v_cache_6136_; lean_object* v_recordedDeps_6137_; lean_object* v_messages_6138_; lean_object* v_infoState_6139_; lean_object* v_snapshotTasks_6140_; lean_object* v___x_6142_; uint8_t v_isShared_6143_; uint8_t v_isSharedCheck_6170_; 
v___x_6130_ = lean_st_ref_take(v___y_6122_);
v_traceState_6131_ = lean_ctor_get(v___x_6130_, 4);
v_env_6132_ = lean_ctor_get(v___x_6130_, 0);
v_nextMacroScope_6133_ = lean_ctor_get(v___x_6130_, 1);
v_ngen_6134_ = lean_ctor_get(v___x_6130_, 2);
v_auxDeclNGen_6135_ = lean_ctor_get(v___x_6130_, 3);
v_cache_6136_ = lean_ctor_get(v___x_6130_, 5);
v_recordedDeps_6137_ = lean_ctor_get(v___x_6130_, 6);
v_messages_6138_ = lean_ctor_get(v___x_6130_, 7);
v_infoState_6139_ = lean_ctor_get(v___x_6130_, 8);
v_snapshotTasks_6140_ = lean_ctor_get(v___x_6130_, 9);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___x_6130_);
if (v_isSharedCheck_6170_ == 0)
{
v___x_6142_ = v___x_6130_;
v_isShared_6143_ = v_isSharedCheck_6170_;
goto v_resetjp_6141_;
}
else
{
lean_inc(v_snapshotTasks_6140_);
lean_inc(v_infoState_6139_);
lean_inc(v_messages_6138_);
lean_inc(v_recordedDeps_6137_);
lean_inc(v_cache_6136_);
lean_inc(v_traceState_6131_);
lean_inc(v_auxDeclNGen_6135_);
lean_inc(v_ngen_6134_);
lean_inc(v_nextMacroScope_6133_);
lean_inc(v_env_6132_);
lean_dec(v___x_6130_);
v___x_6142_ = lean_box(0);
v_isShared_6143_ = v_isSharedCheck_6170_;
goto v_resetjp_6141_;
}
v_resetjp_6141_:
{
uint64_t v_tid_6144_; lean_object* v_traces_6145_; lean_object* v___x_6147_; uint8_t v_isShared_6148_; uint8_t v_isSharedCheck_6169_; 
v_tid_6144_ = lean_ctor_get_uint64(v_traceState_6131_, sizeof(void*)*1);
v_traces_6145_ = lean_ctor_get(v_traceState_6131_, 0);
v_isSharedCheck_6169_ = !lean_is_exclusive(v_traceState_6131_);
if (v_isSharedCheck_6169_ == 0)
{
v___x_6147_ = v_traceState_6131_;
v_isShared_6148_ = v_isSharedCheck_6169_;
goto v_resetjp_6146_;
}
else
{
lean_inc(v_traces_6145_);
lean_dec(v_traceState_6131_);
v___x_6147_ = lean_box(0);
v_isShared_6148_ = v_isSharedCheck_6169_;
goto v_resetjp_6146_;
}
v_resetjp_6146_:
{
lean_object* v___x_6149_; lean_object* v___x_6150_; double v___x_6151_; uint8_t v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6160_; 
v___x_6149_ = lean_box(0);
v___x_6150_ = lean_box(0);
v___x_6151_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_6152_ = 0;
v___x_6153_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6154_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_6154_, 0, v_cls_6117_);
lean_ctor_set(v___x_6154_, 1, v___x_6150_);
lean_ctor_set(v___x_6154_, 2, v___x_6153_);
lean_ctor_set_float(v___x_6154_, sizeof(void*)*3, v___x_6151_);
lean_ctor_set_float(v___x_6154_, sizeof(void*)*3 + 8, v___x_6151_);
lean_ctor_set_uint8(v___x_6154_, sizeof(void*)*3 + 16, v___x_6152_);
v___x_6155_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_6156_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6154_);
lean_ctor_set(v___x_6156_, 1, v_a_6126_);
lean_ctor_set(v___x_6156_, 2, v___x_6155_);
lean_inc(v_ref_6124_);
v___x_6157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6157_, 0, v_ref_6124_);
lean_ctor_set(v___x_6157_, 1, v___x_6156_);
v___x_6158_ = l_Lean_PersistentArray_push___redArg(v_traces_6145_, v___x_6157_);
if (v_isShared_6148_ == 0)
{
lean_ctor_set(v___x_6147_, 0, v___x_6158_);
v___x_6160_ = v___x_6147_;
goto v_reusejp_6159_;
}
else
{
lean_object* v_reuseFailAlloc_6168_; 
v_reuseFailAlloc_6168_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6168_, 0, v___x_6158_);
lean_ctor_set_uint64(v_reuseFailAlloc_6168_, sizeof(void*)*1, v_tid_6144_);
v___x_6160_ = v_reuseFailAlloc_6168_;
goto v_reusejp_6159_;
}
v_reusejp_6159_:
{
lean_object* v___x_6162_; 
if (v_isShared_6143_ == 0)
{
lean_ctor_set(v___x_6142_, 4, v___x_6160_);
v___x_6162_ = v___x_6142_;
goto v_reusejp_6161_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v_env_6132_);
lean_ctor_set(v_reuseFailAlloc_6167_, 1, v_nextMacroScope_6133_);
lean_ctor_set(v_reuseFailAlloc_6167_, 2, v_ngen_6134_);
lean_ctor_set(v_reuseFailAlloc_6167_, 3, v_auxDeclNGen_6135_);
lean_ctor_set(v_reuseFailAlloc_6167_, 4, v___x_6160_);
lean_ctor_set(v_reuseFailAlloc_6167_, 5, v_cache_6136_);
lean_ctor_set(v_reuseFailAlloc_6167_, 6, v_recordedDeps_6137_);
lean_ctor_set(v_reuseFailAlloc_6167_, 7, v_messages_6138_);
lean_ctor_set(v_reuseFailAlloc_6167_, 8, v_infoState_6139_);
lean_ctor_set(v_reuseFailAlloc_6167_, 9, v_snapshotTasks_6140_);
v___x_6162_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6161_;
}
v_reusejp_6161_:
{
lean_object* v___x_6163_; lean_object* v___x_6165_; 
v___x_6163_ = lean_st_ref_put(v___y_6122_, v___x_6162_);
if (v_isShared_6129_ == 0)
{
lean_ctor_set(v___x_6128_, 0, v___x_6149_);
v___x_6165_ = v___x_6128_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v___x_6149_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_6172_, lean_object* v_msg_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_){
_start:
{
lean_object* v_res_6179_; 
v_res_6179_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6172_, v_msg_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
return v_res_6179_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_6180_){
_start:
{
if (lean_obj_tag(v_e_6180_) == 0)
{
uint8_t v___x_6181_; 
v___x_6181_ = 2;
return v___x_6181_;
}
else
{
lean_object* v_a_6182_; uint8_t v___x_6183_; 
v_a_6182_ = lean_ctor_get(v_e_6180_, 0);
v___x_6183_ = lean_unbox(v_a_6182_);
if (v___x_6183_ == 0)
{
uint8_t v___x_6184_; 
v___x_6184_ = 1;
return v___x_6184_;
}
else
{
uint8_t v___x_6185_; 
v___x_6185_ = 0;
return v___x_6185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_6186_){
_start:
{
uint8_t v_res_6187_; lean_object* v_r_6188_; 
v_res_6187_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_6186_);
lean_dec_ref(v_e_6186_);
v_r_6188_ = lean_box(v_res_6187_);
return v_r_6188_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_6189_){
_start:
{
if (lean_obj_tag(v_x_6189_) == 0)
{
lean_object* v_a_6191_; lean_object* v___x_6193_; uint8_t v_isShared_6194_; uint8_t v_isSharedCheck_6198_; 
v_a_6191_ = lean_ctor_get(v_x_6189_, 0);
v_isSharedCheck_6198_ = !lean_is_exclusive(v_x_6189_);
if (v_isSharedCheck_6198_ == 0)
{
v___x_6193_ = v_x_6189_;
v_isShared_6194_ = v_isSharedCheck_6198_;
goto v_resetjp_6192_;
}
else
{
lean_inc(v_a_6191_);
lean_dec(v_x_6189_);
v___x_6193_ = lean_box(0);
v_isShared_6194_ = v_isSharedCheck_6198_;
goto v_resetjp_6192_;
}
v_resetjp_6192_:
{
lean_object* v___x_6196_; 
if (v_isShared_6194_ == 0)
{
lean_ctor_set_tag(v___x_6193_, 1);
v___x_6196_ = v___x_6193_;
goto v_reusejp_6195_;
}
else
{
lean_object* v_reuseFailAlloc_6197_; 
v_reuseFailAlloc_6197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6197_, 0, v_a_6191_);
v___x_6196_ = v_reuseFailAlloc_6197_;
goto v_reusejp_6195_;
}
v_reusejp_6195_:
{
return v___x_6196_;
}
}
}
else
{
lean_object* v_a_6199_; lean_object* v___x_6201_; uint8_t v_isShared_6202_; uint8_t v_isSharedCheck_6206_; 
v_a_6199_ = lean_ctor_get(v_x_6189_, 0);
v_isSharedCheck_6206_ = !lean_is_exclusive(v_x_6189_);
if (v_isSharedCheck_6206_ == 0)
{
v___x_6201_ = v_x_6189_;
v_isShared_6202_ = v_isSharedCheck_6206_;
goto v_resetjp_6200_;
}
else
{
lean_inc(v_a_6199_);
lean_dec(v_x_6189_);
v___x_6201_ = lean_box(0);
v_isShared_6202_ = v_isSharedCheck_6206_;
goto v_resetjp_6200_;
}
v_resetjp_6200_:
{
lean_object* v___x_6204_; 
if (v_isShared_6202_ == 0)
{
lean_ctor_set_tag(v___x_6201_, 0);
v___x_6204_ = v___x_6201_;
goto v_reusejp_6203_;
}
else
{
lean_object* v_reuseFailAlloc_6205_; 
v_reuseFailAlloc_6205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6205_, 0, v_a_6199_);
v___x_6204_ = v_reuseFailAlloc_6205_;
goto v_reusejp_6203_;
}
v_reusejp_6203_:
{
return v___x_6204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_6207_, lean_object* v___y_6208_){
_start:
{
lean_object* v_res_6209_; 
v_res_6209_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6207_);
return v_res_6209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_6210_, lean_object* v_opt_6211_){
_start:
{
lean_object* v_name_6212_; lean_object* v_defValue_6213_; lean_object* v_map_6214_; lean_object* v___x_6215_; 
v_name_6212_ = lean_ctor_get(v_opt_6211_, 0);
v_defValue_6213_ = lean_ctor_get(v_opt_6211_, 1);
v_map_6214_ = lean_ctor_get(v_opts_6210_, 0);
v___x_6215_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6214_, v_name_6212_);
if (lean_obj_tag(v___x_6215_) == 0)
{
lean_inc(v_defValue_6213_);
return v_defValue_6213_;
}
else
{
lean_object* v_val_6216_; 
v_val_6216_ = lean_ctor_get(v___x_6215_, 0);
lean_inc(v_val_6216_);
lean_dec_ref_known(v___x_6215_, 1);
if (lean_obj_tag(v_val_6216_) == 3)
{
lean_object* v_v_6217_; 
v_v_6217_ = lean_ctor_get(v_val_6216_, 0);
lean_inc(v_v_6217_);
lean_dec_ref_known(v_val_6216_, 1);
return v_v_6217_;
}
else
{
lean_dec(v_val_6216_);
lean_inc(v_defValue_6213_);
return v_defValue_6213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_6218_, lean_object* v_opt_6219_){
_start:
{
lean_object* v_res_6220_; 
v_res_6220_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6218_, v_opt_6219_);
lean_dec_ref(v_opt_6219_);
lean_dec_ref(v_opts_6218_);
return v_res_6220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_6221_, size_t v_i_6222_, lean_object* v_bs_6223_){
_start:
{
uint8_t v___x_6224_; 
v___x_6224_ = lean_usize_dec_lt(v_i_6222_, v_sz_6221_);
if (v___x_6224_ == 0)
{
return v_bs_6223_;
}
else
{
lean_object* v_v_6225_; lean_object* v_msg_6226_; lean_object* v___x_6227_; lean_object* v_bs_x27_6228_; size_t v___x_6229_; size_t v___x_6230_; lean_object* v___x_6231_; 
v_v_6225_ = lean_array_uget_borrowed(v_bs_6223_, v_i_6222_);
v_msg_6226_ = lean_ctor_get(v_v_6225_, 1);
lean_inc_ref(v_msg_6226_);
v___x_6227_ = lean_unsigned_to_nat(0u);
v_bs_x27_6228_ = lean_array_uset(v_bs_6223_, v_i_6222_, v___x_6227_);
v___x_6229_ = ((size_t)1ULL);
v___x_6230_ = lean_usize_add(v_i_6222_, v___x_6229_);
v___x_6231_ = lean_array_uset(v_bs_x27_6228_, v_i_6222_, v_msg_6226_);
v_i_6222_ = v___x_6230_;
v_bs_6223_ = v___x_6231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_6233_, lean_object* v_i_6234_, lean_object* v_bs_6235_){
_start:
{
size_t v_sz_boxed_6236_; size_t v_i_boxed_6237_; lean_object* v_res_6238_; 
v_sz_boxed_6236_ = lean_unbox_usize(v_sz_6233_);
lean_dec(v_sz_6233_);
v_i_boxed_6237_ = lean_unbox_usize(v_i_6234_);
lean_dec(v_i_6234_);
v_res_6238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_6236_, v_i_boxed_6237_, v_bs_6235_);
return v_res_6238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_6239_, lean_object* v_data_6240_, lean_object* v_ref_6241_, lean_object* v_msg_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_){
_start:
{
lean_object* v_toCold_6248_; lean_object* v_currRecDepth_6249_; lean_object* v_ref_6250_; uint16_t v_optionFlags_6251_; uint8_t v_suppressElabErrors_6252_; uint8_t v_isRecordingDeps_6253_; lean_object* v_ref_6254_; lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v_traceState_6257_; lean_object* v_traces_6258_; lean_object* v___x_6259_; size_t v_sz_6260_; size_t v___x_6261_; lean_object* v___x_6262_; lean_object* v_msg_6263_; lean_object* v___x_6264_; lean_object* v_a_6265_; lean_object* v___x_6267_; uint8_t v_isShared_6268_; uint8_t v_isSharedCheck_6303_; 
v_toCold_6248_ = lean_ctor_get(v___y_6245_, 0);
v_currRecDepth_6249_ = lean_ctor_get(v___y_6245_, 1);
v_ref_6250_ = lean_ctor_get(v___y_6245_, 2);
v_optionFlags_6251_ = lean_ctor_get_uint16(v___y_6245_, sizeof(void*)*3);
v_suppressElabErrors_6252_ = lean_ctor_get_uint8(v___y_6245_, sizeof(void*)*3 + 2);
v_isRecordingDeps_6253_ = lean_ctor_get_uint8(v___y_6245_, sizeof(void*)*3 + 3);
v_ref_6254_ = l_Lean_replaceRef(v_ref_6241_, v_ref_6250_);
lean_inc(v_currRecDepth_6249_);
lean_inc_ref(v_toCold_6248_);
v___x_6255_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_6255_, 0, v_toCold_6248_);
lean_ctor_set(v___x_6255_, 1, v_currRecDepth_6249_);
lean_ctor_set(v___x_6255_, 2, v_ref_6254_);
lean_ctor_set_uint16(v___x_6255_, sizeof(void*)*3, v_optionFlags_6251_);
lean_ctor_set_uint8(v___x_6255_, sizeof(void*)*3 + 2, v_suppressElabErrors_6252_);
lean_ctor_set_uint8(v___x_6255_, sizeof(void*)*3 + 3, v_isRecordingDeps_6253_);
v___x_6256_ = lean_st_ref_get(v___y_6246_);
v_traceState_6257_ = lean_ctor_get(v___x_6256_, 4);
lean_inc_ref(v_traceState_6257_);
lean_dec(v___x_6256_);
v_traces_6258_ = lean_ctor_get(v_traceState_6257_, 0);
lean_inc_ref(v_traces_6258_);
lean_dec_ref(v_traceState_6257_);
v___x_6259_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6258_);
lean_dec_ref(v_traces_6258_);
v_sz_6260_ = lean_array_size(v___x_6259_);
v___x_6261_ = ((size_t)0ULL);
v___x_6262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_6260_, v___x_6261_, v___x_6259_);
v_msg_6263_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6263_, 0, v_data_6240_);
lean_ctor_set(v_msg_6263_, 1, v_msg_6242_);
lean_ctor_set(v_msg_6263_, 2, v___x_6262_);
v___x_6264_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_6263_, v___y_6243_, v___y_6244_, v___x_6255_, v___y_6246_);
lean_dec_ref_known(v___x_6255_, 3);
v_a_6265_ = lean_ctor_get(v___x_6264_, 0);
v_isSharedCheck_6303_ = !lean_is_exclusive(v___x_6264_);
if (v_isSharedCheck_6303_ == 0)
{
v___x_6267_ = v___x_6264_;
v_isShared_6268_ = v_isSharedCheck_6303_;
goto v_resetjp_6266_;
}
else
{
lean_inc(v_a_6265_);
lean_dec(v___x_6264_);
v___x_6267_ = lean_box(0);
v_isShared_6268_ = v_isSharedCheck_6303_;
goto v_resetjp_6266_;
}
v_resetjp_6266_:
{
lean_object* v___x_6269_; lean_object* v_traceState_6270_; lean_object* v_env_6271_; lean_object* v_nextMacroScope_6272_; lean_object* v_ngen_6273_; lean_object* v_auxDeclNGen_6274_; lean_object* v_cache_6275_; lean_object* v_recordedDeps_6276_; lean_object* v_messages_6277_; lean_object* v_infoState_6278_; lean_object* v_snapshotTasks_6279_; lean_object* v___x_6281_; uint8_t v_isShared_6282_; uint8_t v_isSharedCheck_6302_; 
v___x_6269_ = lean_st_ref_take(v___y_6246_);
v_traceState_6270_ = lean_ctor_get(v___x_6269_, 4);
v_env_6271_ = lean_ctor_get(v___x_6269_, 0);
v_nextMacroScope_6272_ = lean_ctor_get(v___x_6269_, 1);
v_ngen_6273_ = lean_ctor_get(v___x_6269_, 2);
v_auxDeclNGen_6274_ = lean_ctor_get(v___x_6269_, 3);
v_cache_6275_ = lean_ctor_get(v___x_6269_, 5);
v_recordedDeps_6276_ = lean_ctor_get(v___x_6269_, 6);
v_messages_6277_ = lean_ctor_get(v___x_6269_, 7);
v_infoState_6278_ = lean_ctor_get(v___x_6269_, 8);
v_snapshotTasks_6279_ = lean_ctor_get(v___x_6269_, 9);
v_isSharedCheck_6302_ = !lean_is_exclusive(v___x_6269_);
if (v_isSharedCheck_6302_ == 0)
{
v___x_6281_ = v___x_6269_;
v_isShared_6282_ = v_isSharedCheck_6302_;
goto v_resetjp_6280_;
}
else
{
lean_inc(v_snapshotTasks_6279_);
lean_inc(v_infoState_6278_);
lean_inc(v_messages_6277_);
lean_inc(v_recordedDeps_6276_);
lean_inc(v_cache_6275_);
lean_inc(v_traceState_6270_);
lean_inc(v_auxDeclNGen_6274_);
lean_inc(v_ngen_6273_);
lean_inc(v_nextMacroScope_6272_);
lean_inc(v_env_6271_);
lean_dec(v___x_6269_);
v___x_6281_ = lean_box(0);
v_isShared_6282_ = v_isSharedCheck_6302_;
goto v_resetjp_6280_;
}
v_resetjp_6280_:
{
uint64_t v_tid_6283_; lean_object* v___x_6285_; uint8_t v_isShared_6286_; uint8_t v_isSharedCheck_6300_; 
v_tid_6283_ = lean_ctor_get_uint64(v_traceState_6270_, sizeof(void*)*1);
v_isSharedCheck_6300_ = !lean_is_exclusive(v_traceState_6270_);
if (v_isSharedCheck_6300_ == 0)
{
lean_object* v_unused_6301_; 
v_unused_6301_ = lean_ctor_get(v_traceState_6270_, 0);
lean_dec(v_unused_6301_);
v___x_6285_ = v_traceState_6270_;
v_isShared_6286_ = v_isSharedCheck_6300_;
goto v_resetjp_6284_;
}
else
{
lean_dec(v_traceState_6270_);
v___x_6285_ = lean_box(0);
v_isShared_6286_ = v_isSharedCheck_6300_;
goto v_resetjp_6284_;
}
v_resetjp_6284_:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6291_; 
v___x_6287_ = lean_box(0);
v___x_6288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6288_, 0, v_ref_6241_);
lean_ctor_set(v___x_6288_, 1, v_a_6265_);
v___x_6289_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6239_, v___x_6288_);
if (v_isShared_6286_ == 0)
{
lean_ctor_set(v___x_6285_, 0, v___x_6289_);
v___x_6291_ = v___x_6285_;
goto v_reusejp_6290_;
}
else
{
lean_object* v_reuseFailAlloc_6299_; 
v_reuseFailAlloc_6299_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6299_, 0, v___x_6289_);
lean_ctor_set_uint64(v_reuseFailAlloc_6299_, sizeof(void*)*1, v_tid_6283_);
v___x_6291_ = v_reuseFailAlloc_6299_;
goto v_reusejp_6290_;
}
v_reusejp_6290_:
{
lean_object* v___x_6293_; 
if (v_isShared_6282_ == 0)
{
lean_ctor_set(v___x_6281_, 4, v___x_6291_);
v___x_6293_ = v___x_6281_;
goto v_reusejp_6292_;
}
else
{
lean_object* v_reuseFailAlloc_6298_; 
v_reuseFailAlloc_6298_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6298_, 0, v_env_6271_);
lean_ctor_set(v_reuseFailAlloc_6298_, 1, v_nextMacroScope_6272_);
lean_ctor_set(v_reuseFailAlloc_6298_, 2, v_ngen_6273_);
lean_ctor_set(v_reuseFailAlloc_6298_, 3, v_auxDeclNGen_6274_);
lean_ctor_set(v_reuseFailAlloc_6298_, 4, v___x_6291_);
lean_ctor_set(v_reuseFailAlloc_6298_, 5, v_cache_6275_);
lean_ctor_set(v_reuseFailAlloc_6298_, 6, v_recordedDeps_6276_);
lean_ctor_set(v_reuseFailAlloc_6298_, 7, v_messages_6277_);
lean_ctor_set(v_reuseFailAlloc_6298_, 8, v_infoState_6278_);
lean_ctor_set(v_reuseFailAlloc_6298_, 9, v_snapshotTasks_6279_);
v___x_6293_ = v_reuseFailAlloc_6298_;
goto v_reusejp_6292_;
}
v_reusejp_6292_:
{
lean_object* v___x_6294_; lean_object* v___x_6296_; 
v___x_6294_ = lean_st_ref_put(v___y_6246_, v___x_6293_);
if (v_isShared_6268_ == 0)
{
lean_ctor_set(v___x_6267_, 0, v___x_6287_);
v___x_6296_ = v___x_6267_;
goto v_reusejp_6295_;
}
else
{
lean_object* v_reuseFailAlloc_6297_; 
v_reuseFailAlloc_6297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6297_, 0, v___x_6287_);
v___x_6296_ = v_reuseFailAlloc_6297_;
goto v_reusejp_6295_;
}
v_reusejp_6295_:
{
return v___x_6296_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_6304_, lean_object* v_data_6305_, lean_object* v_ref_6306_, lean_object* v_msg_6307_, lean_object* v___y_6308_, lean_object* v___y_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_){
_start:
{
lean_object* v_res_6313_; 
v_res_6313_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6304_, v_data_6305_, v_ref_6306_, v_msg_6307_, v___y_6308_, v___y_6309_, v___y_6310_, v___y_6311_);
lean_dec(v___y_6311_);
lean_dec_ref(v___y_6310_);
lean_dec(v___y_6309_);
lean_dec_ref(v___y_6308_);
return v_res_6313_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_6315_; lean_object* v___x_6316_; 
v___x_6315_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_6316_ = l_Lean_stringToMessageData(v___x_6315_);
return v___x_6316_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_6317_; double v___x_6318_; 
v___x_6317_ = lean_unsigned_to_nat(1000u);
v___x_6318_ = lean_float_of_nat(v___x_6317_);
return v___x_6318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_6319_, uint8_t v_collapsed_6320_, lean_object* v_tag_6321_, lean_object* v_opts_6322_, uint8_t v_clsEnabled_6323_, lean_object* v_oldTraces_6324_, lean_object* v_msg_6325_, lean_object* v_resStartStop_6326_, lean_object* v___y_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_){
_start:
{
lean_object* v_fst_6339_; lean_object* v_snd_6340_; lean_object* v___y_6342_; lean_object* v___y_6343_; lean_object* v_data_6344_; lean_object* v_fst_6355_; lean_object* v_snd_6356_; lean_object* v___x_6357_; uint8_t v___x_6358_; lean_object* v___y_6360_; lean_object* v_a_6361_; uint8_t v___y_6376_; double v___y_6408_; 
v_fst_6339_ = lean_ctor_get(v_resStartStop_6326_, 0);
lean_inc(v_fst_6339_);
v_snd_6340_ = lean_ctor_get(v_resStartStop_6326_, 1);
lean_inc(v_snd_6340_);
lean_dec_ref(v_resStartStop_6326_);
v_fst_6355_ = lean_ctor_get(v_snd_6340_, 0);
lean_inc(v_fst_6355_);
v_snd_6356_ = lean_ctor_get(v_snd_6340_, 1);
lean_inc(v_snd_6356_);
lean_dec(v_snd_6340_);
v___x_6357_ = l_Lean_trace_profiler;
v___x_6358_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6322_, v___x_6357_);
if (v___x_6358_ == 0)
{
v___y_6376_ = v___x_6358_;
goto v___jp_6375_;
}
else
{
lean_object* v___x_6413_; uint8_t v___x_6414_; 
v___x_6413_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6414_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_6322_, v___x_6413_);
if (v___x_6414_ == 0)
{
lean_object* v___x_6415_; lean_object* v___x_6416_; double v___x_6417_; double v___x_6418_; double v___x_6419_; 
v___x_6415_ = l_Lean_trace_profiler_threshold;
v___x_6416_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6322_, v___x_6415_);
v___x_6417_ = lean_float_of_nat(v___x_6416_);
v___x_6418_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_6419_ = lean_float_div(v___x_6417_, v___x_6418_);
v___y_6408_ = v___x_6419_;
goto v___jp_6407_;
}
else
{
lean_object* v___x_6420_; lean_object* v___x_6421_; double v___x_6422_; 
v___x_6420_ = l_Lean_trace_profiler_threshold;
v___x_6421_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_6322_, v___x_6420_);
v___x_6422_ = lean_float_of_nat(v___x_6421_);
v___y_6408_ = v___x_6422_;
goto v___jp_6407_;
}
}
v___jp_6341_:
{
lean_object* v___x_6345_; 
lean_inc(v___y_6342_);
v___x_6345_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6324_, v_data_6344_, v___y_6342_, v___y_6343_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_);
if (lean_obj_tag(v___x_6345_) == 0)
{
lean_object* v___x_6346_; 
lean_dec_ref_known(v___x_6345_, 1);
v___x_6346_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6339_);
return v___x_6346_;
}
else
{
lean_object* v_a_6347_; lean_object* v___x_6349_; uint8_t v_isShared_6350_; uint8_t v_isSharedCheck_6354_; 
lean_dec(v_fst_6339_);
v_a_6347_ = lean_ctor_get(v___x_6345_, 0);
v_isSharedCheck_6354_ = !lean_is_exclusive(v___x_6345_);
if (v_isSharedCheck_6354_ == 0)
{
v___x_6349_ = v___x_6345_;
v_isShared_6350_ = v_isSharedCheck_6354_;
goto v_resetjp_6348_;
}
else
{
lean_inc(v_a_6347_);
lean_dec(v___x_6345_);
v___x_6349_ = lean_box(0);
v_isShared_6350_ = v_isSharedCheck_6354_;
goto v_resetjp_6348_;
}
v_resetjp_6348_:
{
lean_object* v___x_6352_; 
if (v_isShared_6350_ == 0)
{
v___x_6352_ = v___x_6349_;
goto v_reusejp_6351_;
}
else
{
lean_object* v_reuseFailAlloc_6353_; 
v_reuseFailAlloc_6353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6353_, 0, v_a_6347_);
v___x_6352_ = v_reuseFailAlloc_6353_;
goto v_reusejp_6351_;
}
v_reusejp_6351_:
{
return v___x_6352_;
}
}
}
}
v___jp_6359_:
{
uint8_t v_result_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; double v___x_6365_; lean_object* v_data_6366_; 
v_result_6362_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_6339_);
v___x_6363_ = lean_box(v_result_6362_);
v___x_6364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6364_, 0, v___x_6363_);
v___x_6365_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6321_);
lean_inc_ref(v___x_6364_);
lean_inc(v_cls_6319_);
v_data_6366_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6366_, 0, v_cls_6319_);
lean_ctor_set(v_data_6366_, 1, v___x_6364_);
lean_ctor_set(v_data_6366_, 2, v_tag_6321_);
lean_ctor_set_float(v_data_6366_, sizeof(void*)*3, v___x_6365_);
lean_ctor_set_float(v_data_6366_, sizeof(void*)*3 + 8, v___x_6365_);
lean_ctor_set_uint8(v_data_6366_, sizeof(void*)*3 + 16, v_collapsed_6320_);
if (v___x_6358_ == 0)
{
lean_dec_ref_known(v___x_6364_, 1);
lean_dec(v_snd_6356_);
lean_dec(v_fst_6355_);
lean_dec_ref(v_tag_6321_);
lean_dec(v_cls_6319_);
v___y_6342_ = v___y_6360_;
v___y_6343_ = v_a_6361_;
v_data_6344_ = v_data_6366_;
goto v___jp_6341_;
}
else
{
lean_object* v_data_6367_; double v___x_6368_; double v___x_6369_; 
lean_dec_ref_known(v_data_6366_, 3);
v_data_6367_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6367_, 0, v_cls_6319_);
lean_ctor_set(v_data_6367_, 1, v___x_6364_);
lean_ctor_set(v_data_6367_, 2, v_tag_6321_);
v___x_6368_ = lean_unbox_float(v_fst_6355_);
lean_dec(v_fst_6355_);
lean_ctor_set_float(v_data_6367_, sizeof(void*)*3, v___x_6368_);
v___x_6369_ = lean_unbox_float(v_snd_6356_);
lean_dec(v_snd_6356_);
lean_ctor_set_float(v_data_6367_, sizeof(void*)*3 + 8, v___x_6369_);
lean_ctor_set_uint8(v_data_6367_, sizeof(void*)*3 + 16, v_collapsed_6320_);
v___y_6342_ = v___y_6360_;
v___y_6343_ = v_a_6361_;
v_data_6344_ = v_data_6367_;
goto v___jp_6341_;
}
}
v___jp_6370_:
{
lean_object* v_ref_6371_; lean_object* v___x_6372_; 
v_ref_6371_ = lean_ctor_get(v___y_6336_, 2);
lean_inc(v___y_6337_);
lean_inc_ref(v___y_6336_);
lean_inc(v___y_6335_);
lean_inc_ref(v___y_6334_);
lean_inc(v___y_6333_);
lean_inc_ref(v___y_6332_);
lean_inc(v___y_6331_);
lean_inc_ref(v___y_6330_);
lean_inc(v___y_6329_);
lean_inc(v___y_6328_);
lean_inc_ref(v___y_6327_);
lean_inc(v_fst_6339_);
v___x_6372_ = lean_apply_13(v_msg_6325_, v_fst_6339_, v___y_6327_, v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_, lean_box(0));
if (lean_obj_tag(v___x_6372_) == 0)
{
lean_object* v_a_6373_; 
v_a_6373_ = lean_ctor_get(v___x_6372_, 0);
lean_inc(v_a_6373_);
lean_dec_ref_known(v___x_6372_, 1);
v___y_6360_ = v_ref_6371_;
v_a_6361_ = v_a_6373_;
goto v___jp_6359_;
}
else
{
lean_object* v___x_6374_; 
lean_dec_ref_known(v___x_6372_, 1);
v___x_6374_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_6360_ = v_ref_6371_;
v_a_6361_ = v___x_6374_;
goto v___jp_6359_;
}
}
v___jp_6375_:
{
if (v_clsEnabled_6323_ == 0)
{
if (v___y_6376_ == 0)
{
lean_object* v___x_6377_; lean_object* v_traceState_6378_; lean_object* v_env_6379_; lean_object* v_nextMacroScope_6380_; lean_object* v_ngen_6381_; lean_object* v_auxDeclNGen_6382_; lean_object* v_cache_6383_; lean_object* v_recordedDeps_6384_; lean_object* v_messages_6385_; lean_object* v_infoState_6386_; lean_object* v_snapshotTasks_6387_; lean_object* v___x_6389_; uint8_t v_isShared_6390_; uint8_t v_isSharedCheck_6406_; 
lean_dec(v_snd_6356_);
lean_dec(v_fst_6355_);
lean_dec_ref(v_msg_6325_);
lean_dec_ref(v_tag_6321_);
lean_dec(v_cls_6319_);
v___x_6377_ = lean_st_ref_take(v___y_6337_);
v_traceState_6378_ = lean_ctor_get(v___x_6377_, 4);
v_env_6379_ = lean_ctor_get(v___x_6377_, 0);
v_nextMacroScope_6380_ = lean_ctor_get(v___x_6377_, 1);
v_ngen_6381_ = lean_ctor_get(v___x_6377_, 2);
v_auxDeclNGen_6382_ = lean_ctor_get(v___x_6377_, 3);
v_cache_6383_ = lean_ctor_get(v___x_6377_, 5);
v_recordedDeps_6384_ = lean_ctor_get(v___x_6377_, 6);
v_messages_6385_ = lean_ctor_get(v___x_6377_, 7);
v_infoState_6386_ = lean_ctor_get(v___x_6377_, 8);
v_snapshotTasks_6387_ = lean_ctor_get(v___x_6377_, 9);
v_isSharedCheck_6406_ = !lean_is_exclusive(v___x_6377_);
if (v_isSharedCheck_6406_ == 0)
{
v___x_6389_ = v___x_6377_;
v_isShared_6390_ = v_isSharedCheck_6406_;
goto v_resetjp_6388_;
}
else
{
lean_inc(v_snapshotTasks_6387_);
lean_inc(v_infoState_6386_);
lean_inc(v_messages_6385_);
lean_inc(v_recordedDeps_6384_);
lean_inc(v_cache_6383_);
lean_inc(v_traceState_6378_);
lean_inc(v_auxDeclNGen_6382_);
lean_inc(v_ngen_6381_);
lean_inc(v_nextMacroScope_6380_);
lean_inc(v_env_6379_);
lean_dec(v___x_6377_);
v___x_6389_ = lean_box(0);
v_isShared_6390_ = v_isSharedCheck_6406_;
goto v_resetjp_6388_;
}
v_resetjp_6388_:
{
uint64_t v_tid_6391_; lean_object* v_traces_6392_; lean_object* v___x_6394_; uint8_t v_isShared_6395_; uint8_t v_isSharedCheck_6405_; 
v_tid_6391_ = lean_ctor_get_uint64(v_traceState_6378_, sizeof(void*)*1);
v_traces_6392_ = lean_ctor_get(v_traceState_6378_, 0);
v_isSharedCheck_6405_ = !lean_is_exclusive(v_traceState_6378_);
if (v_isSharedCheck_6405_ == 0)
{
v___x_6394_ = v_traceState_6378_;
v_isShared_6395_ = v_isSharedCheck_6405_;
goto v_resetjp_6393_;
}
else
{
lean_inc(v_traces_6392_);
lean_dec(v_traceState_6378_);
v___x_6394_ = lean_box(0);
v_isShared_6395_ = v_isSharedCheck_6405_;
goto v_resetjp_6393_;
}
v_resetjp_6393_:
{
lean_object* v___x_6396_; lean_object* v___x_6398_; 
v___x_6396_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6324_, v_traces_6392_);
lean_dec_ref(v_traces_6392_);
if (v_isShared_6395_ == 0)
{
lean_ctor_set(v___x_6394_, 0, v___x_6396_);
v___x_6398_ = v___x_6394_;
goto v_reusejp_6397_;
}
else
{
lean_object* v_reuseFailAlloc_6404_; 
v_reuseFailAlloc_6404_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6404_, 0, v___x_6396_);
lean_ctor_set_uint64(v_reuseFailAlloc_6404_, sizeof(void*)*1, v_tid_6391_);
v___x_6398_ = v_reuseFailAlloc_6404_;
goto v_reusejp_6397_;
}
v_reusejp_6397_:
{
lean_object* v___x_6400_; 
if (v_isShared_6390_ == 0)
{
lean_ctor_set(v___x_6389_, 4, v___x_6398_);
v___x_6400_ = v___x_6389_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6403_; 
v_reuseFailAlloc_6403_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6403_, 0, v_env_6379_);
lean_ctor_set(v_reuseFailAlloc_6403_, 1, v_nextMacroScope_6380_);
lean_ctor_set(v_reuseFailAlloc_6403_, 2, v_ngen_6381_);
lean_ctor_set(v_reuseFailAlloc_6403_, 3, v_auxDeclNGen_6382_);
lean_ctor_set(v_reuseFailAlloc_6403_, 4, v___x_6398_);
lean_ctor_set(v_reuseFailAlloc_6403_, 5, v_cache_6383_);
lean_ctor_set(v_reuseFailAlloc_6403_, 6, v_recordedDeps_6384_);
lean_ctor_set(v_reuseFailAlloc_6403_, 7, v_messages_6385_);
lean_ctor_set(v_reuseFailAlloc_6403_, 8, v_infoState_6386_);
lean_ctor_set(v_reuseFailAlloc_6403_, 9, v_snapshotTasks_6387_);
v___x_6400_ = v_reuseFailAlloc_6403_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
lean_object* v___x_6401_; lean_object* v___x_6402_; 
v___x_6401_ = lean_st_ref_put(v___y_6337_, v___x_6400_);
v___x_6402_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_6339_);
return v___x_6402_;
}
}
}
}
}
else
{
goto v___jp_6370_;
}
}
else
{
goto v___jp_6370_;
}
}
v___jp_6407_:
{
double v___x_6409_; double v___x_6410_; double v___x_6411_; uint8_t v___x_6412_; 
v___x_6409_ = lean_unbox_float(v_snd_6356_);
v___x_6410_ = lean_unbox_float(v_fst_6355_);
v___x_6411_ = lean_float_sub(v___x_6409_, v___x_6410_);
v___x_6412_ = lean_float_decLt(v___y_6408_, v___x_6411_);
v___y_6376_ = v___x_6412_;
goto v___jp_6375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_6423_ = _args[0];
lean_object* v_collapsed_6424_ = _args[1];
lean_object* v_tag_6425_ = _args[2];
lean_object* v_opts_6426_ = _args[3];
lean_object* v_clsEnabled_6427_ = _args[4];
lean_object* v_oldTraces_6428_ = _args[5];
lean_object* v_msg_6429_ = _args[6];
lean_object* v_resStartStop_6430_ = _args[7];
lean_object* v___y_6431_ = _args[8];
lean_object* v___y_6432_ = _args[9];
lean_object* v___y_6433_ = _args[10];
lean_object* v___y_6434_ = _args[11];
lean_object* v___y_6435_ = _args[12];
lean_object* v___y_6436_ = _args[13];
lean_object* v___y_6437_ = _args[14];
lean_object* v___y_6438_ = _args[15];
lean_object* v___y_6439_ = _args[16];
lean_object* v___y_6440_ = _args[17];
lean_object* v___y_6441_ = _args[18];
lean_object* v___y_6442_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_6443_; uint8_t v_clsEnabled_boxed_6444_; lean_object* v_res_6445_; 
v_collapsed_boxed_6443_ = lean_unbox(v_collapsed_6424_);
v_clsEnabled_boxed_6444_ = lean_unbox(v_clsEnabled_6427_);
v_res_6445_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_6423_, v_collapsed_boxed_6443_, v_tag_6425_, v_opts_6426_, v_clsEnabled_boxed_6444_, v_oldTraces_6428_, v_msg_6429_, v_resStartStop_6430_, v___y_6431_, v___y_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec(v___y_6439_);
lean_dec_ref(v___y_6438_);
lean_dec(v___y_6437_);
lean_dec_ref(v___y_6436_);
lean_dec(v___y_6435_);
lean_dec_ref(v___y_6434_);
lean_dec(v___y_6433_);
lean_dec(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec_ref(v_opts_6426_);
return v_res_6445_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6450_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_6451_ = l_Lean_stringToMessageData(v___x_6450_);
return v___x_6451_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_6452_, lean_object* v_b_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_){
_start:
{
if (lean_obj_tag(v_as_x27_6452_) == 0)
{
lean_object* v___x_6466_; 
v___x_6466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6466_, 0, v_b_6453_);
return v___x_6466_;
}
else
{
lean_object* v_head_6467_; lean_object* v_toCold_6468_; lean_object* v_options_6469_; lean_object* v_tail_6470_; lean_object* v_name_6471_; lean_object* v_run_x27_6472_; lean_object* v_inheritedTraceOptions_6473_; uint8_t v_hasTrace_6474_; lean_object* v___x_6475_; uint8_t v___y_6477_; lean_object* v___x_6482_; lean_object* v___y_6484_; 
lean_dec_ref(v_b_6453_);
v_head_6467_ = lean_ctor_get(v_as_x27_6452_, 0);
v_toCold_6468_ = lean_ctor_get(v___y_6463_, 0);
v_options_6469_ = lean_ctor_get(v_toCold_6468_, 2);
v_tail_6470_ = lean_ctor_get(v_as_x27_6452_, 1);
v_name_6471_ = lean_ctor_get(v_head_6467_, 0);
v_run_x27_6472_ = lean_ctor_get(v_head_6467_, 1);
v_inheritedTraceOptions_6473_ = lean_ctor_get(v_toCold_6468_, 11);
v_hasTrace_6474_ = lean_ctor_get_uint8(v_options_6469_, sizeof(void*)*1);
v___x_6475_ = lean_box(0);
v___x_6482_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_6474_ == 0)
{
lean_object* v___x_6512_; 
lean_inc_ref(v_run_x27_6472_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc_ref(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc_ref(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc(v___y_6455_);
lean_inc_ref(v___y_6454_);
v___x_6512_ = lean_apply_12(v_run_x27_6472_, v___y_6454_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, lean_box(0));
v___y_6484_ = v___x_6512_;
goto v___jp_6483_;
}
else
{
lean_object* v___f_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; uint8_t v___x_6517_; lean_object* v___y_6519_; lean_object* v___y_6520_; lean_object* v_a_6521_; lean_object* v___y_6534_; lean_object* v___y_6535_; lean_object* v_a_6536_; 
lean_inc(v_name_6471_);
v___f_6513_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_6513_, 0, v_name_6471_);
v___x_6514_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6515_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_6516_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6517_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6473_, v_options_6469_, v___x_6516_);
if (v___x_6517_ == 0)
{
lean_object* v___x_6586_; uint8_t v___x_6587_; 
v___x_6586_ = l_Lean_trace_profiler;
v___x_6587_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6469_, v___x_6586_);
if (v___x_6587_ == 0)
{
lean_object* v___x_6588_; 
lean_dec_ref(v___f_6513_);
lean_inc_ref(v_run_x27_6472_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc_ref(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc_ref(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc(v___y_6455_);
lean_inc_ref(v___y_6454_);
v___x_6588_ = lean_apply_12(v_run_x27_6472_, v___y_6454_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, lean_box(0));
v___y_6484_ = v___x_6588_;
goto v___jp_6483_;
}
else
{
goto v___jp_6545_;
}
}
else
{
goto v___jp_6545_;
}
v___jp_6518_:
{
lean_object* v___x_6522_; double v___x_6523_; double v___x_6524_; double v___x_6525_; double v___x_6526_; double v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; 
v___x_6522_ = lean_io_mono_nanos_now();
v___x_6523_ = lean_float_of_nat(v___y_6519_);
v___x_6524_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_6525_ = lean_float_div(v___x_6523_, v___x_6524_);
v___x_6526_ = lean_float_of_nat(v___x_6522_);
v___x_6527_ = lean_float_div(v___x_6526_, v___x_6524_);
v___x_6528_ = lean_box_float(v___x_6525_);
v___x_6529_ = lean_box_float(v___x_6527_);
v___x_6530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6530_, 0, v___x_6528_);
lean_ctor_set(v___x_6530_, 1, v___x_6529_);
v___x_6531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6531_, 0, v_a_6521_);
lean_ctor_set(v___x_6531_, 1, v___x_6530_);
v___x_6532_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6514_, v_hasTrace_6474_, v___x_6515_, v_options_6469_, v___x_6517_, v___y_6520_, v___f_6513_, v___x_6531_, v___y_6454_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_);
v___y_6484_ = v___x_6532_;
goto v___jp_6483_;
}
v___jp_6533_:
{
lean_object* v___x_6537_; double v___x_6538_; double v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; 
v___x_6537_ = lean_io_get_num_heartbeats();
v___x_6538_ = lean_float_of_nat(v___y_6534_);
v___x_6539_ = lean_float_of_nat(v___x_6537_);
v___x_6540_ = lean_box_float(v___x_6538_);
v___x_6541_ = lean_box_float(v___x_6539_);
v___x_6542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6542_, 0, v___x_6540_);
lean_ctor_set(v___x_6542_, 1, v___x_6541_);
v___x_6543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6543_, 0, v_a_6536_);
lean_ctor_set(v___x_6543_, 1, v___x_6542_);
v___x_6544_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_6514_, v_hasTrace_6474_, v___x_6515_, v_options_6469_, v___x_6517_, v___y_6535_, v___f_6513_, v___x_6543_, v___y_6454_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_);
v___y_6484_ = v___x_6544_;
goto v___jp_6483_;
}
v___jp_6545_:
{
lean_object* v___x_6546_; lean_object* v_a_6547_; lean_object* v___x_6548_; uint8_t v___x_6549_; 
v___x_6546_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_6464_);
v_a_6547_ = lean_ctor_get(v___x_6546_, 0);
lean_inc(v_a_6547_);
lean_dec_ref(v___x_6546_);
v___x_6548_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6549_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_6469_, v___x_6548_);
if (v___x_6549_ == 0)
{
lean_object* v___x_6550_; lean_object* v___x_6551_; 
v___x_6550_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_6472_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc_ref(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc_ref(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc(v___y_6455_);
lean_inc_ref(v___y_6454_);
v___x_6551_ = lean_apply_12(v_run_x27_6472_, v___y_6454_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, lean_box(0));
if (lean_obj_tag(v___x_6551_) == 0)
{
lean_object* v_a_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6559_; 
v_a_6552_ = lean_ctor_get(v___x_6551_, 0);
v_isSharedCheck_6559_ = !lean_is_exclusive(v___x_6551_);
if (v_isSharedCheck_6559_ == 0)
{
v___x_6554_ = v___x_6551_;
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_a_6552_);
lean_dec(v___x_6551_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v___x_6557_; 
if (v_isShared_6555_ == 0)
{
lean_ctor_set_tag(v___x_6554_, 1);
v___x_6557_ = v___x_6554_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6558_; 
v_reuseFailAlloc_6558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6558_, 0, v_a_6552_);
v___x_6557_ = v_reuseFailAlloc_6558_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
v___y_6519_ = v___x_6550_;
v___y_6520_ = v_a_6547_;
v_a_6521_ = v___x_6557_;
goto v___jp_6518_;
}
}
}
else
{
lean_object* v_a_6560_; lean_object* v___x_6562_; uint8_t v_isShared_6563_; uint8_t v_isSharedCheck_6567_; 
v_a_6560_ = lean_ctor_get(v___x_6551_, 0);
v_isSharedCheck_6567_ = !lean_is_exclusive(v___x_6551_);
if (v_isSharedCheck_6567_ == 0)
{
v___x_6562_ = v___x_6551_;
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
else
{
lean_inc(v_a_6560_);
lean_dec(v___x_6551_);
v___x_6562_ = lean_box(0);
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
v_resetjp_6561_:
{
lean_object* v___x_6565_; 
if (v_isShared_6563_ == 0)
{
lean_ctor_set_tag(v___x_6562_, 0);
v___x_6565_ = v___x_6562_;
goto v_reusejp_6564_;
}
else
{
lean_object* v_reuseFailAlloc_6566_; 
v_reuseFailAlloc_6566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6566_, 0, v_a_6560_);
v___x_6565_ = v_reuseFailAlloc_6566_;
goto v_reusejp_6564_;
}
v_reusejp_6564_:
{
v___y_6519_ = v___x_6550_;
v___y_6520_ = v_a_6547_;
v_a_6521_ = v___x_6565_;
goto v___jp_6518_;
}
}
}
}
else
{
lean_object* v___x_6568_; lean_object* v___x_6569_; 
v___x_6568_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_6472_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc_ref(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc_ref(v___y_6459_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc(v___y_6455_);
lean_inc_ref(v___y_6454_);
v___x_6569_ = lean_apply_12(v_run_x27_6472_, v___y_6454_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, lean_box(0));
if (lean_obj_tag(v___x_6569_) == 0)
{
lean_object* v_a_6570_; lean_object* v___x_6572_; uint8_t v_isShared_6573_; uint8_t v_isSharedCheck_6577_; 
v_a_6570_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6577_ == 0)
{
v___x_6572_ = v___x_6569_;
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
else
{
lean_inc(v_a_6570_);
lean_dec(v___x_6569_);
v___x_6572_ = lean_box(0);
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
v_resetjp_6571_:
{
lean_object* v___x_6575_; 
if (v_isShared_6573_ == 0)
{
lean_ctor_set_tag(v___x_6572_, 1);
v___x_6575_ = v___x_6572_;
goto v_reusejp_6574_;
}
else
{
lean_object* v_reuseFailAlloc_6576_; 
v_reuseFailAlloc_6576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6576_, 0, v_a_6570_);
v___x_6575_ = v_reuseFailAlloc_6576_;
goto v_reusejp_6574_;
}
v_reusejp_6574_:
{
v___y_6534_ = v___x_6568_;
v___y_6535_ = v_a_6547_;
v_a_6536_ = v___x_6575_;
goto v___jp_6533_;
}
}
}
else
{
lean_object* v_a_6578_; lean_object* v___x_6580_; uint8_t v_isShared_6581_; uint8_t v_isSharedCheck_6585_; 
v_a_6578_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6585_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6585_ == 0)
{
v___x_6580_ = v___x_6569_;
v_isShared_6581_ = v_isSharedCheck_6585_;
goto v_resetjp_6579_;
}
else
{
lean_inc(v_a_6578_);
lean_dec(v___x_6569_);
v___x_6580_ = lean_box(0);
v_isShared_6581_ = v_isSharedCheck_6585_;
goto v_resetjp_6579_;
}
v_resetjp_6579_:
{
lean_object* v___x_6583_; 
if (v_isShared_6581_ == 0)
{
lean_ctor_set_tag(v___x_6580_, 0);
v___x_6583_ = v___x_6580_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6584_; 
v_reuseFailAlloc_6584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6584_, 0, v_a_6578_);
v___x_6583_ = v_reuseFailAlloc_6584_;
goto v_reusejp_6582_;
}
v_reusejp_6582_:
{
v___y_6534_ = v___x_6568_;
v___y_6535_ = v_a_6547_;
v_a_6536_ = v___x_6583_;
goto v___jp_6533_;
}
}
}
}
}
}
v___jp_6476_:
{
lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; 
v___x_6478_ = lean_box(v___y_6477_);
v___x_6479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6479_, 0, v___x_6478_);
v___x_6480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6480_, 0, v___x_6479_);
lean_ctor_set(v___x_6480_, 1, v___x_6475_);
v___x_6481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6481_, 0, v___x_6480_);
return v___x_6481_;
}
v___jp_6483_:
{
if (lean_obj_tag(v___y_6484_) == 0)
{
lean_object* v_a_6485_; uint8_t v___x_6486_; 
v_a_6485_ = lean_ctor_get(v___y_6484_, 0);
lean_inc(v_a_6485_);
lean_dec_ref_known(v___y_6484_, 1);
v___x_6486_ = lean_unbox(v_a_6485_);
if (v___x_6486_ == 0)
{
lean_dec(v_a_6485_);
v_as_x27_6452_ = v_tail_6470_;
v_b_6453_ = v___x_6482_;
goto _start;
}
else
{
if (v_hasTrace_6474_ == 0)
{
uint8_t v___x_6488_; 
v___x_6488_ = lean_unbox(v_a_6485_);
lean_dec(v_a_6485_);
v___y_6477_ = v___x_6488_;
goto v___jp_6476_;
}
else
{
lean_object* v___x_6489_; lean_object* v___x_6490_; uint8_t v___x_6491_; 
v___x_6489_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6490_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6491_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6473_, v_options_6469_, v___x_6490_);
if (v___x_6491_ == 0)
{
uint8_t v___x_6492_; 
v___x_6492_ = lean_unbox(v_a_6485_);
lean_dec(v_a_6485_);
v___y_6477_ = v___x_6492_;
goto v___jp_6476_;
}
else
{
lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6493_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_6494_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6489_, v___x_6493_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_);
if (lean_obj_tag(v___x_6494_) == 0)
{
uint8_t v___x_6495_; 
lean_dec_ref_known(v___x_6494_, 1);
v___x_6495_ = lean_unbox(v_a_6485_);
lean_dec(v_a_6485_);
v___y_6477_ = v___x_6495_;
goto v___jp_6476_;
}
else
{
lean_object* v_a_6496_; lean_object* v___x_6498_; uint8_t v_isShared_6499_; uint8_t v_isSharedCheck_6503_; 
lean_dec(v_a_6485_);
v_a_6496_ = lean_ctor_get(v___x_6494_, 0);
v_isSharedCheck_6503_ = !lean_is_exclusive(v___x_6494_);
if (v_isSharedCheck_6503_ == 0)
{
v___x_6498_ = v___x_6494_;
v_isShared_6499_ = v_isSharedCheck_6503_;
goto v_resetjp_6497_;
}
else
{
lean_inc(v_a_6496_);
lean_dec(v___x_6494_);
v___x_6498_ = lean_box(0);
v_isShared_6499_ = v_isSharedCheck_6503_;
goto v_resetjp_6497_;
}
v_resetjp_6497_:
{
lean_object* v___x_6501_; 
if (v_isShared_6499_ == 0)
{
v___x_6501_ = v___x_6498_;
goto v_reusejp_6500_;
}
else
{
lean_object* v_reuseFailAlloc_6502_; 
v_reuseFailAlloc_6502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6502_, 0, v_a_6496_);
v___x_6501_ = v_reuseFailAlloc_6502_;
goto v_reusejp_6500_;
}
v_reusejp_6500_:
{
return v___x_6501_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6504_; lean_object* v___x_6506_; uint8_t v_isShared_6507_; uint8_t v_isSharedCheck_6511_; 
v_a_6504_ = lean_ctor_get(v___y_6484_, 0);
v_isSharedCheck_6511_ = !lean_is_exclusive(v___y_6484_);
if (v_isSharedCheck_6511_ == 0)
{
v___x_6506_ = v___y_6484_;
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
else
{
lean_inc(v_a_6504_);
lean_dec(v___y_6484_);
v___x_6506_ = lean_box(0);
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
v_resetjp_6505_:
{
lean_object* v___x_6509_; 
if (v_isShared_6507_ == 0)
{
v___x_6509_ = v___x_6506_;
goto v_reusejp_6508_;
}
else
{
lean_object* v_reuseFailAlloc_6510_; 
v_reuseFailAlloc_6510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_a_6504_);
v___x_6509_ = v_reuseFailAlloc_6510_;
goto v_reusejp_6508_;
}
v_reusejp_6508_:
{
return v___x_6509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_6589_, lean_object* v_b_6590_, lean_object* v___y_6591_, lean_object* v___y_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_, lean_object* v___y_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_){
_start:
{
lean_object* v_res_6603_; 
v_res_6603_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6589_, v_b_6590_, v___y_6591_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_);
lean_dec(v___y_6601_);
lean_dec_ref(v___y_6600_);
lean_dec(v___y_6599_);
lean_dec_ref(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec_ref(v___y_6596_);
lean_dec(v___y_6595_);
lean_dec_ref(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec(v___y_6592_);
lean_dec_ref(v___y_6591_);
lean_dec(v_as_x27_6589_);
return v_res_6603_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_6606_; lean_object* v___x_6607_; 
v___x_6606_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_6607_ = l_Lean_stringToMessageData(v___x_6606_);
return v___x_6607_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_6609_; lean_object* v___x_6610_; 
v___x_6609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_6610_ = l_Lean_stringToMessageData(v___x_6609_);
return v___x_6610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_6611_, lean_object* v_a_6612_, lean_object* v_a_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_){
_start:
{
lean_object* v___x_6624_; lean_object* v___x_6625_; 
v___x_6624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_6625_ = l_Lean_Core_checkSystem(v___x_6624_, v_a_6621_, v_a_6622_);
if (lean_obj_tag(v___x_6625_) == 0)
{
lean_object* v___x_6626_; lean_object* v_caches_6627_; lean_object* v_typeAnalysis_6628_; lean_object* v_target_6629_; lean_object* v_hypotheses_6630_; lean_object* v___x_6632_; uint8_t v_isShared_6633_; uint8_t v_isSharedCheck_6715_; 
lean_dec_ref_known(v___x_6625_, 1);
v___x_6626_ = lean_st_ref_take(v_a_6613_);
v_caches_6627_ = lean_ctor_get(v___x_6626_, 0);
v_typeAnalysis_6628_ = lean_ctor_get(v___x_6626_, 1);
v_target_6629_ = lean_ctor_get(v___x_6626_, 2);
v_hypotheses_6630_ = lean_ctor_get(v___x_6626_, 3);
v_isSharedCheck_6715_ = !lean_is_exclusive(v___x_6626_);
if (v_isSharedCheck_6715_ == 0)
{
v___x_6632_ = v___x_6626_;
v_isShared_6633_ = v_isSharedCheck_6715_;
goto v_resetjp_6631_;
}
else
{
lean_inc(v_hypotheses_6630_);
lean_inc(v_target_6629_);
lean_inc(v_typeAnalysis_6628_);
lean_inc(v_caches_6627_);
lean_dec(v___x_6626_);
v___x_6632_ = lean_box(0);
v_isShared_6633_ = v_isSharedCheck_6715_;
goto v_resetjp_6631_;
}
v_resetjp_6631_:
{
uint8_t v___x_6634_; lean_object* v___x_6636_; 
v___x_6634_ = 0;
if (v_isShared_6633_ == 0)
{
v___x_6636_ = v___x_6632_;
goto v_reusejp_6635_;
}
else
{
lean_object* v_reuseFailAlloc_6714_; 
v_reuseFailAlloc_6714_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_caches_6627_);
lean_ctor_set(v_reuseFailAlloc_6714_, 1, v_typeAnalysis_6628_);
lean_ctor_set(v_reuseFailAlloc_6714_, 2, v_target_6629_);
lean_ctor_set(v_reuseFailAlloc_6714_, 3, v_hypotheses_6630_);
v___x_6636_ = v_reuseFailAlloc_6714_;
goto v_reusejp_6635_;
}
v_reusejp_6635_:
{
lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; 
lean_ctor_set_uint8(v___x_6636_, sizeof(void*)*4, v___x_6634_);
v___x_6637_ = lean_st_ref_put(v_a_6613_, v___x_6636_);
v___x_6638_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_6639_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_6611_, v___x_6638_, v_a_6612_, v_a_6613_, v_a_6614_, v_a_6615_, v_a_6616_, v_a_6617_, v_a_6618_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_);
if (lean_obj_tag(v___x_6639_) == 0)
{
lean_object* v_a_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6705_; 
v_a_6640_ = lean_ctor_get(v___x_6639_, 0);
v_isSharedCheck_6705_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6705_ == 0)
{
v___x_6642_ = v___x_6639_;
v_isShared_6643_ = v_isSharedCheck_6705_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_a_6640_);
lean_dec(v___x_6639_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6705_;
goto v_resetjp_6641_;
}
v_resetjp_6641_:
{
lean_object* v_fst_6644_; 
v_fst_6644_ = lean_ctor_get(v_a_6640_, 0);
lean_inc(v_fst_6644_);
lean_dec(v_a_6640_);
if (lean_obj_tag(v_fst_6644_) == 0)
{
lean_object* v___x_6645_; uint8_t v_didChange_6646_; 
v___x_6645_ = lean_st_ref_get(v_a_6613_);
v_didChange_6646_ = lean_ctor_get_uint8(v___x_6645_, sizeof(void*)*4);
lean_dec(v___x_6645_);
if (v_didChange_6646_ == 0)
{
lean_object* v_toCold_6647_; lean_object* v_options_6648_; uint8_t v_hasTrace_6649_; 
v_toCold_6647_ = lean_ctor_get(v_a_6621_, 0);
v_options_6648_ = lean_ctor_get(v_toCold_6647_, 2);
v_hasTrace_6649_ = lean_ctor_get_uint8(v_options_6648_, sizeof(void*)*1);
if (v_hasTrace_6649_ == 0)
{
lean_object* v___x_6650_; lean_object* v___x_6652_; 
v___x_6650_ = lean_box(v_didChange_6646_);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v___x_6650_);
v___x_6652_ = v___x_6642_;
goto v_reusejp_6651_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v___x_6650_);
v___x_6652_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6651_;
}
v_reusejp_6651_:
{
return v___x_6652_;
}
}
else
{
lean_object* v_inheritedTraceOptions_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; uint8_t v___x_6657_; 
v_inheritedTraceOptions_6654_ = lean_ctor_get(v_toCold_6647_, 11);
v___x_6655_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6656_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6657_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6654_, v_options_6648_, v___x_6656_);
if (v___x_6657_ == 0)
{
lean_object* v___x_6658_; lean_object* v___x_6660_; 
v___x_6658_ = lean_box(v_didChange_6646_);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v___x_6658_);
v___x_6660_ = v___x_6642_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6661_; 
v_reuseFailAlloc_6661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6661_, 0, v___x_6658_);
v___x_6660_ = v_reuseFailAlloc_6661_;
goto v_reusejp_6659_;
}
v_reusejp_6659_:
{
return v___x_6660_;
}
}
else
{
lean_object* v___x_6662_; lean_object* v___x_6663_; 
lean_del_object(v___x_6642_);
v___x_6662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_6663_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6655_, v___x_6662_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_);
if (lean_obj_tag(v___x_6663_) == 0)
{
lean_object* v___x_6665_; uint8_t v_isShared_6666_; uint8_t v_isSharedCheck_6671_; 
v_isSharedCheck_6671_ = !lean_is_exclusive(v___x_6663_);
if (v_isSharedCheck_6671_ == 0)
{
lean_object* v_unused_6672_; 
v_unused_6672_ = lean_ctor_get(v___x_6663_, 0);
lean_dec(v_unused_6672_);
v___x_6665_ = v___x_6663_;
v_isShared_6666_ = v_isSharedCheck_6671_;
goto v_resetjp_6664_;
}
else
{
lean_dec(v___x_6663_);
v___x_6665_ = lean_box(0);
v_isShared_6666_ = v_isSharedCheck_6671_;
goto v_resetjp_6664_;
}
v_resetjp_6664_:
{
lean_object* v___x_6667_; lean_object* v___x_6669_; 
v___x_6667_ = lean_box(v_didChange_6646_);
if (v_isShared_6666_ == 0)
{
lean_ctor_set(v___x_6665_, 0, v___x_6667_);
v___x_6669_ = v___x_6665_;
goto v_reusejp_6668_;
}
else
{
lean_object* v_reuseFailAlloc_6670_; 
v_reuseFailAlloc_6670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6670_, 0, v___x_6667_);
v___x_6669_ = v_reuseFailAlloc_6670_;
goto v_reusejp_6668_;
}
v_reusejp_6668_:
{
return v___x_6669_;
}
}
}
else
{
lean_object* v_a_6673_; lean_object* v___x_6675_; uint8_t v_isShared_6676_; uint8_t v_isSharedCheck_6680_; 
v_a_6673_ = lean_ctor_get(v___x_6663_, 0);
v_isSharedCheck_6680_ = !lean_is_exclusive(v___x_6663_);
if (v_isSharedCheck_6680_ == 0)
{
v___x_6675_ = v___x_6663_;
v_isShared_6676_ = v_isSharedCheck_6680_;
goto v_resetjp_6674_;
}
else
{
lean_inc(v_a_6673_);
lean_dec(v___x_6663_);
v___x_6675_ = lean_box(0);
v_isShared_6676_ = v_isSharedCheck_6680_;
goto v_resetjp_6674_;
}
v_resetjp_6674_:
{
lean_object* v___x_6678_; 
if (v_isShared_6676_ == 0)
{
v___x_6678_ = v___x_6675_;
goto v_reusejp_6677_;
}
else
{
lean_object* v_reuseFailAlloc_6679_; 
v_reuseFailAlloc_6679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6679_, 0, v_a_6673_);
v___x_6678_ = v_reuseFailAlloc_6679_;
goto v_reusejp_6677_;
}
v_reusejp_6677_:
{
return v___x_6678_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_6681_; lean_object* v_options_6682_; uint8_t v_hasTrace_6683_; 
lean_del_object(v___x_6642_);
v_toCold_6681_ = lean_ctor_get(v_a_6621_, 0);
v_options_6682_ = lean_ctor_get(v_toCold_6681_, 2);
v_hasTrace_6683_ = lean_ctor_get_uint8(v_options_6682_, sizeof(void*)*1);
if (v_hasTrace_6683_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; uint8_t v___x_6688_; 
v_inheritedTraceOptions_6685_ = lean_ctor_get(v_toCold_6681_, 11);
v___x_6686_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_6687_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___x_6688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6685_, v_options_6682_, v___x_6687_);
if (v___x_6688_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_6690_; lean_object* v___x_6691_; 
v___x_6690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_6691_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_6686_, v___x_6690_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_);
if (lean_obj_tag(v___x_6691_) == 0)
{
lean_dec_ref_known(v___x_6691_, 1);
goto _start;
}
else
{
lean_object* v_a_6693_; lean_object* v___x_6695_; uint8_t v_isShared_6696_; uint8_t v_isSharedCheck_6700_; 
v_a_6693_ = lean_ctor_get(v___x_6691_, 0);
v_isSharedCheck_6700_ = !lean_is_exclusive(v___x_6691_);
if (v_isSharedCheck_6700_ == 0)
{
v___x_6695_ = v___x_6691_;
v_isShared_6696_ = v_isSharedCheck_6700_;
goto v_resetjp_6694_;
}
else
{
lean_inc(v_a_6693_);
lean_dec(v___x_6691_);
v___x_6695_ = lean_box(0);
v_isShared_6696_ = v_isSharedCheck_6700_;
goto v_resetjp_6694_;
}
v_resetjp_6694_:
{
lean_object* v___x_6698_; 
if (v_isShared_6696_ == 0)
{
v___x_6698_ = v___x_6695_;
goto v_reusejp_6697_;
}
else
{
lean_object* v_reuseFailAlloc_6699_; 
v_reuseFailAlloc_6699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6699_, 0, v_a_6693_);
v___x_6698_ = v_reuseFailAlloc_6699_;
goto v_reusejp_6697_;
}
v_reusejp_6697_:
{
return v___x_6698_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_6701_; lean_object* v___x_6703_; 
v_val_6701_ = lean_ctor_get(v_fst_6644_, 0);
lean_inc(v_val_6701_);
lean_dec_ref_known(v_fst_6644_, 1);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v_val_6701_);
v___x_6703_ = v___x_6642_;
goto v_reusejp_6702_;
}
else
{
lean_object* v_reuseFailAlloc_6704_; 
v_reuseFailAlloc_6704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6704_, 0, v_val_6701_);
v___x_6703_ = v_reuseFailAlloc_6704_;
goto v_reusejp_6702_;
}
v_reusejp_6702_:
{
return v___x_6703_;
}
}
}
}
else
{
lean_object* v_a_6706_; lean_object* v___x_6708_; uint8_t v_isShared_6709_; uint8_t v_isSharedCheck_6713_; 
v_a_6706_ = lean_ctor_get(v___x_6639_, 0);
v_isSharedCheck_6713_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6713_ == 0)
{
v___x_6708_ = v___x_6639_;
v_isShared_6709_ = v_isSharedCheck_6713_;
goto v_resetjp_6707_;
}
else
{
lean_inc(v_a_6706_);
lean_dec(v___x_6639_);
v___x_6708_ = lean_box(0);
v_isShared_6709_ = v_isSharedCheck_6713_;
goto v_resetjp_6707_;
}
v_resetjp_6707_:
{
lean_object* v___x_6711_; 
if (v_isShared_6709_ == 0)
{
v___x_6711_ = v___x_6708_;
goto v_reusejp_6710_;
}
else
{
lean_object* v_reuseFailAlloc_6712_; 
v_reuseFailAlloc_6712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_a_6706_);
v___x_6711_ = v_reuseFailAlloc_6712_;
goto v_reusejp_6710_;
}
v_reusejp_6710_:
{
return v___x_6711_;
}
}
}
}
}
}
else
{
lean_object* v_a_6716_; lean_object* v___x_6718_; uint8_t v_isShared_6719_; uint8_t v_isSharedCheck_6723_; 
v_a_6716_ = lean_ctor_get(v___x_6625_, 0);
v_isSharedCheck_6723_ = !lean_is_exclusive(v___x_6625_);
if (v_isSharedCheck_6723_ == 0)
{
v___x_6718_ = v___x_6625_;
v_isShared_6719_ = v_isSharedCheck_6723_;
goto v_resetjp_6717_;
}
else
{
lean_inc(v_a_6716_);
lean_dec(v___x_6625_);
v___x_6718_ = lean_box(0);
v_isShared_6719_ = v_isSharedCheck_6723_;
goto v_resetjp_6717_;
}
v_resetjp_6717_:
{
lean_object* v___x_6721_; 
if (v_isShared_6719_ == 0)
{
v___x_6721_ = v___x_6718_;
goto v_reusejp_6720_;
}
else
{
lean_object* v_reuseFailAlloc_6722_; 
v_reuseFailAlloc_6722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6722_, 0, v_a_6716_);
v___x_6721_ = v_reuseFailAlloc_6722_;
goto v_reusejp_6720_;
}
v_reusejp_6720_:
{
return v___x_6721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_6724_, lean_object* v_a_6725_, lean_object* v_a_6726_, lean_object* v_a_6727_, lean_object* v_a_6728_, lean_object* v_a_6729_, lean_object* v_a_6730_, lean_object* v_a_6731_, lean_object* v_a_6732_, lean_object* v_a_6733_, lean_object* v_a_6734_, lean_object* v_a_6735_, lean_object* v_a_6736_){
_start:
{
lean_object* v_res_6737_; 
v_res_6737_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6724_, v_a_6725_, v_a_6726_, v_a_6727_, v_a_6728_, v_a_6729_, v_a_6730_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_, v_a_6735_);
lean_dec(v_a_6735_);
lean_dec_ref(v_a_6734_);
lean_dec(v_a_6733_);
lean_dec_ref(v_a_6732_);
lean_dec(v_a_6731_);
lean_dec_ref(v_a_6730_);
lean_dec(v_a_6729_);
lean_dec_ref(v_a_6728_);
lean_dec(v_a_6727_);
lean_dec(v_a_6726_);
lean_dec_ref(v_a_6725_);
lean_dec(v_passes_6724_);
return v_res_6737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_6738_, lean_object* v_msg_6739_, lean_object* v___y_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_, lean_object* v___y_6744_, lean_object* v___y_6745_, lean_object* v___y_6746_, lean_object* v___y_6747_, lean_object* v___y_6748_, lean_object* v___y_6749_, lean_object* v___y_6750_){
_start:
{
lean_object* v___x_6752_; 
v___x_6752_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_6738_, v_msg_6739_, v___y_6747_, v___y_6748_, v___y_6749_, v___y_6750_);
return v___x_6752_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_6753_, lean_object* v_msg_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_, lean_object* v___y_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_, lean_object* v___y_6761_, lean_object* v___y_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_, lean_object* v___y_6765_, lean_object* v___y_6766_){
_start:
{
lean_object* v_res_6767_; 
v_res_6767_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_6753_, v_msg_6754_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_, v___y_6763_, v___y_6764_, v___y_6765_);
lean_dec(v___y_6765_);
lean_dec_ref(v___y_6764_);
lean_dec(v___y_6763_);
lean_dec_ref(v___y_6762_);
lean_dec(v___y_6761_);
lean_dec_ref(v___y_6760_);
lean_dec(v___y_6759_);
lean_dec_ref(v___y_6758_);
lean_dec(v___y_6757_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6755_);
return v_res_6767_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6768_, lean_object* v_x_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_, lean_object* v___y_6772_, lean_object* v___y_6773_, lean_object* v___y_6774_, lean_object* v___y_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_){
_start:
{
lean_object* v___x_6782_; 
v___x_6782_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6769_);
return v___x_6782_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6783_, lean_object* v_x_6784_, lean_object* v___y_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_, lean_object* v___y_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_, lean_object* v___y_6796_){
_start:
{
lean_object* v_res_6797_; 
v_res_6797_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6783_, v_x_6784_, v___y_6785_, v___y_6786_, v___y_6787_, v___y_6788_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_, v___y_6795_);
lean_dec(v___y_6795_);
lean_dec_ref(v___y_6794_);
lean_dec(v___y_6793_);
lean_dec_ref(v___y_6792_);
lean_dec(v___y_6791_);
lean_dec_ref(v___y_6790_);
lean_dec(v___y_6789_);
lean_dec_ref(v___y_6788_);
lean_dec(v___y_6787_);
lean_dec(v___y_6786_);
lean_dec_ref(v___y_6785_);
return v_res_6797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6798_, lean_object* v_as_x27_6799_, lean_object* v_b_6800_, lean_object* v_a_6801_, lean_object* v___y_6802_, lean_object* v___y_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_, lean_object* v___y_6809_, lean_object* v___y_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_){
_start:
{
lean_object* v___x_6814_; 
v___x_6814_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6799_, v_b_6800_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_);
return v___x_6814_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6815_, lean_object* v_as_x27_6816_, lean_object* v_b_6817_, lean_object* v_a_6818_, lean_object* v___y_6819_, lean_object* v___y_6820_, lean_object* v___y_6821_, lean_object* v___y_6822_, lean_object* v___y_6823_, lean_object* v___y_6824_, lean_object* v___y_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_){
_start:
{
lean_object* v_res_6831_; 
v_res_6831_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6815_, v_as_x27_6816_, v_b_6817_, v_a_6818_, v___y_6819_, v___y_6820_, v___y_6821_, v___y_6822_, v___y_6823_, v___y_6824_, v___y_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_);
lean_dec(v___y_6829_);
lean_dec_ref(v___y_6828_);
lean_dec(v___y_6827_);
lean_dec_ref(v___y_6826_);
lean_dec(v___y_6825_);
lean_dec_ref(v___y_6824_);
lean_dec(v___y_6823_);
lean_dec_ref(v___y_6822_);
lean_dec(v___y_6821_);
lean_dec(v___y_6820_);
lean_dec_ref(v___y_6819_);
lean_dec(v_as_x27_6816_);
lean_dec(v_as_6815_);
return v_res_6831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6832_, lean_object* v_data_6833_, lean_object* v_ref_6834_, lean_object* v_msg_6835_, lean_object* v___y_6836_, lean_object* v___y_6837_, lean_object* v___y_6838_, lean_object* v___y_6839_, lean_object* v___y_6840_, lean_object* v___y_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_){
_start:
{
lean_object* v___x_6848_; 
v___x_6848_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6832_, v_data_6833_, v_ref_6834_, v_msg_6835_, v___y_6843_, v___y_6844_, v___y_6845_, v___y_6846_);
return v___x_6848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6849_, lean_object* v_data_6850_, lean_object* v_ref_6851_, lean_object* v_msg_6852_, lean_object* v___y_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_){
_start:
{
lean_object* v_res_6865_; 
v_res_6865_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6849_, v_data_6850_, v_ref_6851_, v_msg_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_);
lean_dec(v___y_6863_);
lean_dec_ref(v___y_6862_);
lean_dec(v___y_6861_);
lean_dec_ref(v___y_6860_);
lean_dec(v___y_6859_);
lean_dec_ref(v___y_6858_);
lean_dec(v___y_6857_);
lean_dec_ref(v___y_6856_);
lean_dec(v___y_6855_);
lean_dec(v___y_6854_);
lean_dec_ref(v___y_6853_);
return v_res_6865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_){
_start:
{
lean_object* v___x_6879_; 
v___x_6879_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6866_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_, v_a_6872_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_, v_a_6877_);
if (lean_obj_tag(v___x_6879_) == 0)
{
lean_object* v_a_6880_; lean_object* v___x_6881_; lean_object* v___x_6883_; uint8_t v_isShared_6884_; uint8_t v_isSharedCheck_6888_; 
v_a_6880_ = lean_ctor_get(v___x_6879_, 0);
lean_inc(v_a_6880_);
lean_dec_ref_known(v___x_6879_, 1);
v___x_6881_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropPassCaches___redArg(v_a_6867_, v_a_6868_);
v_isSharedCheck_6888_ = !lean_is_exclusive(v___x_6881_);
if (v_isSharedCheck_6888_ == 0)
{
lean_object* v_unused_6889_; 
v_unused_6889_ = lean_ctor_get(v___x_6881_, 0);
lean_dec(v_unused_6889_);
v___x_6883_ = v___x_6881_;
v_isShared_6884_ = v_isSharedCheck_6888_;
goto v_resetjp_6882_;
}
else
{
lean_dec(v___x_6881_);
v___x_6883_ = lean_box(0);
v_isShared_6884_ = v_isSharedCheck_6888_;
goto v_resetjp_6882_;
}
v_resetjp_6882_:
{
lean_object* v___x_6886_; 
if (v_isShared_6884_ == 0)
{
lean_ctor_set(v___x_6883_, 0, v_a_6880_);
v___x_6886_ = v___x_6883_;
goto v_reusejp_6885_;
}
else
{
lean_object* v_reuseFailAlloc_6887_; 
v_reuseFailAlloc_6887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6887_, 0, v_a_6880_);
v___x_6886_ = v_reuseFailAlloc_6887_;
goto v_reusejp_6885_;
}
v_reusejp_6885_:
{
return v___x_6886_;
}
}
}
else
{
return v___x_6879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6890_, lean_object* v_a_6891_, lean_object* v_a_6892_, lean_object* v_a_6893_, lean_object* v_a_6894_, lean_object* v_a_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_){
_start:
{
lean_object* v_res_6903_; 
v_res_6903_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6890_, v_a_6891_, v_a_6892_, v_a_6893_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_, v_a_6901_);
lean_dec(v_a_6901_);
lean_dec_ref(v_a_6900_);
lean_dec(v_a_6899_);
lean_dec_ref(v_a_6898_);
lean_dec(v_a_6897_);
lean_dec_ref(v_a_6896_);
lean_dec(v_a_6895_);
lean_dec_ref(v_a_6894_);
lean_dec(v_a_6893_);
lean_dec(v_a_6892_);
lean_dec_ref(v_a_6891_);
lean_dec(v_passes_6890_);
return v_res_6903_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default = _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default);
l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp = _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
